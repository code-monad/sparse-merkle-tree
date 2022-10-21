use crate::{
    branch::*,
    error::{Error, Result},
    merge::{merge, merge_trie, MergeValue},
    merkle_proof::MerkleProof,
    traits::{Hasher, StoreReadOps, StoreWriteOps, Value},
    vec::Vec,
    H256, MAX_STACK_SIZE,
    collections::BTreeMap,
};
use core::marker::PhantomData;


#[derive(Debug, PartialEq)]
pub enum HighestDirection{
    Left,
    Right,
}

/// Sparse merkle tree
#[derive(Default, Debug)]
pub struct SparseMerkleTree<H, V, S> {
    store: S,
    root: H256,
    phantom: PhantomData<(H, V)>,
    height: u8,
    leaves_cnt: BTreeMap<u8,usize>,
    highest: Option<HighestDirection>,
}

impl<H, V, S: StoreReadOps<V>> SparseMerkleTree<H, V, S> {
    /// Build a merkle tree from root and store
    pub fn new(root: H256, store: S) -> SparseMerkleTree<H, V, S> {
        SparseMerkleTree {
            root,
            store,
            phantom: PhantomData,
            height: 0,
            leaves_cnt: BTreeMap::<u8,usize>::new(),
            highest: None,
        }
    }


    /// Merkle root
    pub fn root(&self) -> &H256 {
        &self.root
    }

    /// Check empty of the tree
    pub fn is_empty(&self) -> bool {
        self.root.is_zero()
    }

    /// Destroy current tree and retake store
    pub fn take_store(self) -> S {
        self.store
    }

    /// Get backend store
    pub fn store(&self) -> &S {
        &self.store
    }

    /// Get mutable backend store
    pub fn store_mut(&mut self) -> &mut S {
        &mut self.store
    }

    pub fn height(&self) -> u8 {
        self.height
    }

}


impl<H: Hasher + Default, V: Value + PartialEq, S: StoreReadOps<V> + StoreWriteOps<V>>
SparseMerkleTree<H, V, S>
{
    /// Update a leaf, return new merkle root
    /// set to zero value to delete a key
    pub fn update(&mut self, key: H256, value: V) -> Result<&H256> {
        // compute and store new leaf
        let node = MergeValue::trie_from_h256(key, value.to_h256());
        // notice when value is zero the leaf is deleted, so we do not need to store it
        if !node.is_zero() {
            self.store.insert_leaf(key, value)?;
        } else {
            self.store.remove_leaf(&key)?;
        }

        if self.root.is_zero() && !node.is_zero() { // empty root, build branch for root and update it
            let (left, right) = if key.is_right(0) {
                self.highest = Some(HighestDirection::Right);
                (MergeValue::zero(), node)
            } else {
                self.highest = Some(HighestDirection::Left);
                (node, MergeValue::zero())
            };
            // update root hash immediately
            self.height = 1;
            self.root = merge_trie::<H>(self.height, &H256::zero(), &left, &right).hash::<H>();

            let branch = BranchNode { left, right };
            self.store.insert_branch(BranchKey::new(self.height, H256::zero()), branch)?; // insert the branch
            self.leaves_cnt.insert(0, 1);
        } else {
            let prev_height = self.height;
            let new_root = if !node.is_zero() { // insert
                self.insert_node(key, node, 0, MergeValue::trie_from_h256(H256::zero(), self.root), &BranchKey::new(0, H256::zero()), prev_height)?
            } else { // delete
                self.delete_node(key, node, 0, MergeValue::trie_from_h256(H256::zero(),self.root), &BranchKey::new(0, H256::zero()), prev_height)?
            };

            if let Some(new_root) = new_root {
                self.root = new_root;
            } // else the root is not updated

            if prev_height != self.height {
                self.refresh_tree_hash(prev_height)?;
            }
            //
        }

        Ok(&self.root)
    }

    /// Walk-through recurse insertion fn
    fn insert_node(&mut self, key: H256, node: MergeValue, distance: u8, current: MergeValue, parent_key: &BranchKey, prev_height: u8) -> Result<Option<H256>> {
        let mut height = prev_height - distance; // transform height
        let current_key = BranchKey::new(height, current.key());

        if let Some(parent_branch) = self.store.get_branch(&current_key)? {
            let (left, right) = (parent_branch.left, parent_branch.right);
            let (target, another) = if distance != 0 {
                if key.is_right(distance) {
                    (left, right)
                } else {
                    (right, left)
                }
            }  else { // we need to avoid inserting to highest sub-tree
                match self.highest {
                    Some(HighestDirection::Left) => (right, left),
                    _ => (left, right),
                }
            };

            if target.is_zero() { // insert inplace
                let new_branch = if key.is_right(distance) {
                    BranchNode {
                        left: another,
                        right: node,
                    }
                } else {
                    BranchNode {
                        left: node,
                        right: another,
                    }
                };
                let new_branch_key = BranchKey::new(height, current.key());
                let new_hash = merge::<H>(height, &parent_key.node_key, &new_branch.left, &new_branch.right);
                let new_merge_value = MergeValue::trie_from_h256(current.key(), new_hash.hash::<H>());
                self.store.remove_branch(&current_key)?;
                self.store.insert_branch(new_branch_key, new_branch)?;

                // update current height count
                let current_cnt = self.get_leaves_count_by_distance(distance);

                self.leaves_cnt.insert(distance,current_cnt + 1);

                // update parent_branch because this current has updated
                if let Some(parent_branch) = self.store.get_branch(parent_key)? { // when current is root, parent_key is ZERO so this won't match
                    let (parent_left, parent_right) = if parent_branch.left.key() == parent_key.node_key {
                        (new_merge_value, parent_branch.right)
                    } else {
                        (parent_branch.left, new_merge_value)
                    };

                    self.store.insert_branch(parent_key.clone(), BranchNode {
                        left: parent_left,
                        right: parent_right,
                    })?;
                }
                Ok(Some(new_hash.hash::<H>()))
            } else {
                // walk down the tree
                self.insert_node(key, node, distance + 1, target, &BranchKey::new(height - 1, current.key()), prev_height)
            }
        } else { // no branch before, add a new merge node, [MERGE_VALUE, (current, new)]
            let (left, right) = if key.is_right(distance) {
                (current, node)
            } else {
                (node, current)
            };

            if distance + 1 > prev_height {
                self.height = distance + 1;
            }

            // update leaves count
            let current_cnt = self.get_leaves_count_by_distance(distance + 1);

            self.leaves_cnt.insert(height + 1,current_cnt + 2);
            let new_merge = merge_trie::<H>(height + 1, &parent_key.node_key, &left, &right);

            // insert new branch
            let new_key = BranchKey::new(height + 1, new_merge.hash::<H>());
            self.store.insert_branch(new_key.clone(), BranchNode {
                left: left.clone(),
                right: right.clone(),
            })?;

            Ok(Some(new_merge.hash::<H>()))
        }
    }

    /// Walk-through recurse insertion fn
    fn delete_node(&mut self, key: H256, node: MergeValue, distance: u8, current: MergeValue, parent_key: &BranchKey, prev_height: u8) -> Result<Option<H256>> {
        let height = prev_height - distance;
        let current_key = BranchKey::new(height, current.key());
        let branch = self.store.get_branch(&current_key)?;
        if !branch.is_none() {
            let branch = branch.unwrap();
            let (left, right) = (branch.left, branch.right);
            if left.key() == key || right.key() == key {
                let remained = if left.key() == key {
                    &right
                } else {
                    &left
                };
                let current_cnt = self.get_leaves_count_by_distance(distance);

                // decreasing
                self.leaves_cnt.insert(distance,current_cnt - 1);

                // delete empty branch
                if remained.is_zero() {
                    self.store.remove_branch(&current_key)?;
                } else { // move neighbor up
                    self.store.remove_branch(&current_key)?;
                    if let Some(parent_branch) = self.store.get_branch(&parent_key)? {
                        let current_cnt = self.get_leaves_count_by_distance(distance);
                        // decreasing
                        if current_cnt != 0 {
                            self.leaves_cnt.insert(distance,current_cnt - 1);
                        }
                        // increasing parent
                        let parent_cnt = self.get_leaves_count_by_distance(distance - 1);
                        self.leaves_cnt.insert(distance-1, parent_cnt + 1);

                        let (new_left, new_right) = if current_key.node_key.is_right(distance - 1) {
                            (&parent_branch.left, remained)
                        } else {
                            (remained, &parent_branch.right)
                        };
                        let new_parent_branch = BranchNode {
                            left: new_left.clone(),
                            right: new_right.clone(),
                        };
                        let new_hash = merge_trie::<H>(height, &parent_key.node_key, &new_left, &new_right).hash::<H>();
                        self.store.insert_branch(parent_key.clone(), new_parent_branch)?;
                        return Ok(Some(new_hash))
                    } else { // this is root, remain the dangling sibling
                        let new_branch = if remained.key().is_right(distance) {
                            BranchNode{
                                left: MergeValue::zero(),
                                right: remained.clone(),
                            }
                        } else {
                            BranchNode{
                                left: remained.clone(),
                                right: MergeValue::zero(),
                            }
                        };
                        let new_hash = merge_trie::<H>(height, &parent_key.node_key, &new_branch.left, &new_branch.right).hash::<H>();
                        self.store.insert_branch(BranchKey::new(height, parent_key.node_key), new_branch)?;
                        return Ok(Some(new_hash))
                    }
                }

                let bottom_cnt = self.get_leaves_count_by_distance(prev_height);
                if bottom_cnt == 0 { // empty bottom
                    self.height = self.height - 1
                }

            } else {
                let target = if key.is_right(distance) {
                    right
                } else {
                    left
                };

                // walk down the tree
                return self.delete_node(key, node, distance + 1, target, &BranchKey::new(height - 1, current.key()), prev_height);
            }
        } else {
            return Ok(None);
        }

        Ok(Some(H256::zero()))
    }


    /// Update multiple leaves at once
    pub fn update_all(&mut self, mut leaves: Vec<(H256, V)>) -> Result<&H256> {
        // Dedup(only keep the last of each key) and sort leaves
        leaves.reverse();
        leaves.sort_by_key(|(a, _)| *a);
        leaves.dedup_by_key(|(a, _)| *a);

        for (key, value) in leaves {
            self.update(key, value)?;
        }

        Ok(&self.root)
    }

    /// Update the tree root hence of height change
    pub fn refresh_tree_hash(&mut self, prev_height: u8) -> Result<&H256> {
        if !self.root.is_zero() { // won't update empty tree
            let root_value = MergeValue::trie_from_h256(H256::zero(), self.root);
            self.root = self.refresh_hash(root_value, H256::zero(), 0, prev_height)?.hash::<H>();
        }
        Ok(&self.root)
    }

    fn refresh_hash(&mut self, current: MergeValue, parent_node: H256,distance: u8, prev_height: u8) -> Result<MergeValue> {
        if let Some(branch) = self.store.get_branch(&BranchKey::new(prev_height - distance, current.key()))? {
            let left = self.refresh_hash(branch.left, current.key(), distance + 1, prev_height)?;
            let right = self.refresh_hash(branch.right, current.key(), distance + 1, prev_height)?;
            let new_merge = merge_trie::<H>(self.height - distance, &parent_node, &left, &right);
            self.store.remove_branch(&BranchKey::new(prev_height - distance, current.key()))?;
            self.store.insert_branch(BranchKey::new(self.height - distance, new_merge.hash::<H>()), BranchNode {
                left, right
            })?;
            Ok(new_merge)
        } else {
            Ok(current)
        }
    }

    fn get_leaves_count_by_distance(&self, distance: u8) -> usize {
        if let Some(cnt) = self.leaves_cnt.get(&distance) {
            cnt.clone()
        } else {
            0
        }
    }
}

impl<H: Hasher + Default, V: Value, S: StoreReadOps<V>> SparseMerkleTree<H, V, S> {
    /// Get value of a leaf
    /// return zero value if leaf not exists
    pub fn get(&self, key: &H256) -> Result<V> {
        if self.is_empty() {
            return Ok(V::zero());
        }
        Ok(self.store.get_leaf(key)?.unwrap_or_else(V::zero))
    }

    /// Generate merkle proof
    pub fn merkle_proof(&self, mut keys: Vec<H256>) -> Result<MerkleProof> {
        if keys.is_empty() {
            return Err(Error::EmptyKeys);
        }

        // sort keys
        keys.sort_unstable();

        // Collect leaf bitmaps
        let mut leaves_bitmap: Vec<H256> = Default::default();
        let mut proof: Vec<MergeValue> = Default::default();
        for current_key in &keys {
            let mut bitmap = H256::zero();
            self.try_proof(current_key.clone(), MergeValue::trie_from_h256(H256::zero(), self.root), 0,&mut bitmap, &mut proof)?;
            leaves_bitmap.push(bitmap);
        }

        Ok(MerkleProof::new(leaves_bitmap, proof))
    }

    pub fn try_proof(&self, key: H256, current: MergeValue, distance: u8, bitmap: &mut H256, proof: &mut Vec<MergeValue>) -> Result<()> {
        let height = self.height - distance;

        if let Some(branch) = self.store.get_branch(&BranchKey::new(height, current.key()))? {
            let sibling = if key.is_right(self.height - distance) {
                branch.right
            } else {
                branch.left
            };

            if !sibling.is_zero() {
                bitmap.set_bit(height);
            }

            proof.push(current.clone());
            self.try_proof(key, sibling, distance+1, bitmap, proof)?
        } else { // reached leaf
            if current.key() == key {  // exists
                bitmap.set_bit(height);
            } else { // non exist

            }
        }
        Ok(())
    }
}