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



/// Sparse merkle tree
#[derive(Default, Debug)]
pub struct SparseMerkleTree<H, V, S> {
    store: S,
    root: H256,
    phantom: PhantomData<(H, V)>,
    height: u8,
    leaves_cnt: BTreeMap<u8,usize>,
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
        let node = MergeValue::from_h256(value.to_h256());
        // notice when value is zero the leaf is deleted, so we do not need to store it
        if !node.is_zero() {
            self.store.insert_leaf(key, value)?;
        } else {
            self.store.remove_leaf(&key)?;
        }

        if self.root.is_zero() && !node.is_zero() { // empty root, build branch for root and update it
            let (left, right) = if key.is_right(0) {
                (MergeValue::zero(), node)
            } else {
                (node, MergeValue::zero())
            };
            // update root hash immediately
            self.height = 1;
            self.root = merge_trie::<H>(self.height, &H256::zero(), &left, &right).hash::<H>();

            let branch = BranchNode { left, right };
            self.store.insert_branch(BranchKey::new(0, self.root), branch)?; // insert the branch
            self.leaves_cnt.insert(0, 1);
        } else {
            let prev_height = self.height;

            if !node.is_zero() {
                self.insert_node(key, node, 0, MergeValue::trie_from_h256(self.height, self.root), &BranchKey::new(0, H256::zero()), prev_height, false)?
            } else { // delete
                self.delete_node(key, node, 0, MergeValue::trie_from_h256(self.height, self.root), &BranchKey::new(0, H256::zero()), prev_height)?
            };

            self.refresh_tree_hash()?;

        }

        Ok(&self.root)
    }

    /// Walk-through recurse insertion fn
    fn insert_node(&mut self, key: H256, node: MergeValue, distance: u8, current: MergeValue, parent_key: &BranchKey, prev_height: u8, in_replace: bool) -> Result<Option<H256>> {
        let height = prev_height - distance; // transform height
        let current_key = BranchKey::new(distance, current.key());

        if let Some(parent_branch) = self.store.get_branch(&current_key)? {
            let (left, right) = (parent_branch.left.clone(), parent_branch.right.clone());
            let (target, another) =
            if key.is_right(distance) {
                (right, left)
            } else {
                (left, right)
            };

            let (target, another) = if !target.is_zero() && !in_replace && key < target.key() && another.is_zero() {
                 (another, target)
            } else {
                (target, another)
            };


            if target.is_zero() { // insert inplace
                let new_branch = if target.key() == parent_branch.left.key() {
                    BranchNode {
                        left: node,
                        right: another,
                    }
                } else {
                    BranchNode {
                        left: another,
                        right: node,
                    }
                };
                let new_branch_key = BranchKey::new(distance, current.key());
                let new_hash = merge_trie::<H>(height, &parent_key.node_key, &new_branch.left, &new_branch.right);
                self.store.remove_branch(&current_key)?;
                self.store.insert_branch(new_branch_key, new_branch)?;

                // update current height count
                let current_cnt = self.get_leaves_count_by_distance(distance);

                self.leaves_cnt.insert(distance,current_cnt + 1);

                Ok(Some(new_hash.hash::<H>()))
            } else {
                if self.store.get_branch(&BranchKey::new(distance + 1, target.key()))?.is_none() { //  a leaf
                    if !in_replace {
                        if key > target.key() {
                            //replace target with new
                            self.store.remove_branch(&current_key)?;


                            let new_branch = if another.key() == parent_branch.left.key() {
                                BranchNode{
                                    left: another,
                                    right: node,
                                }
                            } else {
                                BranchNode{
                                    right: another,
                                    left: node,
                                }
                            };
                            self.store.insert_branch(current_key, new_branch)?;
                            self.insert_node(target.key(), target, distance, current, &parent_key, prev_height, false)
                        } else if another.key() < key { // enter another
                            self.insert_node(key, node, distance + 1, another, &BranchKey::new(distance + 1, current.key()), prev_height, true)
                        } else {
                            // directly create new merge
                            self.insert_node(key, node, distance + 1, target, &BranchKey::new(distance + 1, current.key()), prev_height, false)
                        }
                    } else {
                        // walk down the tree
                        self.insert_node(key, node, distance + 1, target, &BranchKey::new(distance + 1, current.key()), prev_height, true)
                    }
                } else {
                        // walk down, to create new merge
                        self.insert_node(key, node, distance + 1, target, &BranchKey::new(distance + 1, current.key()), prev_height, true)
                }

            }
        } else { // no branch before
            let (left, right) = if key.is_right(distance) {
                (current.clone(), node)
            } else {
                (node, current.clone())
            };

            if distance + 1> prev_height {
                self.height = distance + 1;
            }

            let current_cnt = self.get_leaves_count_by_distance(distance);
            if current_cnt > 0 {
                self.leaves_cnt.insert(distance, current_cnt - 1);
            }

            // update leaves count
            let current_cnt = self.get_leaves_count_by_distance(distance + 1);

            self.leaves_cnt.insert(distance + 1,current_cnt + 2);
            let new_merge = merge_trie::<H>(self.height - distance , &parent_key.node_key, &left, &right);

            // insert new branch
            let new_key = BranchKey::new(distance + 1, new_merge.key());
            self.store.insert_branch(new_key.clone(), BranchNode {
                left: left.clone(),
                right: right.clone(),
            })?;

            // update parent
            if let Some(parent) = self.store.get_branch(&parent_key)? {
                let new_branch = if parent.left.key() == current.key(){
                    BranchNode {
                        left: new_merge.clone(),
                        right: parent.right,
                    }
                }  else {
                    BranchNode {
                        left: parent.left,
                        right: new_merge.clone(),
                    }
                };
                self.store.remove_branch(parent_key)?;
                self.store.insert_branch(parent_key.clone(), new_branch)?;
            }
            Ok(Some(new_merge.hash::<H>()))
        }
    }

    /// Walk-through recurse insertion fn
    fn delete_node(&mut self, key: H256, node: MergeValue, distance: u8, current: MergeValue, parent_key: &BranchKey, prev_height: u8) -> Result<Option<H256>> {
        let height = prev_height - distance;
        let current_key = BranchKey::new(distance, current.key());
        let branch = self.store.get_branch(&current_key)?;
        if !branch.is_none() {
            let branch = branch.unwrap();
            let (left, right) = (branch.left, branch.right);
            if left.key() == key || right.key() == key {
                let remained = if left.key() == key {
                    right
                } else {
                    left
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
                        self.store.remove_branch(&current_key)?;
                        let current_cnt = self.get_leaves_count_by_distance(distance);
                        // decreasing
                        if current_cnt != 0 {
                            self.leaves_cnt.insert(distance,current_cnt - 1);
                        }

                        let (new_left, new_right) = if parent_branch.left.key() == current_key.node_key {
                            (remained, parent_branch.right)
                        } else {
                            (parent_branch.left, remained)
                        };

                        self.store.insert_branch(parent_key.clone(), BranchNode{left: new_left, right: new_right})?;
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
                        let new_hash = merge_trie::<H>(height, &parent_key.node_key, &new_branch.left, &new_branch.right);
                        self.store.insert_branch(BranchKey::new(distance, new_hash.key()), new_branch)?;
                        self.store.remove_branch(&BranchKey::new(0, self.root))?;
                        self.root = new_hash.hash::<H>();
                        return Ok(Some(self.root))
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
                return self.delete_node(key, node, distance + 1, target, &BranchKey::new(distance + 1, current.key()), prev_height);

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
    pub fn refresh_tree_hash(&mut self) -> Result<&H256> {
        if !self.root.is_zero() { // won't update empty tree
            let root_value = MergeValue::trie_from_h256(self.height,self.root);
            self.root = self.refresh_hash(root_value, H256::zero(), 0)?.hash::<H>();
        }
        Ok(&self.root)
    }

    fn refresh_hash(&mut self, current: MergeValue, parent_node: H256,distance: u8) -> Result<MergeValue> {
        if let Some(branch) = self.store.get_branch(&BranchKey::new(distance, current.key()))? {
            let left = self.refresh_hash(branch.left, current.key(), distance + 1)?;
            let right = self.refresh_hash(branch.right, current.key(), distance + 1)?;
            let height = match current {
              MergeValue::TrieValue(h,_) => h,
                _ => panic!("Invalid Type of MergeValue"),
            };
            let new_merge = merge_trie::<H>(height, &parent_node, &left, &right);
            self.store.remove_branch(&BranchKey::new(distance, current.key()))?;
            if !(left.is_zero() && right.is_zero()) {
                self.store.insert_branch(BranchKey::new(distance, new_merge.key()), BranchNode {
                    left, right
                })?;
            }
            Ok(new_merge)
        } else {
            match current {
                MergeValue::Value(_) => Ok(current),
                MergeValue::TrieValue(_,_)=> Ok(MergeValue::zero()), // if not found, means it was set to empty
                _ => Ok(MergeValue::zero()),
            }
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
            self.try_proof(current_key.clone(), MergeValue::from_h256(self.root), 0,&mut bitmap, &mut proof)?;
            leaves_bitmap.push(bitmap);
        }

        Ok(MerkleProof::new(leaves_bitmap, proof))
    }

    pub fn try_proof(&self, key: H256, current: MergeValue, distance: u8, bitmap: &mut H256, proof: &mut Vec<MergeValue>) -> Result<()> {
        let height = self.height - distance;

        if let Some(branch) = self.store.get_branch(&BranchKey::new(distance, current.key()))? {
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