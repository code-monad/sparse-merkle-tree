use crate::{
    branch::*,
    collections::VecDeque,
    error::{Error, Result},
    merge::{merge, merge_trie, MergeValue},
    merkle_proof::MerkleProof,
    traits::{Hasher, StoreReadOps, StoreWriteOps, Value},
    vec::Vec,
    H256, MAX_STACK_SIZE,
};
use core::cmp::Ordering;
use core::marker::PhantomData;
use std::borrow::Borrow;

/// Sparse merkle tree
#[derive(Default, Debug)]
pub struct SparseMerkleTree<H, V, S> {
    store: S,
    root: H256,
    phantom: PhantomData<(H, V)>,
    height: u8,
    highest: Option<H256>,
    past_roots: Vec<H256>,
}

impl<H, V, S: StoreReadOps<V>> SparseMerkleTree<H, V, S> {
    /// Build a merkle tree from root and store
    pub fn new(root: H256, store: S) -> SparseMerkleTree<H, V, S> {
        SparseMerkleTree {
            root,
            store,
            phantom: PhantomData,
            height: 0,
            highest: None,
            past_roots: Vec::new(),
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

    /// Get Past Roots
    pub fn past_roots(&self) -> &Vec<H256> {
        &self.past_roots
    }
}

/// A tree in N level can contain max of (2^N + 1) leaves
/// So the inverse calculation for tree have M leaves, the level is: ⌊log2(M-1)⌋
pub fn calculate_smt_height(leaves_count: u8) -> u8 {
    if leaves_count >= 1 {
        ((leaves_count - 1) as f64).log2().ceil() as u8 + 1
    } else {
        0
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
                (MergeValue::zero(), node)
            } else {
                (node, MergeValue::zero())
            };
            // update root hash immediately
            self.height = 1;
            self.root = merge::<H>(self.height, &H256::zero(), &left, &right).hash::<H>();
            let branch = BranchNode { left, right };
            self.store.insert_branch(BranchKey::new(self.height, self.root), branch)?; // insert the branch
        } else {

            let new_root = if !node.is_zero() { // insert
                self.insert_node(key, node, self.height, MergeValue::trie_from_h256(self.root, self.root), &BranchKey::new(0, H256::zero()))?
            } else { // delete
                self.delete_node(key, node, self.height, MergeValue::trie_from_h256(self.root, self.root), &BranchKey::new(0, H256::zero()))?
            };


            self.root = new_root;


            self.height = calculate_smt_height(self.store.get_leaves_len() as u8);
        }

        Ok(&self.root)
    }

    /// Walk-through recurse insertion fn
    fn insert_node(&mut self, key: H256, node: MergeValue, height: u8, current: MergeValue, parent_key: &BranchKey) -> Result<H256> {
        let current_key = BranchKey::new(height, current.key());
        if let Some(parent_branch) = self.store.get_branch(&current_key)? {
            let (left, right) = (parent_branch.left, parent_branch.right);
            let (target, another) = if key.is_right(height) {
                (left, right)
            } else {
                (right, left)
            };

            if target.is_zero() { // insert inplace
                let new_branch = if key.is_right(height) {
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
                self.store.insert_branch(new_branch_key, new_branch)?;

                // update parent_branch because this current has updated
                if let Some(parent_branch) = self.store.get_branch(parent_key)? { // when current is root, parent_key is ZERO so this won't match
                    let (parent_left, parent_right) = if parent_branch.left.key() == parent_key.node_key {
                        (new_merge_value, parent_branch.right)
                    } else {
                        (parent_branch.left, new_merge_value)
                    };

                    self.store.insert_branch(parent_key.clone(), BranchNode{
                        left: parent_left,
                        right:parent_right
                    })?;
                }
                Ok(new_hash.hash::<H>())

            } else {
                // walk down the tree
                self.insert_node(key, node, height - 1, target, &BranchKey::new(height - 1, current.key()))
            }

        } else { // no branch before, add a new merge node, [MERGE_VALUE, (current, new)]
            let (left, right) = if key.is_right(height) {
                (current, node)
            } else {
                (node, current)
            };
            let new_merge = merge::<H>(height, &parent_key.node_key, &left, &right);


            // insert new branch
            let new_key = BranchKey::new(height, new_merge.hash::<H>());
            self.store.insert_branch(new_key.clone(), BranchNode {
                left: left.clone(),
                right: right.clone(),
            })?;
            Ok(new_merge.hash::<H>())
        }
    }

    /// Walk-through recurse insertion fn
    fn delete_node(&mut self, key: H256, node: MergeValue, height: u8, current: MergeValue, parent_key: &BranchKey) -> Result<H256> {
        let current_key = BranchKey::new(height, current.key());
        if let Some(branch) = self.store.get_branch(&current_key)? {
            let (left, right) = (branch.left, branch.right);
            if left.key() == key || right.key() == key {
                let new_branch = if left.key() == key {
                    BranchNode {
                        left: MergeValue::zero(),
                        right,
                    }
                } else {
                    BranchNode {
                        left,
                        right: MergeValue::zero(),
                    }
                };
                // delete empty branch
                if new_branch.is_empty(){
                    self.store.remove_branch(&current_key)?;
                } else { // move neighbor up
                    self.store.remove_branch(&current_key)?;
                    if let Some(parent_branch) = self.store.get_branch(&parent_key)? {
                        let remained = if new_branch.left.is_zero() {
                            &new_branch.right
                        } else {
                            &new_branch.left
                        };
                        let (new_left, new_right) = if parent_branch.left.key() == remained.key() {
                            (remained, &new_branch.right)
                        } else {
                            (&parent_branch.left, remained)
                        };
                        let new_parent_branch = BranchNode{
                            left: new_left.clone(),
                            right: new_right.clone()
                        };
                        let new_hash = merge::<H>(height, &parent_key.node_key, &new_left, &new_right).hash::<H>();
                        self.store.insert_branch(parent_key.clone(), new_parent_branch)?;
                        return Ok(new_hash)
                    } else { // this is root, remain the dangling sibling
                        let new_hash = merge::<H>(height, &parent_key.node_key, &new_branch.left, &new_branch.right).hash::<H>();
                        self.store.insert_branch(parent_key.clone(), new_branch)?;
                        return Ok(new_hash)
                    }
                }
            } else {
                let target = if key.is_right(height) {
                    right
                } else {
                    left
                };

                // walk down the tree
               return self.delete_node(key, node, height - 1, target, &BranchKey::new(height - 1, current.key()))
            }
        }
        Ok(H256::zero())

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
        for current_key in &keys {
            let mut bitmap = H256::zero();
            for height in 0..=core::u8::MAX {
                let parent_key = current_key.parent_path(height);
                let parent_branch_key = BranchKey::new(height, parent_key);
                if let Some(parent_branch) = self.store.get_branch(&parent_branch_key)? {
                    let sibling = if current_key.is_right(height) {
                        parent_branch.left
                    } else {
                        parent_branch.right
                    };
                    if !sibling.is_zero() {
                        bitmap.set_bit(height);
                    }
                } else {
                    // The key is not in the tree (support non-inclusion proof)
                }
            }
            leaves_bitmap.push(bitmap);
        }

        let mut proof: Vec<MergeValue> = Default::default();
        let mut stack_fork_height = [0u8; MAX_STACK_SIZE]; // store fork height
        let mut stack_top = 0;
        let mut leaf_index = 0;
        while leaf_index < keys.len() {
            let leaf_key = keys[leaf_index];
            let fork_height = if leaf_index + 1 < keys.len() {
                leaf_key.fork_height(&keys[leaf_index + 1])
            } else {
                core::u8::MAX
            };
            for height in 0..=fork_height {
                if height == fork_height && leaf_index + 1 < keys.len() {
                    // If it's not final round, we don't need to merge to root (height=255)
                    break;
                }
                let parent_key = leaf_key.parent_path(height);
                let is_right = leaf_key.is_right(height);

                // has non-zero sibling
                if stack_top > 0 && stack_fork_height[stack_top - 1] == height {
                    stack_top -= 1;
                } else if leaves_bitmap[leaf_index].get_bit(height) {
                    let parent_branch_key = BranchKey::new(height, parent_key);
                    if let Some(parent_branch) = self.store.get_branch(&parent_branch_key)? {
                        let sibling = if is_right {
                            parent_branch.left
                        } else {
                            parent_branch.right
                        };
                        if !sibling.is_zero() {
                            proof.push(sibling);
                        } else {
                            unreachable!();
                        }
                    } else {
                        // The key is not in the tree (support non-inclusion proof)
                    }
                }
            }
            debug_assert!(stack_top < MAX_STACK_SIZE);
            stack_fork_height[stack_top] = fork_height;
            stack_top += 1;
            leaf_index += 1;
        }
        assert_eq!(stack_top, 1);
        Ok(MerkleProof::new(leaves_bitmap, proof))
    }
}
