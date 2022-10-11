use crate::{
    branch::{BranchKey, BranchNode},
    collections::VecDeque,
    error::{Error, Result},
    merge::{merge, MergeValue},
    merkle_proof::MerkleProof,
    traits::{Hasher, StoreReadOps, StoreWriteOps, Value},
    vec::Vec,
    H256, MAX_STACK_SIZE,
};

use core::marker::PhantomData;
use std::borrow::Borrow;
use std::cmp::max;


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
        let node = MergeValue::Value(value.to_h256());
        // notice when value is zero the leaf is deleted, so we do not need to store it
        if !node.is_zero() {
            self.store.insert_leaf(key, value)?;
        } else {
            self.store.remove_leaf(&key)?;
        }

        let new_height = calculate_smt_height(self.store.get_leaves_len() as u8);


        // the tree grows or decrements, root hash must be updated
        let height_changed: i8 = new_height as i8 - self.height as i8;


        if self.root.is_zero() { // empty tree now
            let branch = if key.is_right((0 + height_changed) as u8) {
                BranchNode {
                    left: MergeValue::zero(),
                    right: node,
                }
            } else {
                BranchNode {
                    left: node,
                    right: MergeValue::zero(),
                }
            };

            self.store.remove_branch(&BranchKey::new(self.height, self.root))?;
            self.root = merge::<H>(new_height as u8, &H256::zero(), &branch.left, &branch.right).hash::<H>();
            self.store.insert_branch(BranchKey::new(new_height, self.root), branch.clone())?;
            self.height = new_height;
        } else {
            // walk through the tree from top to bottom
            let mut parent_key = BranchKey::new(self.height, self.root);
            let mut walk_path = Vec::<BranchKey>::new(); // recording the walk path for out recursion update hashes.
            while !parent_key.node_key.is_zero() {
                if let Some(parent_branch) = self.store.get_branch(&parent_key)? {
                    walk_path.push(parent_key.clone());
                    let (left, right) = (parent_branch.left, parent_branch.right);
                    if node.is_zero(){ // deletion
                        if left.hash() == key {
                            self.store.insert_branch(parent_key.clone(), BranchNode{
                                left: MergeValue::zero(),
                                right,
                            })?;
                        } else if right.hash() == key {
                            self.store.insert_branch(parent_key.clone(), BranchNode{
                                left,
                                right: MergeValue::zero(),
                            })?;
                        } else { // find next
                            let mut target = match left {
                                MergeValue::TrieValue(k,v) => { Some(BranchKey::new(parent_key.height - 1, k))},
                                _ => { None },
                            };
                            if target.is_none() { // try right
                                target = match right {
                                    MergeValue::TrieValue(k,v) => { Some(BranchKey::new(parent_key.height - 1, k))},
                                    _ => { None },
                                };
                            }

                            parent_key = target.unwrap();
                        }
                    } else { // insertion

                    }
                } else { // no branch recorded in this node's subtree, maybe a leaf? => create new merge node with  [MergeHash, [THIS_LEAF, INSERTED_LEAF]]

                }
            }

        }

        self.height = new_height;

        Ok(&self.root)
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
