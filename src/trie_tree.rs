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
        let value_hash = value.to_h256();
        let node = MergeValue::TrieValue(key, value_hash);
        // notice when value is zero the leaf is deleted, so we do not need to store it
        if !node.is_zero() {
            self.store.insert_leaf(key, value)?;
        } else {
            self.store.remove_leaf(&key)?;
        }

        let new_height = calculate_smt_height(self.store.get_leaves_len() as u8);


        // the tree grows or decrements, root hash must be updated
        let height_changed: i8 = new_height as i8 - self.height as i8;

        // check if a empty root
        if self.root.is_zero() {
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
            let mut walk_path = Vec::<(BranchKey, BranchNode)>::new(); // recording the walk path for out recursion update hashes.


            while !parent_key.node_key.is_zero() {
                if let Some(parent_branch) = self.store.get_branch(&parent_key)? {
                    let new_parent_height = (parent_key.height as i8 + height_changed) as u8;
                    walk_path.push((parent_key.clone(), parent_branch.clone()));
                    let parent_height = (parent_key.height as i8 + height_changed) as u8;
                    let (left, right) = (parent_branch.left, parent_branch.right);
                    if parent_key.height > 0 {
                        let mut next_step = if key.is_right(parent_height) {
                            right.clone()
                        } else {
                            left.clone()
                        };

                        if parent_key.height == self.height && !next_step.is_zero() {
                            next_step = if key.is_right(parent_height) {
                                right.clone()
                            }  else {
                                left.clone()
                            };
                        }

                        if next_step.is_zero() { // valid position, build branch to connect here
                            let new_branch = if key.is_right(parent_height) {
                                BranchNode {
                                    left,
                                    right: node.clone(),
                                }
                            } else {
                                BranchNode {
                                    left: node.clone(),
                                    right,
                                }
                            };
                            self.store.insert_branch(parent_key, new_branch)?;
                            break;
                        } else {
                            if let MergeValue::TrieValue(k,v) = next_step {
                                if k == key {
                                    let new_branch = if key.is_right(parent_height) {
                                        BranchNode {
                                            left,
                                            right: node.clone(),
                                        }
                                    } else {
                                        BranchNode {
                                            left: node.clone(),
                                            right,
                                        }
                                    };
                                    let insert_height = if parent_height == 0 {
                                        0
                                    } else {
                                        parent_height - 1
                                    };
                                    self.store.insert_branch(BranchKey::new(insert_height, k), new_branch.clone())?;

                                    walk_path.push((parent_key.clone(), new_branch));
                                } else {
                                    if key.is_right(parent_key.height) {
                                        parent_key = BranchKey::new(parent_key.height - 1, right.hash::<H>());
                                    } else {
                                        parent_key = BranchKey::new(parent_key.height - 1, left.hash::<H>());
                                    }
                                }
                            } else {

                            }
                        }
                    } else { // reached bottom subtree
                        break;
                    }
                } else { // no branch recorded before, maybe is a value leaf

                    let branch = if key.is_right((parent_key.height as i8 + height_changed) as u8) {
                        BranchNode {
                            left: MergeValue::trie_from_h256(key, value_hash),
                            right: node,
                        }
                    } else {
                        BranchNode {
                            left: node,
                            right: MergeValue::trie_from_h256(key, value_hash),
                        }
                    };
                    self.store.insert_branch(parent_key.clone(), branch.clone())?; // update this node inplace
                    walk_path.push((parent_key, branch));
                    break;
                }
            }

            // update the tree's hash
            while let Some((key, branch)) = walk_path.pop() {
                if let Some((parent_key, parent_branch)) = walk_path.pop() { // stil have stacked path
                    if !branch.left.is_zero() && !branch.right.is_zero() {
                        let new_node_height = max(0, (key.height as i8 + height_changed) as u8);
                        let new_hash = merge::<H>(new_node_height, &parent_key.node_key, &branch.left, &branch.right);
                        self.store.remove_branch(&key)?;
                        self.store.insert_branch(BranchKey::new(new_node_height, new_hash.hash::<H>()), branch)?;
                        if parent_key.node_key == self.root { // this is root, update it
                            self.root = new_hash.hash::<H>();
                            self.past_roots.push(self.root);
                        }
                    } else if branch.is_empty() { // this node is empty now, set parent as an empty node
                        self.store.remove_branch(&parent_key)?;
                        walk_path.push((parent_key, BranchNode::new_empty()));
                    } else { // there is a value remained, move it up
                        let value_remain = if branch.left.is_zero() {
                            branch.right
                        } else {
                            branch.left
                        };

                        let (parent_left, parent_right) = (parent_branch.left, parent_branch.right);

                        // insert to it's parent nodes' sibling
                        let parent_branch = if parent_left.is_zero() {
                            BranchNode {
                                left: value_remain,
                                right: parent_right,
                            }
                        } else {
                            BranchNode {
                                left: parent_left,
                                right: value_remain,
                            }
                        };

                        // calculate new parent hash cuz it moved up
                        let parent_hash = merge::<H>(parent_key.height, &parent_key.node_key, &parent_branch.left, &parent_branch.right).hash::<H>();

                        self.store.remove_branch(&parent_key)?; // remove old branch

                        self.store.insert_branch(BranchKey::new(parent_key.height, parent_hash), parent_branch)?;
                    }
                } else { // this is root now, no need to update recursively

                    //update root hash
                    self.store.remove_branch(&key)?; // remove old root's branch

                    self.root = merge::<H>(new_height, &H256::zero(), &branch.left, &branch.right).hash::<H>();
                    self.store.insert_branch(BranchKey::new(new_height, self.root), branch)?;

                    if let Some(last_root) = self.past_roots.last() {
                        if last_root != &self.root {
                            self.past_roots.push(self.root); // recording new root
                        }
                    } else {
                        self.past_roots.push(self.root);
                    }
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
