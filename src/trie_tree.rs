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

/// Sparse merkle tree
#[derive(Default, Debug)]
pub struct SparseMerkleTree<H, V, S> {
    store: S,
    root: H256,
    phantom: PhantomData<(H, V)>,
    height: u8,
    past_roots: Vec<H256>,
}

impl<H, V, S> SparseMerkleTree<H, V, S> {
    /// Build a merkle tree from root and store
    pub fn new(root: H256, store: S) -> SparseMerkleTree<H, V, S> {
        SparseMerkleTree {
            root,
            store,
            phantom: PhantomData,
            height: 0,
            past_roots: Vec::<H256>::new(),
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

impl<H: Hasher + Default, V: Value + PartialEq, S: StoreReadOps<V> + StoreWriteOps<V>>
    SparseMerkleTree<H, V, S>
{
    /// Update a leaf, return new merkle root
    /// set to zero value to delete a key
    pub fn update(&mut self, key: H256, value: V) -> Result<&H256> {
        self.update_all([(key, value)].into())
    }
    /// Update multiple leaves at once
    pub fn update_all(&mut self, mut leaves: Vec<(H256, V)>) -> Result<&H256> {
        // Dedup(only keep the last of each key) and sort leaves
        leaves.reverse();
        leaves.sort_by_key(|(a, _)| *a);
        leaves.dedup_by_key(|(a, _)| *a);

        // Remove leaf if set to zero
        let mut nodes = leaves
            .into_iter()
            .map(|(k, v)| {
                let value = MergeValue::trie_from_h256(v.to_h256());
                if !value.is_zero() {
                    self.store.insert_leaf(k, v)
                } else {
                    self.store.remove_leaf(&k)
                }
                .map(|_| (k, value))
            })
            .collect::<Result<VecDeque<(H256, MergeValue)>>>()?;

        // build first branch if this is new tree
        while let Some((current_key, current_merge_value)) = nodes.pop_front() {
            let mut updated = false; // flag for if root is updated
            let root_branch_key = BranchKey::new(self.height, self.root);
            let mut current_node = self.root;
            if let Some(root_branch) = self.store.get_branch(&root_branch_key)? {
                let (mut left, mut right) = (root_branch.left, root_branch.right);
                let mut height = self.height;
                'walk: while !left.is_zero() {
                    // walk to the branch
                    if height == 0 {
                        // walked to bottom, but
                    }

                    // this is a deletion
                    if current_merge_value.is_zero() && left == current_merge_value {
                        self.store
                            .remove_branch(&BranchKey::new(height, current_key))?;
                        break 'walk;
                    }

                    match left {
                        MergeValue::Value(value) => {
                            // try right
                            current_node = right.hash::<H>();
                            if let Some(next_branch) = self
                                .store
                                .get_branch(&BranchKey::new(height, current_node))?
                            {
                                left = next_branch.left;
                                right = next_branch.right;
                                height -= 1;
                            } else { // no branch for right ?
                            }
                        }
                        MergeValue::TrieValue(value) => { // left is an trie hash, try left first
                        }
                        _ => {}
                    }
                }
                if left.is_zero() {
                    self.store.insert_branch(
                        BranchKey::new(height, current_key),
                        BranchNode {
                            left: MergeValue::from_h256(current_key),
                            right: right,
                        },
                    )?;
                }
            } else {
                // empty branch, which means empty tree contains only root
                if current_merge_value.is_zero() {
                    continue; // we shouldn't remove from an empty tree
                }
                let lhs = current_merge_value;
                let rhs = MergeValue::zero();

                // we need to update roots everytime when tree is modified
                self.root = merge::<H>(self.height, &self.root, &lhs, &rhs).hash::<H>();
                self.store.remove_branch(&root_branch_key)?;
                self.store.insert_branch(
                    BranchKey::new(self.height + 1, self.root),
                    BranchNode {
                        left: lhs,
                        right: rhs,
                    },
                );
                updated = true;
            }

            if updated {
                if let Some(last_root) = self.past_roots.last() {
                    self.store
                        .remove_branch(&BranchKey::new(self.height, *last_root))?;
                }
                self.past_roots.push(self.root);
            }
        }

        return Ok(&self.root);
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
