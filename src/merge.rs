use crate::h256::H256;
use crate::traits::Hasher;

const MERGE_NORMAL: u8 = 1;
const MERGE_ZEROS: u8 = 2;

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum MergeValue {
    Value(H256),
    MergeWithZero {
        base_node: H256,
        zero_bits: H256,
        zero_count: u8,
    },
    TrieValue(H256, H256), // TrieValue(K, V)  = (node_key, node_value)
}

impl MergeValue {
    pub fn from_h256(v: H256) -> Self {
        MergeValue::Value(v)
    }

    pub fn trie_from_h256(k: H256, v: H256) -> Self {
        MergeValue::TrieValue(k,v)
    }

    pub fn zero() -> Self {
        MergeValue::Value(H256::zero())
    }

    pub fn is_zero(&self) -> bool {
        match self {
            MergeValue::Value(v) => {
                v.is_zero()
            },
            MergeValue::TrieValue(_,v) => {
                v.is_zero()
            },
            _ => false

        }
    }

    pub fn hash<H: Hasher + Default>(&self) -> H256 {
        match self {
            MergeValue::Value(v) => *v,
            MergeValue::MergeWithZero {
                base_node,
                zero_bits,
                zero_count,
            } => {
                let mut hasher = H::default();
                hasher.write_byte(MERGE_ZEROS);
                hasher.write_h256(base_node);
                hasher.write_h256(zero_bits);
                hasher.write_byte(*zero_count);
                hasher.finish()
            }
            MergeValue::TrieValue(_,v) => {
                if v.is_zero() {
                    H256::zero()
                } else {

                    let mut hasher = H::default();
                    //hasher.write_byte(MERGE_TRIE);
                    //hasher.write_h256(k);
                    hasher.write_h256(v);
                    hasher.finish()
                }
            }
        }
    }

    /// helper function for TrieValue to get key, simplify code
    pub fn key(&self) -> H256 {
        match self {
            MergeValue::TrieValue(k,_) => *k,
            MergeValue::Value(v) => *v,
            _ => H256::zero(),

        }
    }
}

/// Hash base node into a H256
pub fn hash_base_node<H: Hasher + Default>(
    base_height: u8,
    base_key: &H256,
    base_value: &H256,
) -> H256 {
    let mut hasher = H::default();
    hasher.write_byte(base_height);
    hasher.write_h256(base_key);
    hasher.write_h256(base_value);
    hasher.finish()
}

/// Merge two hash with node information
/// this function optimized for ZERO_HASH
/// if lhs and rhs both are ZERO_HASH return ZERO_HASH, otherwise hash all info.
pub fn merge<H: Hasher + Default>(
    height: u8,
    node_key: &H256,
    lhs: &MergeValue,
    rhs: &MergeValue,
) -> MergeValue {
    if lhs.is_zero() && rhs.is_zero() {
        return MergeValue::zero();
    }
    if lhs.is_zero() {
        return merge_with_zero::<H>(height, node_key, rhs, true);
    }
    if rhs.is_zero() {
        return merge_with_zero::<H>(height, node_key, lhs, false);
    }
    let mut hasher = H::default();
    hasher.write_byte(MERGE_NORMAL);
    hasher.write_byte(height);
    hasher.write_h256(node_key);
    hasher.write_h256(&lhs.hash::<H>());
    hasher.write_h256(&rhs.hash::<H>());
    MergeValue::Value(hasher.finish())
}

pub fn merge_trie<H: Hasher + Default> (height: u8,
                                          node_key: &H256,
                                          lhs: &MergeValue,
                                          rhs: &MergeValue,) -> MergeValue {

    let mut hasher = H::default();
    if lhs.is_zero() && rhs.is_zero() {
        return MergeValue::zero();
    }
    hasher.write_byte(MERGE_NORMAL);
    hasher.write_byte(height);
    hasher.write_h256(node_key);
    hasher.write_h256(&lhs.hash::<H>());
    hasher.write_h256(&rhs.hash::<H>());
    MergeValue::TrieValue(node_key.clone(), hasher.finish())
}

fn merge_with_zero<H: Hasher + Default>(
    height: u8,
    node_key: &H256,
    value: &MergeValue,
    set_bit: bool,
) -> MergeValue {
    match value {
        MergeValue::Value(v) => {
            let mut zero_bits = H256::zero();
            if set_bit {
                zero_bits.set_bit(height);
            }
            let base_node = hash_base_node::<H>(height, node_key, v);
            MergeValue::MergeWithZero {
                base_node,
                zero_bits,
                zero_count: 1,
            }
        }
        MergeValue::MergeWithZero {
            base_node,
            zero_bits,
            zero_count,
        } => {
            let mut zero_bits = *zero_bits;
            if set_bit {
                zero_bits.set_bit(height);
            }
            MergeValue::MergeWithZero {
                base_node: *base_node,
                zero_bits,
                zero_count: zero_count.wrapping_add(1),
            }
        }
        MergeValue::TrieValue(_,v) => {
            let mut zero_bits = H256::zero();
            if set_bit {
                zero_bits.set_bit(height);
            }
            let base_node = hash_base_node::<H>(height, node_key, v);
            MergeValue::MergeWithZero {
                base_node,
                zero_bits,
                zero_count: 1,
            }
        }
    }
}
