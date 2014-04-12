#![feature(globs)]

use hit::*;
use std::hash::Hash;
use std::iter::{range, range_inclusive};
use std::mem::replace;
use std::ptr::RawPtr;

mod hit;

//////////////////////////////////////////////////////////////////////////

fn swap_bucket<K,V>(full_bucket: &mut hit::FullBucketMut<K,V>,
                    hash: SafeHash,
                    key: K,
                    value: V)
                    -> (SafeHash, K, V)
{
    let (old_hash_ref, old_key_ref, old_val_ref) = full_bucket.read_mut();

    let old_hash = replace(old_hash_ref, hash);
    let old_key  = replace(old_key_ref,  key);
    let old_val  = replace(old_val_ref,  value);

    (old_hash, old_key, old_val)
}

// Probe the `idx`th bucket for a given hash, returning the index of the
// target bucket.
//
// This exploits the power-of-two size of the hashtable. As long as this
// is always true, we can use a bitmask of cap-1 to do modular arithmetic.
//
// Prefer to use this with increasing values of `idx` rather than repeatedly
// calling `probe_next`. This reduces data-dependencies between loops, which
// can help the optimizer, and certainly won't hurt it. `probe_next` is
// simply for convenience, and is no more efficient than `probe`.
fn probe<K,V,M:TableRef<K,V>>(table: &M, hash: SafeHash, idx: uint) -> uint {
    let hash_mask = table.capacity() - 1;

    // So I heard a rumor that unsigned overflow is safe in rust..
    ((hash.to_u64() as uint) + idx) & hash_mask
}

// Generate the next probe in a sequence. Prefer to use 'probe' by itself,
// but this can sometimes be useful.
fn probe_next<K,V,M:TableRef<K,V>>(full_bucket: FullBucket<M>) -> (M, uint) {
    let probe = full_bucket.index();
    let table = full_bucket.to_table();
    let hash_mask = table.capacity() - 1;
    (table, (probe + 1) & hash_mask)
}

/// Get the distance of the bucket at the given index that it lies
/// from its 'ideal' location.
///
/// In the cited blog posts above, this is called the "distance to
/// inital bucket", or DIB.
fn bucket_distance<K,V,M:TableRef<K,V>>(bucket: &FullBucket<M>) -> uint {
    // where the hash of the element that happens to reside at
    // `index_of_elem` tried to place itself first.
    let first_probe_index = probe(bucket.table(), bucket.hash(), 0);
    let raw_index = bucket.index();
    if first_probe_index <= raw_index {
        // probe just went forward
        raw_index - first_probe_index
    } else {
        // probe wrapped around the hashtable
        raw_index + (bucket.table().capacity() - first_probe_index)
    }
}

/// Search for a pre-hashed key.
fn search_hashed_generic<K,V,M:TableRef<K,V>>(
    mut table: M,
    hash: SafeHash,
    is_match: |&K| -> bool)
    -> Option<FullBucket<M>>
{
    for num_probes in range(0u, table.size()) {
        let probe = probe(&table, hash, num_probes);

        let full_bucket = match table.peek(probe) {
            EmptyBucket(_) => return None, // hit an empty bucket
            FullBucket(fb) => fb
        };

        // We can finish the search early if we hit any bucket
        // with a lower distance to initial bucket than we've probed.
        if bucket_distance(&full_bucket) < num_probes {
            return None;
        }

        // If the hash doesn't match, it can't be this one.
        if hash != full_bucket.hash() {
            table = full_bucket.to_table();
            continue;
        }

        // If the key doesn't match, it can't be this one.
        let matched = {
            let (k, _) = full_bucket.read();
            is_match(k)
        };
        if !matched {
            table = full_bucket.to_table();
            continue;
        }

        return Some(full_bucket);
    }

    return None
}

fn search_hashed<K:TotalEq,V,M:TableRef<K,V>>(
    table: M,
    hash: SafeHash,
    k: &K)
    -> Option<FullBucket<M>>
{
    search_hashed_generic(table, hash, |k_| *k == *k_)
}

fn swap<K:TotalEq,V>(mut table: &mut Table<K,V>,
                     hash: SafeHash,
                     k: K,
                     v: V)
                     -> Option<V>
{
    //FIXME let potential_new_size = table.size() + 1;
    //FIXME make_some_room(table, potential_new_size);

    for dib in range_inclusive(0u, table.size()) {
        let probe = probe(&table, hash, dib);

        let mut full_bucket = match table.peek(probe) {
            EmptyBucket(b) => {
                // Found a hole!
                b.put(hash, k, v);
                return None;
            },
            FullBucket(b) => b
        };

        if full_bucket.hash() == hash {
            let (_, bucket_k, bucket_v) = full_bucket.read_mut();
            if k == *bucket_k {
                // Found an existing value.
                return Some(replace(bucket_v, v));
            }
        }

        let probe_dib = bucket_distance(&full_bucket);

        if probe_dib < dib {
            // Found a luckier bucket. This implies that the key does not
            // already exist in the hashtable. Just do a robin hood
            // insertion, then.
            robin_hood(full_bucket, probe_dib, hash, k, v);
            return None;
        }

        table = full_bucket.to_table();
    }

    // We really shouldn't be here.
    fail!("Internal HashMap error: Out of space.");
}

/// Perform robin hood bucket stealing at the given 'index'. You must
/// also pass that probe's "distance to initial bucket" so we don't have
/// to recalculate it, as well as the total number of probes already done
/// so we have some sort of upper bound on the number of probes to do.
///
/// 'hash', 'k', and 'v' are the elements to robin hood into the hashtable.
fn robin_hood<K:TotalEq,V>(mut full_bucket: FullBucketMut<K,V>,
                           dib_param: uint,
                           hash: SafeHash,
                           k: K,
                           v: V)
{
    // Swap (hash, k, v) into `full_bucket`, but now we have to find
    // a new home for the old contents.
    let (old_hash, old_key, old_val) = swap_bucket(&mut full_bucket, hash, k, v);

    for dib in range(dib_param + 1, full_bucket.table().size()) {
        let (table, probe) = probe_next(full_bucket);
        match table.peek(probe) {
            EmptyBucket(b) => {
                // Finally. A hole!
                b.put(old_hash, old_key, old_val);
                return;
            }
            FullBucket(b) => {
                full_bucket = b;

                // Robin hood! Steal the spot.
                let probe_dib = bucket_distance(&full_bucket);
                if probe_dib < dib {
                    return robin_hood(full_bucket, probe_dib,
                                      old_hash, old_key, old_val);
                }

                // Otherwise, keep probing.
            }
        }
    }

    fail!("HashMap fatal error: 100% load factor?");
}


// We use this type for the load factor, to avoid floating point operations
// which might not be supported efficiently on some hardware.
//
// We use small u16s here to save space in the hashtable. They get upcasted
// to u64s when we actually use them.
type Fraction = (u16, u16); // (numerator, denominator)

pub struct HashMap<K, V> {
    // All hashes are keyed on these values, to prevent hash collision attacks.
    k0: u64,
    k1: u64,

    // When size == grow_at, we double the capacity.
    grow_at: uint,

    // The capacity must never drop below this.
    minimum_capacity: uint,

    table: Table<K, V>,

    // We keep this at the end since it's 4-bytes, unlike everything else
    // in this struct. Might as well save a word of padding!
    load_factor: Fraction,
}

/*
impl<K:Hash+Eq,V> Map<K,V> for HashMap<K,V> {
    fn find<'a>(&'a self, k: &K) -> Option<&'a V> {
        self.search(k).map(|idx| {
            let (_, v) = self.table.read(&idx);
            v
        })
    }

    fn contains_key(&self, k: &K) -> bool {
        self.search(k).is_some()
    }
}
*/

fn main() { }
