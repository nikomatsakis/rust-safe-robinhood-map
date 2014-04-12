/*!
 * # Hash-Initialized Table (HIT)
 *
 * This module encapsulates the unsafely implemented part of the
 * robin hood hashtable. They key idea is that we have three arrays:
 * hashes, keys, and values. The keys and values arrays are only
 * initialized if hashes are non-zero. The external interface offered
 * by this module maintains that invariant at all times.
 *
 * The key idea is that you start out with a `Table`. You can `peek` at
 * this table to examine the state of a particular bucket. In so doing,
 * you *surrender* your reference to the table and get back a `BucketState`.
 * This `BucketState` can be either an `EmptyBucket` (indicating a spot in
 * the table that has no key/value) or a `FullBucket` (indicating a spot in
 * the table that has been initialized).
 *
 * The key point is that the `BucketState` *encapsulates* the table
 * reference you provided initially. This prevents you from modifying
 * the table, which ensures that the bucket state remains accurate.
 * Any further operations you would like to do, such as modifying the
 * state of the bucket, are done on the `BucketState` itself.
 *
 * Finally, you can surrender a `BucketState` and get back the raw
 * table reference.
 */

use std::intrinsics::{transmute, move_val_init};
use std::ptr;

pub struct Table<K,V> {
    capacity: uint,
    size: uint,
    hashes: ~[u64],
    keys: *mut K,
    values: *mut V,
}

pub enum BucketState<M> {
    EmptyBucket(EmptyBucket<M>),
    FullBucket(FullBucket<M>),
}

pub struct EmptyBucket<M> {
    table: M,
    index: uint,
}

pub struct FullBucket<M> {
    table: M,
    index: uint,
    hash: SafeHash,
}

///////////////////////////////////////////////////////////////////////////
// TableRef

/**
 * This trait encapsulates over `&Table` and `&mut Table` references.
 * It is essentially a workaround for the fact that we cannot write
 * code that is generic over mutability.
 */
pub trait TableRef<K,V> {
    fn size(&self) -> uint {
        self.borrow().size
    }

    fn capacity(&self) -> uint {
        self.borrow().capacity
    }

    fn hash(&self, index: uint) -> u64 {
        self.borrow().hashes[index]
    }

    fn borrow<'a>(&'a self) -> &'a Table<K,V>;
}

impl<'table,K,V> TableRef<K,V> for &'table Table<K,V> {
    fn borrow<'a>(&'a self) -> &'a Table<K,V> {
        &**self
    }
}

impl<'table,K,V> TableRef<K,V> for &'table mut Table<K,V> {
    fn borrow<'a>(&'a self) -> &'a Table<K,V> {
        &**self
    }
}

//////////////////////////////////////////////////////////////////////////

/// A hash that is not zero, since we use that to represent empty buckets.
#[deriving(Eq)]
pub struct SafeHash {
    hash: u64,
}

static EMPTY_BUCKET: u64 = 0u64;

impl SafeHash {
    pub fn new(unsafe_hash: u64) -> SafeHash {
        if unsafe_hash == EMPTY_BUCKET {
            SafeHash { hash: unsafe_hash | 0x8000_0000_0000_0000_u64 }
        } else {
            SafeHash { hash: unsafe_hash }
        }
    }

    /// Peek at the hash value, which is guaranteed to be non-zero.
    pub fn to_u64(&self) -> u64 { self.hash }
}

//////////////////////////////////////////////////////////////////////////

pub type EmptyBucketImm<'table,K,V> = EmptyBucket<&'table Table<K,V>>;
pub type FullBucketImm<'table,K,V> = FullBucket<&'table Table<K,V>>;
pub type EmptyBucketMut<'table,K,V> = EmptyBucket<&'table mut Table<K,V>>;
pub type FullBucketMut<'table,K,V> = FullBucket<&'table mut Table<K,V>>;

impl<K,V,M:TableRef<K,V>> EmptyBucket<M> {
    pub fn to_table(self) -> M {
        self.table
    }

    pub fn table<'a>(&'a self) -> &'a M {
        &self.table
    }
}

impl<K,V,M:TableRef<K,V>> FullBucket<M> {
    pub fn index(&self) -> uint {
        self.index
    }

    pub fn hash(&self) -> SafeHash {
        self.hash
    }

    pub fn freeze<'a>(&'a self) -> FullBucketImm<'a,K,V> {
        FullBucket {
            table: self.table.borrow(),
            index: self.index,
            hash: self.hash
        }
    }

    pub fn to_table(self) -> M {
        self.table
    }

    pub fn table<'a>(&'a self) -> &'a M {
        &self.table
    }
}

///////////////////////////////////////////////////////////////////////////
// Operations on the table

pub trait HitOps {
    /** Examine a given index and yield its current state. */
    fn peek(self, index: uint) -> BucketState<Self>;
}

pub fn peek<K,V,M:TableRef<K,V>>(table: M, index: uint) -> BucketState<M> {
    // FIXME -- I think this fn is needed due to overagressive autoref
    // coupled with overagressive borrowck rules that don't permit loans
    // to be forgotten when reborrowed pointer is mutated
    table.peek(index)
}

impl<K,V,M:TableRef<K,V>> HitOps for M {
    fn peek(self, index: uint) -> BucketState<M> {
        assert!(index < self.capacity());
        let hash = self.hash(index);
        if hash == EMPTY_BUCKET {
            EmptyBucket(EmptyBucket { table: self, index: index })
        } else {
            FullBucket(FullBucket { table: self, index: index,
                                    hash: SafeHash { hash: hash } })
        }
    }
}

///////////////////////////////////////////////////////////////////////////
// Operations on buckets

impl<'table,K,V> EmptyBucket<&'table mut Table<K,V>> {
    pub fn put(self, hash: SafeHash, key: K, value: V)
               -> FullBucketMut<'table,K,V>
    {
        let index = self.index as int; // FIXME
        unsafe {
            assert_eq!(self.table.hashes[self.index], 0);
            self.table.hashes[self.index] = hash.to_u64();
            move_val_init(&mut *self.table.keys.offset(index), key);
            move_val_init(&mut *self.table.values.offset(index), value);
        }
        self.table.size += 1;
        FullBucket { index: self.index, hash: hash, table: self.table }
    }
}

impl<'table,K,V> FullBucket<&'table mut Table<K,V>> {
    pub fn read_mut<'a>(&'a mut self)
                        -> (&'a mut SafeHash, &'a mut K, &'a mut V)
    {
        // Abuse the fact that a pointer to any u64 in the
        // hashtable at a full index is a safe hash. Thanks to `SafeHash`
        // just being a wrapper around u64, this is true, and the exposed
        // API is also safe: you can only update the entry to another SafeHash,
        // and thus the self remains full.
        let index = self.index as int; // FIXME
        unsafe {
            (transmute::<&'a mut u64, &'a mut SafeHash>(
                &mut self.table.hashes[self.index]),
             &mut *self.table.keys.offset(index),
             &mut *self.table.values.offset(index))
        }
    }

    pub fn take(self) -> (EmptyBucketMut<'table,K,V>, K, V) {
        unsafe {
            let index = self.index as int;
            self.table.hashes[self.index] = EMPTY_BUCKET;
            let keys: *K = &*self.table.keys;
            let key = ptr::read(keys.offset(index));
            let values: *V = &*self.table.values;
            let value = ptr::read(values.offset(index));
            self.table.size -= 1;
            (EmptyBucket { index: self.index, table: self.table }, key, value)
        }
    }
}

impl<K,V,M:TableRef<K,V>> FullBucket<M> {
    pub fn read<'a>(&'a self) -> (&'a K, &'a V) {
        unsafe {
            let index = self.index as int; // FIXME
            let table = self.table.borrow();
            (&*table.keys.offset(index),
             &*table.values.offset(index))
        }
    }
}
