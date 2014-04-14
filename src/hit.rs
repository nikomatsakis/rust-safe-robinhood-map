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

extern crate libc;
use std::intrinsics::{size_of, transmute, move_val_init};
use std::ptr;
use std::rt::global_heap;
use std::iter::{range_step_inclusive};

pub struct Table<K,V> {
    capacity: uint,
    size: uint,
    hashes: *mut u64,
    keys: *mut K,
    values: *mut V,
}

pub enum BucketState<M> {
    EmptyBucket(EmptyBucket<M>),
    FullBucket(FullBucket<M>),
}

pub trait Bucket<M> {
    fn to_table(self) -> M;
    fn index(&self) -> uint;
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
        assert!(index < self.capacity());
        unsafe {
            *self.borrow().hashes.offset(index as int)
        }
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
    pub fn table<'a>(&'a self) -> &'a M {
        &self.table
    }
}

impl<K,V,M:TableRef<K,V>> FullBucket<M> {
    pub fn freeze<'a>(&'a self) -> FullBucketImm<'a,K,V> {
        FullBucket {
            table: self.table.borrow(),
            index: self.index,
            hash: self.hash
        }
    }

    pub fn table<'a>(&'a self) -> &'a M {
        &self.table
    }

    pub fn hash(&self) -> SafeHash {
        self.hash
    }
}

impl<M> Bucket<M> for EmptyBucket<M> {
    fn to_table(self) -> M {
        self.table
    }

    fn index(&self) -> uint {
        self.index
    }
}

impl<M> Bucket<M> for FullBucket<M> {
    fn to_table(self) -> M {
        self.table
    }

    fn index(&self) -> uint {
        self.index
    }
}

///////////////////////////////////////////////////////////////////////////
// Operations on the table

impl<K,V> Table<K,V> {
    /// Does not initialize the buckets. The caller should ensure they,
    /// at the very least, set every hash to EMPTY_BUCKET.
    unsafe fn new_uninitialized(capacity: uint) -> Table<K, V> {
        let hashes_size =
            capacity.checked_mul(&size_of::<u64>()).expect("capacity overflow");
        let keys_size   =
            capacity.checked_mul(&size_of::< K >()).expect("capacity overflow");
        let vals_size   =
            capacity.checked_mul(&size_of::< V >()).expect("capacity overflow");

        /*
        The following code was my first pass at making RawTable only
        allocate a single buffer, since that's all it needs. There's
        no logical reason for this to require three calls to malloc.

        However, I'm not convinced the code below is correct. If you
        want to take a stab at it, please do! The alignment is
        especially tricky to get right, especially if you need more
        alignment than malloc guarantees.

        let hashes_offset = 0;
        let keys_offset   = align_size(hashes_offset + hashes_size, keys_align);
        let vals_offset   = align_size(keys_offset + keys_size, vals_align);
        let end = vals_offset + vals_size;

        let buffer = global_heap::malloc_raw(end);

        let hashes = buffer.offset(hashes_offset) as *mut u64;
        let keys   = buffer.offset(keys_offset)   as *mut K;
        let vals   = buffer.offset(vals_offset)   as *mut V;

         */

        let hashes = global_heap::malloc_raw(hashes_size) as *mut u64;
        let keys   = global_heap::malloc_raw(keys_size)   as *mut K;
        let values = global_heap::malloc_raw(vals_size)   as *mut V;

        Table {
            capacity: capacity,
            size:     0,
            hashes:   hashes,
            keys:     keys,
            values:   values,
        }
    }

    /// Creates a new raw table from a given capacity. All buckets are
    /// initially empty.
    pub fn new(capacity: uint) -> Table<K, V> {
        unsafe {
            let ret = Table::new_uninitialized(capacity);

            for i in range(0, ret.capacity as int) {
                *ret.hashes.offset(i) = EMPTY_BUCKET;
            }

            ret
        }
    }

    pub fn move_iter(self) -> MoveEntries<K, V> {
        MoveEntries { table: self, idx: 0 }
    }

    pub fn size(&self) -> uint {
        self.borrow().size
    }

    pub fn capacity(&self) -> uint {
        self.borrow().capacity
    }
}

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

#[unsafe_destructor]
impl<K, V> Drop for Table<K, V> {
    fn drop(&mut self) {
        // Ideally, this should be in reverse, since we're likely to have
        // partially taken some elements out with `.move_iter()` from the
        // front.
        for i in range_step_inclusive(self.capacity as int - 1, 0, -1) {
            // Check if the size is 0, so we don't do a useless scan when
            // dropping empty tables such as on resize.

            if self.size == 0 { break }

            match self.peek(i as uint) {
                EmptyBucket(eb)  => {},
                FullBucket(fb) => { fb.take(); }
            }
        }

        assert!(self.size == 0);

        unsafe {
            libc::free(self.values as *mut libc::c_void);
            libc::free(self.keys   as *mut libc::c_void);
            libc::free(self.hashes as *mut libc::c_void);
        }
    }
}

///////////////////////////////////////////////////////////////////////////
//

pub struct MoveEntries<K, V> {
    table: Table<K, V>,
    idx: uint,
}

impl<K, V> Iterator<(SafeHash, K, V)> for MoveEntries<K, V> {
    fn next(&mut self) -> Option<(SafeHash, K, V)> {
        while self.idx < self.table.capacity {
            let i = self.idx;
            self.idx += 1;

            match peek(&mut self.table, i) {
                EmptyBucket(_) => {},
                FullBucket(b) => {
                    let h = b.hash;
                    let (_, k, v) = b.take();
                    return Some((h, k, v));
                }
            }
        }

        None
    }

    fn size_hint(&self) -> (uint, Option<uint>) {
        let size = self.table.size;
        (size, Some(size))
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
            assert_eq!(self.table.hash(self.index), 0);
            *self.table.hashes.offset(index) = hash.to_u64();
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
            (transmute::<*mut u64, &'a mut SafeHash>(
                self.table.hashes.offset(index)),
             &mut *self.table.keys.offset(index),
             &mut *self.table.values.offset(index))
        }
    }

    pub fn take(self) -> (EmptyBucketMut<'table,K,V>, K, V) {
        unsafe {
            let index = self.index as int;
            *self.table.hashes.offset(index) = EMPTY_BUCKET;
            let keys: *K = &*self.table.keys;
            let key = ptr::read(keys.offset(index));
            let values: *V = &*self.table.values;
            let value = ptr::read(values.offset(index));
            self.table.size -= 1;
            (EmptyBucket { index: self.index, table: self.table }, key, value)
        }
    }
}

impl<'table,K,V> FullBucket<&'table mut Table<K,V>> {
    pub fn to_mut_refs(self) -> (&'table mut K, &'table mut V) {
        unsafe {
            let FullBucket { index, table, .. } = self;
            let index = index as int; // FIXME
            (&mut *table.keys.offset(index),
             &mut *table.values.offset(index))
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

impl<'table,K,V> FullBucket<&'table Table<K,V>> {
    pub fn to_refs(self) -> (&'table K, &'table V) {
        unsafe {
            let FullBucket { index, table, .. } = self;
            let index = index as int; // FIXME
            (&*table.keys.offset(index),
             &*table.values.offset(index))
        }
    }
}
