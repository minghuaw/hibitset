use std::default::Default;
use std::fmt::{Debug, Error as FormatError, Formatter};
use std::iter::repeat;
// use std::sync::atomic::{AtomicUsize, Ordering};

use atom::AtomSetOnce;

use crossbeam_utils::atomic::AtomicCell;

use crate::util::*;
use crate::{BitSetLike, DrainableBitSet};

/// This is similar to a [`BitSet`] but allows setting of value
/// without unique ownership of the structure
///
/// An `AtomicBitSet` has the ability to add an item to the set
/// without unique ownership (given that the set is big enough).
/// Removing elements does require unique ownership as an effect
/// of the hierarchy it holds. Worst case multiple writers set the
/// same bit twice (but only is told they set it).
///
/// It is possible to atomically remove from the set, but not at the
/// same time as atomically adding. This is because there is no way
/// to know if layer 1-3 would be left in a consistent state if they are
/// being cleared and set at the same time.
///
/// `AtromicBitSet` resolves this race by disallowing atomic
/// clearing of bits.
///
/// [`BitSet`]: ../struct.BitSet.html
#[derive(Debug)]
pub struct AtomicBitSet {
    layer4: AtomicCell<u128>,
    layer3: Vec<AtomicCell<u128>>,
    layer2: Vec<AtomicCell<u128>>,
    layer1: Vec<AtomicBlock>,
}

impl AtomicBitSet {
    /// Creates an empty `AtomicBitSet`.
    pub fn new() -> AtomicBitSet {
        Default::default()
    }

    /// Adds `id` to the `AtomicBitSet`. Returns `true` if the value was
    /// already in the set.
    ///
    /// Because we cannot safely extend an AtomicBitSet without unique ownership
    /// this will panic if the Index is out of range.
    #[inline]
    pub fn add_atomic(&self, id: Index) -> bool {
        let (_, p1, p2, p3) = offsets(id);

        // While it is tempting to check of the bit was set and exit here if it
        // was, this can result in a data race. If this thread and another
        // thread both set the same bit it is possible for the second thread
        // to exit before l3 was set. Resulting in the iterator to be in an
        // incorrect state. The window is small, but it exists.
        let set = self.layer1[p1].add(id);
        self.layer2[p2].fetch_or(id.mask(SHIFT2));
        self.layer3[p3].fetch_or(id.mask(SHIFT3));
        self.layer4.fetch_or(id.mask(SHIFT4));
        set
    }

    /// Adds `id` to the `BitSet`. Returns `true` if the value was
    /// already in the set.
    #[inline]
    pub fn add(&mut self, id: Index) -> bool {
        // use std::sync::atomic::Ordering::Relaxed;

        let (_, p1, p2, p3) = offsets(id);
        if self.layer1[p1].add(id) {
            return true;
        }

        self.layer2[p2].store(self.layer2[p2].load() | id.mask(SHIFT2));
        self.layer3[p3].store(self.layer3[p3].load() | id.mask(SHIFT3));
        self.layer4
            .store(self.layer4.load() | id.mask(SHIFT4));
        false
    }

    /// Removes `id` from the set, returns `true` if the value
    /// was removed, and `false` if the value was not set
    /// to begin with.
    #[inline]
    pub fn remove(&mut self, id: Index) -> bool {
        // use std::sync::atomic::Ordering::Relaxed;
        let (_, p1, p2, p3) = offsets(id);

        // if the bitmask was set we need to clear
        // its bit from layer0 to 3. the layers above only
        // should be cleared if the bit cleared was the last bit
        // in its set
        //
        // These are used over a `fetch_and` because we have a mutable
        // access to the AtomicBitSet so this is sound (and faster)
        if !self.layer1[p1].remove(id) {
            return false;
        }
        if self.layer1[p1].mask.load() != 0 {
            return true;
        }

        let v = self.layer2[p2].load() & !id.mask(SHIFT2);
        self.layer2[p2].store(v);
        if v != 0 {
            return true;
        }

        let v = self.layer3[p3].load() & !id.mask(SHIFT3);
        self.layer3[p3].store(v);
        if v != 0 {
            return true;
        }

        let v = self.layer4.load() & !id.mask(SHIFT4);
        self.layer4.store(v);
        return true;
    }

    /// Returns `true` if `id` is in the set.
    #[inline]
    pub fn contains(&self, id: Index) -> bool {
        let i = id.offset(SHIFT2);
        self.layer1[i].contains(id)
    }

    /// Clear all bits in the set
    pub fn clear(&mut self) {
        // This is the same hierarchical-striding used in the iterators.
        // Using this technique we can avoid clearing segments of the bitset
        // that are already clear. In the best case when the set is already cleared,
        // this will only touch the highest layer.

        let (mut m4, mut m3, mut m2) = (self.layer4.swap(0), 0u128, 0u128);
        let mut offset = 0;

        loop {
            if m2 != 0 {
                let bit = m2.trailing_zeros() as usize;
                m2 &= !(1 << bit);

                // layer 1 & 0 are cleared unconditionally. it's only 32-64 words
                // and the extra logic to select the correct works is slower
                // then just clearing them all.
                self.layer1[offset + bit].clear();
                continue;
            }

            if m3 != 0 {
                let bit = m3.trailing_zeros() as usize;
                m3 &= !(1 << bit);
                offset = bit << BITS;
                m2 = self.layer2[bit].swap(0); // FIXME: what does offset do?
                continue;
            }

            if m4 != 0 {
                let bit = m4.trailing_zeros() as usize;
                m4 &= !(1 << bit);
                // offset = bit << BITS;
                m3 = self.layer3[bit].swap(0);
                continue;
            }

            break;
        }
    }
}

impl BitSetLike for AtomicBitSet {
    #[inline]
    fn layer4(&self) -> u128 {
        self.layer4.load()
    }
    #[inline]
    fn layer3(&self, i: usize) -> u128 {
        self.layer3[i].load()
    }
    #[inline]
    fn layer2(&self, i: usize) -> u128 {
        self.layer2[i].load()
    }
    #[inline]
    fn layer1(&self, i: usize) -> u128 {
        self.layer1[i].mask.load()
    }
    #[inline]
    fn layer0(&self, i: usize) -> u128 {
        let (o1, o0) = (i >> BITS, i & ((1 << BITS) - 1));
        self.layer1[o1]
            .atom
            .get()
            .map(|l0| l0[o0].load())
            .unwrap_or(0)
    }
    #[inline]
    fn contains(&self, i: Index) -> bool {
        self.contains(i)
    }
}

impl DrainableBitSet for AtomicBitSet {
    #[inline]
    fn remove(&mut self, i: Index) -> bool {
        self.remove(i)
    }
}

impl Default for AtomicBitSet {
    fn default() -> Self {
        AtomicBitSet {
            layer4: Default::default(),
            layer3:  repeat(0)
                .map(|_| AtomicCell::new(0))
                .take(1 << BITS)
                .collect(),
            layer2: repeat(0)
                .map(|_| AtomicCell::new(0))
                .take(1 << BITS)
                .collect(),
            layer1: repeat(0)
                .map(|_| AtomicBlock::new())
                .take(1 << (2 * BITS))
                .collect(),
        }
    }
}

struct AtomicBlock {
    mask: AtomicCell<u128>,
    atom: AtomSetOnce<Box<[AtomicCell<u128>; 1 << BITS]>>,
}

impl AtomicBlock {
    fn new() -> AtomicBlock {
        AtomicBlock {
            mask: AtomicCell::new(0),
            atom: AtomSetOnce::empty(),
        }
    }

    fn add(&self, id: Index) -> bool {
        if self.atom.is_none() {
            let v = Box::new(unsafe { ::std::mem::zeroed() });
            self.atom.set_if_none(v);
        }

        let (i, m) = (id.row(SHIFT1), id.mask(SHIFT0));
        let old = self.atom.get().unwrap()[i].fetch_or(m);
        self.mask.fetch_or(id.mask(SHIFT1));
        old & m != 0
    }

    fn contains(&self, id: Index) -> bool {
        self.atom
            .get()
            .map(|l0| l0[id.row(SHIFT1)].load() & id.mask(SHIFT0) != 0)
            .unwrap_or(false)
    }

    fn remove(&mut self, id: Index) -> bool {
        if let Some(l0) = self.atom.get_mut() {
            let (i, m) = (id.row(SHIFT1), !id.mask(SHIFT0));
            let v = l0[i].load();
            l0[i].store(v & m);
            if v & m == 0 {
                let v = self.mask.load() & !id.mask(SHIFT1);
                self.mask.store(v);
            }
            v & id.mask(SHIFT0) == id.mask(SHIFT0)
        } else {
            false
        }
    }

    fn clear(&mut self) {
        self.mask.store(0);
        self.atom.get().map(|l0| {
            for l in &l0[..] {
                l.store(0);
            }
        });
    }
}

impl Debug for AtomicBlock {
    fn fmt(&self, f: &mut Formatter) -> Result<(), FormatError> {
        f.debug_struct("AtomicBlock")
            .field("mask", &self.mask)
            .field("atom", &self.atom.get().unwrap().iter())
            .finish()
    }
}

#[cfg(test)]
mod atomic_set_test {
    use crate::{AtomicBitSet, BitSetAnd, BitSetLike, util::Index};

    #[test]
    fn insert() {
        let mut c = AtomicBitSet::new();
        for i in 0..1_000 {
            assert!(!c.add(i));
            assert!(c.add(i));
        }

        for i in 0..1_000 {
            assert!(c.contains(i));
        }
    }

    #[test]
    fn insert_100k() {
        let mut c = AtomicBitSet::new();
        for i in 0..100_000 {
            assert!(!c.add(i));
            assert!(c.add(i));
        }

        for i in 0..100_000 {
            assert!(c.contains(i));
        }
    }

    #[test]
    fn add_atomic() {
        let c = AtomicBitSet::new();
        for i in 0..1_000 {
            assert!(!c.add_atomic(i));
            assert!(c.add_atomic(i));
        }

        for i in 0..1_000 {
            assert!(c.contains(i));
        }
    }

    #[test]
    fn add_atomic_100k() {
        let c = AtomicBitSet::new();
        for i in 0..100_000 {
            assert!(!c.add_atomic(i));
            assert!(c.add_atomic(i));
        }

        for i in 0..100_000 {
            assert!(c.contains(i));
        }
    }

    #[test]
    fn remove() {
        let mut c = AtomicBitSet::new();
        for i in 0..1_000 {
            assert!(!c.add(i));
        }

        for i in 0..1_000 {
            assert!(c.contains(i));
            assert!(c.remove(i));
            assert!(!c.contains(i));
            assert!(!c.remove(i));
        }
    }

    #[test]
    fn iter() {
        let mut c = AtomicBitSet::new();
        for i in 0..100_000 {
            c.add(i);
        }

        let mut count = 0;
        for (idx, i) in c.iter().enumerate() {
            count += 1;
            assert_eq!(idx, i as usize);
        }
        assert_eq!(count, 100_000);
    }

    #[test]
    fn iter_odd_even() {
        let mut odd = AtomicBitSet::new();
        let mut even = AtomicBitSet::new();
        for i in 0..100_000 {
            if i % 2 == 1 {
                odd.add(i);
            } else {
                even.add(i);
            }
        }

        assert_eq!((&odd).iter().count(), 50_000);
        assert_eq!((&even).iter().count(), 50_000);
        assert_eq!(BitSetAnd(&odd, &even).iter().count(), 0);
    }

    #[test]
    fn clear() {
        let mut set = AtomicBitSet::new();
        for i in 0..1_000 {
            set.add(i);
        }

        assert_eq!((&set).iter().sum::<Index>(), 500_500 - 1_000);

        assert_eq!((&set).iter().count(), 1_000);
        set.clear();
        assert_eq!((&set).iter().count(), 0);

        for i in 0..1_000 {
            set.add(i * 64);
        }

        assert_eq!((&set).iter().count(), 1_000);
        set.clear();
        assert_eq!((&set).iter().count(), 0);

        for i in 0..1_000 {
            set.add(i * 1_000);
        }

        assert_eq!((&set).iter().count(), 1_000);
        set.clear();
        assert_eq!((&set).iter().count(), 0);

        for i in 0..100 {
            set.add(i * 10_000);
        }

        assert_eq!((&set).iter().count(), 100);
        set.clear();
        assert_eq!((&set).iter().count(), 0);

        for i in 0..10 {
            set.add(i * 10_000);
        }

        assert_eq!((&set).iter().count(), 10);
        set.clear();
        assert_eq!((&set).iter().count(), 0);
    }

}
