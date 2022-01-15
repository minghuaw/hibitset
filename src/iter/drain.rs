use iter::BitIter;
use util::*;
use DrainableBitSet;

/// A draining `Iterator` over a [`DrainableBitSet`] structure.
///
/// [`DrainableBitSet`]: ../trait.DrainableBitSet.html
pub struct DrainBitIter<'a, T: 'a, const N: usize> {
    iter: BitIter<&'a mut T, N>,
}

impl<'a, T: DrainableBitSet<N>, const N: usize> DrainBitIter<'a, T, N> {
    /// Creates a new `DrainBitIter`. You usually don't call this function
    /// but just [`.drain()`] on a bit set.
    ///
    /// [`.drain()`]: ../trait.DrainableBitSet.html#method.drain
    pub fn new(set: &'a mut T, top_mask: [usize; N], bot_masks: [usize; LAYERS - 1], prefix: [u32; LAYERS]) -> Self {
        DrainBitIter {
            iter: BitIter::new(set, top_mask, bot_masks, prefix),
        }
    }
}

impl<'a, T, const N: usize> Iterator for DrainBitIter<'a, T, N>
where
    T: DrainableBitSet<N>,
{
    type Item = Index;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.iter.next();
        if let Some(next) = next {
            self.iter.set.remove(next);
        }
        next
    }
}

#[test]
fn drain_all() {
    use {BitSet, BitSetLike};
    let mut bit_set: BitSet<1> = (0..10000).filter(|i| i % 2 == 0).collect();
    bit_set.drain().for_each(|_| {});
    assert_eq!(0, bit_set.iter().count());
}
