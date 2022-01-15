use util::*;
use {BitSet, BitSetLike};

pub use self::drain::DrainBitIter;

#[cfg(feature = "parallel")]
pub use self::parallel::{BitParIter, BitProducer};

mod drain;
#[cfg(feature = "parallel")]
mod parallel;

/// An `Iterator` over a [`BitSetLike`] structure.
///
/// [`BitSetLike`]: ../trait.BitSetLike.html
#[derive(Debug, Clone)]
pub struct BitIter<T, const N: usize> {
    pub(crate) set: T,
    pub(crate) top_mask: [usize; N],
    pub(crate) bot_masks: [usize; LAYERS - 1],
    // pub(crate) prefix: [u32; LAYERS - 1],
    pub(crate) prefix: [u32; LAYERS]
}

impl<T, const N: usize> BitIter<T, N> {
    /// Creates a new `BitIter`. You usually don't call this function
    /// but just [`.iter()`] on a bit set.
    ///
    /// [`.iter()`]: ../trait.BitSetLike.html#method.iter
    pub fn new(set: T, top_mask: [usize; N], bot_masks: [usize; LAYERS - 1], prefix: [u32; LAYERS]) -> Self {
        BitIter {
            set,
            top_mask,
            bot_masks,
            prefix,
        }
    }
}

impl<T: BitSetLike<N>, const N: usize> BitIter<T, N> {
    /// Allows checking if set bit is contained in underlying bit set.
    pub fn contains(&self, i: Index) -> bool {
        self.set.contains(i)
    }
}

impl<'a, const N: usize> BitIter<&'a mut BitSet<N>, N> {
    /// Clears the rest of the bitset starting from the next inner layer.
    pub(crate) fn clear(&mut self) {
        use self::State::Continue;
        while let Some(level) = (1..LAYERS).find(|&level| self.handle_level(level) == Continue) {
            let lower = level - 1;
            let idx = (self.prefix[lower] >> BITS) as usize;
            *self.set.layer_mut(lower, idx) = 0;
            if level == LAYERS - 1 {
                for i in 0..N {
                    self.set.layer3[i] &= !((2 << idx) - 1);
                }
            }
        }
    }
}

#[derive(PartialEq)]
pub(crate) enum State {
    Empty,
    Continue,
    Value(Index),
}

impl<T, const N: usize> Iterator for BitIter<T, N>
where
    T: BitSetLike<N>,
{
    type Item = Index;

    fn next(&mut self) -> Option<Self::Item> {
        use self::State::*;
        'find: loop {
            for level in 0..LAYERS {
                match self.handle_level(level) {
                    Value(v) => return Some(v),
                    Continue => continue 'find,
                    Empty => {}
                }
            }
            // There is no set bits left
            return None;
        }
    }
}

impl<T: BitSetLike<N>, const N: usize> BitIter<T, N> {
    pub(crate) fn handle_level(&mut self, level: usize) -> State {
        use self::State::*;

        // layer3 is the top layer
        if level == 3 {
            if self.top_mask == [0; N] {
                Empty
            } else {
                let mut first_bit = 0;
                let mut mask = [0; N];
                for i in 0..N {
                    let trailing_zeros = self.top_mask[i].trailing_zeros();
                    mask[i] &= !(1 << trailing_zeros);
                    first_bit += trailing_zeros;
                }
                // TODO: what does this do?
                let idx = self.prefix.get(level).cloned().unwrap_or(0) | first_bit;
                self.bot_masks[level - 1] = self.set.get_from_layer(level - 1, idx as usize);
                self.prefix[level - 1] = idx << BITS;
                Continue
            }
        } else {
            if self.bot_masks[level] == 0 {
                Empty
            } else {
                // Take the first bit that isn't zero
                let first_bit = self.bot_masks[level].trailing_zeros();
                // Remove it from the mask
                self.bot_masks[level] &= !(1 << first_bit);
                // Calculate the index of it
                let idx = self.prefix.get(level).cloned().unwrap_or(0) | first_bit;
                if level == 0 {
                    // It's the lowest layer, so the `idx` is the next set bit
                    Value(idx)
                } else {
                    // Take the corresponding `usize` from the layer below
                    self.bot_masks[level - 1] = self.set.get_from_layer(level - 1, idx as usize);
                    self.prefix[level - 1] = idx << BITS;
                    Continue
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use {BitSet, BitSetLike};

    #[test]
    fn iterator_clear_empties() {
        use rand::prelude::*;

        let mut set = BitSet::new();
        let mut rng = thread_rng();
        let limit = 1_048_576;
        for _ in 0..(limit / 10) {
            set.add(rng.gen_range(0, limit));
        }
        (&mut set).iter().clear();
        for &i in &set.layer3 {
            assert_eq!(0, i);
        }
        for &i in &set.layer2 {
            assert_eq!(0, i);
        }
        for &i in &set.layer1 {
            assert_eq!(0, i);
        }
        for &i in &set.layer0 {
            assert_eq!(0, i);
        }
    }

    #[test]
    fn iterator_clone() {
        let mut set = BitSet::new();
        set.add(1);
        set.add(3);
        let iter = set.iter().skip(1);
        for (a, b) in iter.clone().zip(iter) {
            assert_eq!(a, b);
        }
    }
}
