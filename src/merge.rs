use binary_heap_plus::{BinaryHeap, PeekMut};
use compare::Compare;
use core::cmp::Ordering;
use core::mem::swap;
use core::ops::DerefMut;

/// Iterates over the union of many sorted deduplicated iterators.
///
/// # Examples
///
/// ```
/// use iter_set_ops::merge_iters;
///
/// let it1 = 1u8..=5;
/// let it2 = 3u8..=7;
/// let it3 = 2u8..=4;
/// let mut iters = [it1, it2, it3];
/// let res: Vec<_> = merge_iters(&mut iters).collect();
///
/// assert_eq!(res, vec![1, 2, 3, 4, 5, 6, 7]);
/// ```
#[inline]
pub fn merge_iters<'a, T: Ord + 'a, I: Iterator<Item = T>>(
    iters: &mut [I],
) -> MergeIterator<
    T,
    I,
    impl Fn(&T, &T) -> Ordering + 'a,
    impl Fn(&(usize, T), &(usize, T)) -> Ordering + 'a,
> {
    merge_iters_by(iters, T::cmp)
}

/// Iterates over the union of many sorted deduplicated iterators, using `cmp` as the comparison operator.
///
/// # Examples
///
/// ```
/// use iter_set_ops::merge_iters_by;
///
/// let it1 = (1u8..=5).rev();
/// let it2 = (3u8..=7).rev();
/// let it3 = (2u8..=4).rev();
/// let mut iters = [it1, it2, it3];
/// let res: Vec<_> = merge_iters_by(&mut iters, |x, y| y.cmp(x)).collect();
///
/// assert_eq!(res, vec![7, 6, 5, 4, 3, 2, 1]);
/// ```
pub fn merge_iters_by<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering + Copy + 'a>(
    iters: &mut [I],
    cmp: F,
) -> MergeIterator<T, I, F, impl Fn(&(usize, T), &(usize, T)) -> Ordering + 'a> {
    let mut vec = Vec::with_capacity(iters.len());
    for (i, iter) in iters.iter_mut().enumerate() {
        if let Some(x) = iter.next() {
            vec.push((i, x));
        }
    }
    let heap = BinaryHeap::from_vec_cmp(vec, move |(_, x): &(usize, T), (_, y): &(usize, T)| {
        cmp(y, x)
    });
    MergeIterator { iters, cmp, heap }
}

pub struct MergeIterator<
    'a,
    T,
    I: Iterator<Item = T>,
    F: Fn(&T, &T) -> Ordering,
    C: Compare<(usize, T)>,
> {
    iters: &'a mut [I],
    cmp: F,
    heap: BinaryHeap<(usize, T), C>,
}

impl<T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering, C: Compare<(usize, T)>> Iterator
    for MergeIterator<'_, T, I, F, C>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.heap.is_empty() {
            let res = {
                let mut peek = self.heap.peek_mut().unwrap();
                let entry = peek.deref_mut();
                if let Some(mut x) = self.iters[entry.0].next() {
                    swap(&mut entry.1, &mut x);
                    x
                } else {
                    PeekMut::pop(peek).1
                }
            };
            while let Some(mut peek) = self.heap.peek_mut() {
                if (self.cmp)(&res, &peek.1) == Ordering::Equal {
                    let entry = peek.deref_mut();
                    if let Some(mut x) = self.iters[entry.0].next() {
                        swap(&mut entry.1, &mut x);
                    } else {
                        PeekMut::pop(peek);
                    }
                } else {
                    break;
                }
            }
            Some(res)
        } else {
            None
        }
    }
}

/// Iterates over the union of many sorted deduplicated iterators and groups equal items with their indices into a [`Vec`].
///
/// # Examples
///
/// ```
/// use iter_set_ops::merge_iters_detailed;
///
/// let it1 = 1u8..=2;
/// let it2 = 2u8..=3;
/// let mut iters = [it1, it2];
/// let res: Vec<_> = merge_iters_detailed(&mut iters).collect();
///
/// assert_eq!(res, vec![vec![(0, 1)], vec![(1, 2), (0, 2)], vec![(1, 3)]]);
/// ```
#[inline]
pub fn merge_iters_detailed<'a, T: Ord + 'a, I: Iterator<Item = T>>(
    iters: &mut [I],
) -> DetailedMergeIterator<
    T,
    I,
    impl Fn(&T, &T) -> Ordering + 'a,
    impl Fn(&(usize, T), &(usize, T)) -> Ordering + 'a,
> {
    merge_iters_detailed_by(iters, T::cmp)
}

/// Iterates over the union of many sorted deduplicated iterators and groups equal items with their indices into a [`Vec`], using `cmp` as the comparison operator.
///
/// # Examples
///
/// ```
/// use iter_set_ops::merge_iters_detailed_by;
///
/// let it1 = (1u8..=2).rev();
/// let it2 = (2u8..=3).rev();
/// let mut iters = [it1, it2];
/// let res: Vec<_> = merge_iters_detailed_by(&mut iters, |x, y| y.cmp(x)).collect();
///
/// assert_eq!(res, vec![vec![(1, 3)], vec![(0, 2), (1, 2)], vec![(0, 1)]]);
/// ```
pub fn merge_iters_detailed_by<
    'a,
    T,
    I: Iterator<Item = T>,
    F: Fn(&T, &T) -> Ordering + Copy + 'a,
>(
    iters: &mut [I],
    cmp: F,
) -> DetailedMergeIterator<T, I, F, impl Fn(&(usize, T), &(usize, T)) -> Ordering + 'a> {
    let mut vec = Vec::with_capacity(iters.len());
    for (i, iter) in iters.iter_mut().enumerate() {
        if let Some(x) = iter.next() {
            vec.push((i, x));
        }
    }
    let heap = BinaryHeap::from_vec_cmp(vec, move |(_, x): &(usize, T), (_, y): &(usize, T)| {
        cmp(y, x)
    });
    DetailedMergeIterator { iters, cmp, heap }
}

pub struct DetailedMergeIterator<
    'a,
    T,
    I: Iterator<Item = T>,
    F: Fn(&T, &T) -> Ordering,
    C: Compare<(usize, T)>,
> {
    iters: &'a mut [I],
    cmp: F,
    heap: BinaryHeap<(usize, T), C>,
}

impl<T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering, C: Compare<(usize, T)>> Iterator
    for DetailedMergeIterator<'_, T, I, F, C>
{
    type Item = Vec<(usize, T)>;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.heap.is_empty() {
            let mut details = Vec::new();
            let (i, res) = {
                let mut peek = self.heap.peek_mut().unwrap();
                let entry = peek.deref_mut();
                if let Some(mut x) = self.iters[entry.0].next() {
                    swap(&mut entry.1, &mut x);
                    (entry.0, x)
                } else {
                    PeekMut::pop(peek)
                }
            };
            while let Some(mut peek) = self.heap.peek_mut() {
                if (self.cmp)(&res, &peek.1) == Ordering::Equal {
                    let entry = peek.deref_mut();
                    if let Some(mut x) = self.iters[entry.0].next() {
                        swap(&mut entry.1, &mut x);
                        details.push((entry.0, x));
                    } else {
                        let (j, x) = PeekMut::pop(peek);
                        details.push((j, x));
                    }
                } else {
                    break;
                }
            }
            details.push((i, res));
            Some(details)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, Rng, SeedableRng};
    use std::collections::HashSet;

    #[test]
    fn test_merge() {
        let it1 = 1u8..=5;
        let it2 = 3u8..=7;
        let it3 = 2u8..=4;
        let mut iters = [it1, it2, it3];
        let res: Vec<_> = merge_iters(&mut iters).collect();

        assert_eq!(res, vec![1, 2, 3, 4, 5, 6, 7]);
        assert!(iters[1].next().is_none());
    }

    #[test]
    fn test_merge_by() {
        let it1 = (1u8..=5).rev();
        let it2 = (3u8..=7).rev();
        let it3 = (2u8..=4).rev();
        let mut iters = [it1, it2, it3];
        let res: Vec<_> = merge_iters_by(&mut iters, |x, y| y.cmp(x)).collect();

        assert_eq!(res, vec![7, 6, 5, 4, 3, 2, 1]);
        assert!(iters[1].next().is_none());
    }

    #[test]
    fn test_merge_detailed() {
        let it1 = 1u8..=2;
        let it2 = 2u8..=3;
        let mut iters = [it1, it2];
        let res: Vec<_> = merge_iters_detailed(&mut iters).collect();

        assert_eq!(res, vec![vec![(0, 1)], vec![(1, 2), (0, 2)], vec![(1, 3)]]);
        assert!(iters[1].next().is_none());
    }

    #[test]
    fn test_merge_detailed_by() {
        let it1 = (1u8..=2).rev();
        let it2 = (2u8..=3).rev();
        let mut iters = [it1, it2];
        let res: Vec<_> = merge_iters_detailed_by(&mut iters, |x, y| y.cmp(x)).collect();

        assert_eq!(res, vec![vec![(1, 3)], vec![(0, 2), (1, 2)], vec![(0, 1)]]);
        assert!(iters[1].next().is_none());
    }

    #[test]
    fn test_large_merge() {
        const C: usize = 10;
        const N: usize = 100_000;

        let mut iters: Vec<_> = (0..C).map(|i| (0..(C * N)).skip(i).step_by(C)).collect();
        let res: Vec<_> = merge_iters(&mut iters).collect();

        let expected: Vec<_> = (0..(C * N)).collect();
        assert_eq!(res, expected);
    }

    #[test]
    fn test_random_merge() {
        const C: usize = 10;
        const N: usize = 10_000;

        let mut rng = StdRng::seed_from_u64(42);
        let mut vecs = Vec::with_capacity(C);
        for _ in 0..C {
            let mut vec = Vec::with_capacity(N);
            for _ in 0..N {
                vec.push(rng.gen::<u16>());
            }
            vec.sort_unstable();
            vec.dedup();
            vecs.push(vec);
        }
        let mut iters: Vec<_> = vecs.iter().map(|v| v.iter()).collect();
        let res: HashSet<_> = merge_iters(&mut iters).collect();

        for vec in vecs.iter() {
            for x in vec {
                assert!(res.contains(x));
            }
        }
    }

    #[test]
    fn test_associative_merge() {
        const C: usize = 10;
        const N: usize = 10_000;

        let mut rng = StdRng::seed_from_u64(42);
        let mut vecs = Vec::with_capacity(C);
        for _ in 0..C {
            let mut vec = Vec::with_capacity(N);
            for _ in 0..N {
                vec.push(rng.gen::<u16>());
            }
            vec.sort_unstable();
            vec.dedup();
            vecs.push(vec);
        }

        let mut iters: Vec<_> = vecs.iter().map(|v| v.iter()).collect();
        let res10: HashSet<_> = merge_iters(&mut iters).collect();

        let mut nested_iters: Vec<Vec<_>> = (0..C)
            .step_by(5)
            .map(|i| vecs.iter().skip(i).take(5).map(|v| v.iter()).collect())
            .collect();
        let res5: HashSet<_> = merge_iters(
            &mut nested_iters
                .iter_mut()
                .map(|inner_iters| merge_iters(inner_iters))
                .collect::<Vec<_>>(),
        )
        .collect();

        let mut nested_iters: Vec<Vec<_>> = (0..C)
            .step_by(2)
            .map(|i| vecs.iter().skip(i).take(2).map(|v| v.iter()).collect())
            .collect();
        let res2: HashSet<_> = merge_iters(
            &mut nested_iters
                .iter_mut()
                .map(|inner_iters| merge_iters(inner_iters))
                .collect::<Vec<_>>(),
        )
        .collect();

        assert_eq!(res10, res5);
        assert_eq!(res10, res2);
    }
}
