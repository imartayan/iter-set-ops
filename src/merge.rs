use binary_heap_plus::{BinaryHeap, PeekMut};
use compare::Compare;
use core::cmp::Ordering;
use core::mem::swap;
use core::ops::DerefMut;

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

impl<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering, C: Compare<(usize, T)>> Iterator
    for MergeIterator<'a, T, I, F, C>
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

impl<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering, C: Compare<(usize, T)>> Iterator
    for DetailedMergeIterator<'a, T, I, F, C>
{
    type Item = Vec<Option<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.heap.is_empty() {
            let mut details = Vec::from_iter((0..self.iters.len()).map(|_| None));
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
                        details[entry.0] = Some(x);
                    } else {
                        let (j, x) = PeekMut::pop(peek);
                        details[j] = Some(x);
                    }
                } else {
                    break;
                }
            }
            details[i] = Some(res);
            Some(details)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let it1 = 1u8..=5;
        let it2 = 3u8..=7;
        let it3 = 2u8..=4;
        let mut iters = [it1, it2, it3];
        let res: Vec<_> = merge_iters_by(&mut iters, u8::cmp).collect();
        assert_eq!(res, vec![1, 2, 3, 4, 5, 6, 7]);
        assert!(iters[1].next().is_none());
    }

    #[test]
    fn test_merge_detailed() {
        let it1 = 1u8..=2;
        let it2 = 2u8..=3;
        let mut iters = [it1, it2];
        let res: Vec<_> = merge_iters_detailed(&mut iters).collect();
        assert_eq!(
            res,
            vec![
                vec![Some(1), None],
                vec![Some(2), Some(2)],
                vec![None, Some(3)]
            ]
        );
        assert!(iters[1].next().is_none());
    }

    #[test]
    fn test_merge_detailed_by() {
        let it1 = 1u8..=2;
        let it2 = 2u8..=3;
        let mut iters = [it1, it2];
        let res: Vec<_> = merge_iters_detailed_by(&mut iters, u8::cmp).collect();
        assert_eq!(
            res,
            vec![
                vec![Some(1), None],
                vec![Some(2), Some(2)],
                vec![None, Some(3)]
            ]
        );
        assert!(iters[1].next().is_none());
    }
}
