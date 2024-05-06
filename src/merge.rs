use binary_heap_plus::{BinaryHeap, FnComparator, PeekMut};
use core::cmp::Ordering;

pub fn merge_iters<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering + Copy + 'a>(
    iters: &mut [I],
    cmp: F,
) -> MergeIterator<T, I, F, impl Fn(&(usize, T), &(usize, T)) -> Ordering + 'a> {
    let n_iters = iters.len();
    let mut heap = BinaryHeap::with_capacity_by(n_iters, move |(_, x), (_, y)| cmp(y, x));
    for (i, iter) in iters.iter_mut().enumerate() {
        if let Some(x) = iter.next() {
            heap.push((i, x));
        }
    }
    let popped = Vec::with_capacity(n_iters);
    MergeIterator {
        iters,
        cmp,
        heap,
        popped,
    }
}

pub struct MergeIterator<
    'a,
    T,
    I: Iterator<Item = T>,
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&(usize, T), &(usize, T)) -> Ordering,
> {
    iters: &'a mut [I],
    cmp: F,
    heap: BinaryHeap<(usize, T), FnComparator<G>>,
    popped: Vec<usize>,
}

impl<
        'a,
        T,
        I: Iterator<Item = T>,
        F: Fn(&T, &T) -> Ordering,
        G: Fn(&(usize, T), &(usize, T)) -> Ordering,
    > Iterator for MergeIterator<'a, T, I, F, G>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((i, x)) = self.heap.pop() {
            self.popped.push(i);
            while let Some(peek) = self.heap.peek_mut() {
                if (self.cmp)(&x, &peek.1) == Ordering::Equal {
                    let (j, _) = PeekMut::pop(peek);
                    self.popped.push(j);
                } else {
                    break;
                }
            }
            for j in self.popped.drain(..) {
                if let Some(y) = self.iters[j].next() {
                    self.heap.push((j, y));
                }
            }
            Some(x)
        } else {
            None
        }
    }
}

pub fn merge_iters_detailed<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering + Copy + 'a>(
    iters: &mut [I],
    cmp: F,
) -> DetailedMergeIterator<T, I, F, impl Fn(&(usize, T), &(usize, T)) -> Ordering + 'a> {
    let n_iters = iters.len();
    let mut heap = BinaryHeap::with_capacity_by(n_iters, move |(_, x), (_, y)| cmp(y, x));
    for (i, iter) in iters.iter_mut().enumerate() {
        if let Some(x) = iter.next() {
            heap.push((i, x));
        }
    }
    let popped = Vec::with_capacity(n_iters);
    DetailedMergeIterator {
        n_iters,
        iters,
        cmp,
        heap,
        popped,
    }
}

pub struct DetailedMergeIterator<
    'a,
    T,
    I: Iterator<Item = T>,
    F: Fn(&T, &T) -> Ordering,
    G: Fn(&(usize, T), &(usize, T)) -> Ordering,
> {
    n_iters: usize,
    iters: &'a mut [I],
    cmp: F,
    heap: BinaryHeap<(usize, T), FnComparator<G>>,
    popped: Vec<usize>,
}

impl<
        'a,
        T,
        I: Iterator<Item = T>,
        F: Fn(&T, &T) -> Ordering,
        G: Fn(&(usize, T), &(usize, T)) -> Ordering,
    > Iterator for DetailedMergeIterator<'a, T, I, F, G>
{
    type Item = Vec<Option<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((i, x)) = self.heap.pop() {
            let mut details = Vec::from_iter((0..self.n_iters).map(|_| None));
            self.popped.push(i);
            while let Some(peek) = self.heap.peek_mut() {
                if (self.cmp)(&x, &peek.1) == Ordering::Equal {
                    let (j, y) = PeekMut::pop(peek);
                    self.popped.push(j);
                    details[j] = Some(y);
                } else {
                    break;
                }
            }
            details[i] = Some(x);
            for j in self.popped.drain(..) {
                if let Some(y) = self.iters[j].next() {
                    self.heap.push((j, y));
                }
            }
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
        let res: Vec<_> = merge_iters(&mut iters, u8::cmp).collect();
        assert_eq!(res, vec![1, 2, 3, 4, 5, 6, 7]);
        assert!(iters[1].next().is_none());
    }

    #[test]
    fn test_merge_details() {
        let it1 = 1u8..=2;
        let it2 = 2u8..=3;
        let mut iters = [it1, it2];
        let res: Vec<_> = merge_iters_detailed(&mut iters, u8::cmp).collect();
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
