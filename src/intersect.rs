use binary_heap_plus::{BinaryHeap, FnComparator, PeekMut};
use core::cmp::Ordering;

pub fn intersect_iters<'a, T: Ord + 'a, I: Iterator<Item = T>>(
    iters: &mut [I],
) -> IntersectIterator<
    T,
    I,
    impl Fn(&T, &T) -> Ordering + 'a,
    impl Fn(&(usize, T), &(usize, T)) -> Ordering + 'a,
> {
    intersect_iters_by(iters, T::cmp)
}

pub fn intersect_iters_by<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering + Copy + 'a>(
    iters: &mut [I],
    cmp: F,
) -> IntersectIterator<T, I, F, impl Fn(&(usize, T), &(usize, T)) -> Ordering + 'a> {
    let n_iters = iters.len();
    let mut heap = BinaryHeap::with_capacity_by(n_iters, move |(_, x), (_, y)| cmp(y, x));
    let mut exhausted = false;
    for (i, iter) in iters.iter_mut().enumerate() {
        if let Some(x) = iter.next() {
            heap.push((i, x));
        } else {
            exhausted = true;
            break;
        }
    }
    let popped = Vec::with_capacity(n_iters);
    IntersectIterator {
        n_iters,
        iters,
        cmp,
        heap,
        popped,
        exhausted,
    }
}

pub struct IntersectIterator<
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
    exhausted: bool,
}

impl<
        'a,
        T,
        I: Iterator<Item = T>,
        F: Fn(&T, &T) -> Ordering,
        G: Fn(&(usize, T), &(usize, T)) -> Ordering,
    > Iterator for IntersectIterator<'a, T, I, F, G>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        while !self.exhausted {
            let (i, x) = self.heap.pop().unwrap();
            self.popped.push(i);
            while let Some(peek) = self.heap.peek_mut() {
                if (self.cmp)(&x, &peek.1) == Ordering::Equal {
                    let (j, _) = PeekMut::pop(peek);
                    self.popped.push(j);
                } else {
                    break;
                }
            }
            let n_popped = self.popped.len();
            for j in self.popped.drain(..) {
                if let Some(y) = self.iters[j].next() {
                    self.heap.push((j, y));
                } else {
                    self.exhausted = true;
                    break;
                }
            }
            if n_popped == self.n_iters {
                return Some(x);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intersect() {
        let it1 = 1u8..=5;
        let it2 = 3u8..=7;
        let it3 = 2u8..=4;
        let mut iters = [it1, it2, it3];
        let res: Vec<_> = intersect_iters(&mut iters).collect();
        assert_eq!(res, vec![3, 4]);
        assert!(iters[1].next().is_some());
    }

    #[test]
    fn test_intersect_by() {
        let it1 = 1u8..=5;
        let it2 = 3u8..=7;
        let it3 = 2u8..=4;
        let mut iters = [it1, it2, it3];
        let res: Vec<_> = intersect_iters_by(&mut iters, u8::cmp).collect();
        assert_eq!(res, vec![3, 4]);
        assert!(iters[1].next().is_some());
    }
}
