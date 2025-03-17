use core::cmp::Ordering;
use core::mem::swap;

/// Iterates over the difference of many sorted deduplicated iterators.
///
/// # Examples
///
/// ```
/// use iter_set_ops::subtract_iters;
///
/// let it1 = 1u8..=9;
/// let it2 = 6u8..=10;
/// let it3 = 2u8..=4;
/// let res: Vec<_> = subtract_iters(it1, vec![it2, it3]).collect();
///
/// assert_eq!(res, vec![1, 5]);
/// ```
#[inline]
pub fn subtract_iters<T: Ord, I: Iterator<Item = T>, J: Iterator<Item = T>>(
    left_iter: I,
    right_iters: Vec<J>,
) -> SubtractIterator<T, I, J, impl Fn(&T, &T) -> Ordering> {
    subtract_iters_by(left_iter, right_iters, T::cmp)
}

/// Iterates over the difference of many sorted deduplicated iterators, using `cmp` as the comparison operator.
///
/// # Examples
///
/// ```
/// use iter_set_ops::subtract_iters_by;
///
/// let it1 = (1u8..=9).rev();
/// let it2 = (6u8..=10).rev();
/// let it3 = (2u8..=4).rev();
/// let res: Vec<_> = subtract_iters_by(it1, vec![it2, it3], |x, y| y.cmp(x)).collect();
///
/// assert_eq!(res, vec![5, 1]);
/// ```
pub fn subtract_iters_by<
    T,
    I: Iterator<Item = T>,
    J: Iterator<Item = T>,
    F: Fn(&T, &T) -> Ordering + Copy,
>(
    mut left_iter: I,
    right_iters: Vec<J>,
    cmp: F,
) -> SubtractIterator<T, I, J, F> {
    let left = left_iter.next();
    let front = Vec::with_capacity(right_iters.len());
    SubtractIterator {
        left_iter,
        right_iters,
        cmp,
        left,
        front,
        all_greater: false,
        collision_index: 0,
        exhausted_indices: Vec::new(),
    }
}

pub struct SubtractIterator<
    T,
    I: Iterator<Item = T>,
    J: Iterator<Item = T>,
    F: Fn(&T, &T) -> Ordering,
> {
    left_iter: I,
    right_iters: Vec<J>,
    cmp: F,
    left: Option<T>,
    front: Vec<T>,
    all_greater: bool,
    collision_index: usize,
    exhausted_indices: Vec<usize>,
}

impl<T, I: Iterator<Item = T>, J: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering> Iterator
    for SubtractIterator<T, I, J, F>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.left.as_ref()?;
        'until_all_greater: while !self.all_greater {
            let index_iter = ((0..=self.collision_index).rev())
                .chain((self.collision_index + 1)..self.right_iters.len());
            for i in index_iter {
                if i >= self.front.len() {
                    if let Some(x) = self.right_iters[i].next() {
                        self.front.push(x);
                    } else {
                        self.exhausted_indices.push(i);
                        continue;
                    }
                }
                let mut ord = (self.cmp)(&self.front[i], self.left.as_ref().unwrap());
                while ord.is_lt() {
                    if let Some(x) = self.right_iters[i].next() {
                        ord = (self.cmp)(&x, self.left.as_ref().unwrap());
                        self.front[i] = x;
                    } else {
                        self.exhausted_indices.push(i);
                        break;
                    }
                }
                if ord.is_eq() {
                    if let Some(x) = self.left_iter.next() {
                        self.left = Some(x);
                        self.collision_index = i;
                        self.exhausted_indices.sort_unstable();
                        for j in self.exhausted_indices.drain(..).rev() {
                            self.front.swap_remove(j);
                            self.right_iters.swap(j, self.front.len());
                            self.right_iters.swap_remove(self.front.len());
                            if self.collision_index == j {
                                self.collision_index = 0;
                            } else if self.collision_index == self.front.len() {
                                self.collision_index = j;
                            }
                        }
                        continue 'until_all_greater;
                    } else {
                        self.left = None;
                        return None;
                    }
                }
            }
            self.exhausted_indices.sort_unstable();
            for j in self.exhausted_indices.drain(..).rev() {
                self.front.swap_remove(j);
                self.right_iters.swap(j, self.front.len());
                self.right_iters.swap_remove(self.front.len());
                if self.collision_index == j {
                    self.collision_index = 0;
                } else if self.collision_index == self.front.len() {
                    self.collision_index = j;
                }
            }
            self.all_greater = true;
        }
        let mut res = self.left_iter.next();
        swap(&mut res, &mut self.left);
        self.all_greater = false;
        res
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, Rng, SeedableRng};
    use std::collections::HashSet;

    #[test]
    fn test_subtract() {
        let it1 = 1u8..=9;
        let it2 = 6u8..=10;
        let it3 = 2u8..=4;
        let res: Vec<_> = subtract_iters(it1, vec![it2, it3]).collect();

        assert_eq!(res, vec![1, 5]);
    }

    #[test]
    fn test_subtract_by() {
        let it1 = (1u8..=9).rev();
        let it2 = (6u8..=10).rev();
        let it3 = (2u8..=4).rev();
        let res: Vec<_> = subtract_iters_by(it1, vec![it2, it3], |x, y| y.cmp(x)).collect();

        assert_eq!(res, vec![5, 1]);
    }

    #[test]
    fn test_large_subtract() {
        const C: usize = 10;
        const N: usize = 100_000;

        let left_iter = (0..=(C * N)).step_by(C);
        let right_iters: Vec<_> = (0..C).map(|i| (0..(C * N)).skip(i).step_by(C)).collect();
        let res: Vec<_> = subtract_iters(left_iter, right_iters).collect();

        assert_eq!(res, vec![C * N]);
    }

    #[test]
    fn test_random_subtract() {
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
        let left_iter = vecs[0].iter();
        let right_iters: Vec<_> = vecs.iter().skip(1).map(|v| v.iter()).collect();
        let res: HashSet<_> = subtract_iters(left_iter, right_iters).collect();

        for &x in res.iter() {
            assert!(vecs[0].contains(x));
        }
        for vec in vecs.iter().skip(1) {
            for x in vec {
                assert!(!res.contains(x));
            }
        }
    }
}
