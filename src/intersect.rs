use core::cmp::Ordering;
use core::mem::swap;

/// Iterates over the intersection of many sorted deduplicated iterators.
///
/// # Examples
///
/// ```
/// use iter_set_ops::intersect_iters;
///
/// let it1 = 1u8..=5;
/// let it2 = 3u8..=7;
/// let it3 = 2u8..=4;
/// let mut iters = [it1, it2, it3];
/// let res: Vec<_> = intersect_iters(&mut iters).collect();
///
/// assert_eq!(res, vec![3, 4]);
/// ```
#[inline]
pub fn intersect_iters<'a, T: Ord + 'a, I: Iterator<Item = T>>(
    iters: &mut [I],
) -> IntersectIterator<T, I, impl Fn(&T, &T) -> Ordering + 'a> {
    intersect_iters_by(iters, T::cmp)
}

/// Iterates over the intersection of many sorted deduplicated iterators, using `cmp` as the comparison operator.
///
/// # Examples
///
/// ```
/// use iter_set_ops::intersect_iters_by;
///
/// let it1 = (1u8..=5).rev();
/// let it2 = (3u8..=7).rev();
/// let it3 = (2u8..=4).rev();
/// let mut iters = [it1, it2, it3];
/// let res: Vec<_> = intersect_iters_by(&mut iters, |x, y| y.cmp(x)).collect();
///
/// assert_eq!(res, vec![4, 3]);
/// ```
pub fn intersect_iters_by<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering + Copy + 'a>(
    iters: &mut [I],
    cmp: F,
) -> IntersectIterator<T, I, F> {
    let mut front: Vec<T> = Vec::with_capacity(iters.len());
    let mut max_index = 0;
    let mut nonmax_index = 0;
    let mut all_equal = true;
    if iters.is_empty() {
        return IntersectIterator {
            iters,
            cmp,
            front,
            max_index,
            nonmax_index,
            all_equal,
            exhausted: true,
        };
    }
    if let Some(x) = iters[0].next() {
        front.push(x);
    } else {
        return IntersectIterator {
            iters,
            cmp,
            front,
            max_index,
            nonmax_index,
            all_equal,
            exhausted: true,
        };
    }
    for (i, iter) in iters.iter_mut().enumerate().skip(1) {
        if let Some(x) = iter.next() {
            front.push(x);
            match cmp(&front[i], &front[max_index]) {
                Ordering::Less => {
                    nonmax_index = i;
                    all_equal = false;
                    break;
                }
                Ordering::Greater => {
                    nonmax_index = max_index;
                    max_index = i;
                    all_equal = false;
                    break;
                }
                _ => (),
            }
        } else {
            return IntersectIterator {
                iters,
                cmp,
                front,
                max_index,
                nonmax_index,
                all_equal,
                exhausted: true,
            };
        }
    }
    IntersectIterator {
        iters,
        cmp,
        front,
        max_index,
        nonmax_index,
        all_equal,
        exhausted: false,
    }
}

pub struct IntersectIterator<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering> {
    iters: &'a mut [I],
    cmp: F,
    front: Vec<T>,
    max_index: usize,
    nonmax_index: usize,
    all_equal: bool,
    exhausted: bool,
}

impl<T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering> Iterator
    for IntersectIterator<'_, T, I, F>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }
        'until_all_equal: while !self.all_equal {
            let index_iter = ((0..=self.nonmax_index).rev())
                .chain((self.nonmax_index + 1)..self.iters.len())
                .filter(|&i| i != self.max_index);
            for i in index_iter {
                if i >= self.front.len() {
                    if let Some(x) = self.iters[i].next() {
                        self.front.push(x);
                    } else {
                        self.exhausted = true;
                        return None;
                    }
                }
                let mut ord = (self.cmp)(&self.front[i], &self.front[self.max_index]);
                while ord.is_lt() {
                    if let Some(x) = self.iters[i].next() {
                        ord = (self.cmp)(&x, &self.front[self.max_index]);
                        self.front[i] = x;
                    } else {
                        self.exhausted = true;
                        return None;
                    }
                }
                if ord.is_gt() {
                    self.nonmax_index = self.max_index;
                    self.max_index = i;
                    continue 'until_all_equal;
                }
            }
            self.all_equal = true;
        }
        let res = if let Some(mut x) = self.iters[self.max_index].next() {
            swap(&mut x, &mut self.front[self.max_index]);
            x
        } else {
            self.exhausted = true;
            return Some(self.front.swap_remove(self.max_index));
        };
        let index_iter = ((0..=self.nonmax_index).rev())
            .chain((self.nonmax_index + 1)..self.iters.len())
            .filter(|&i| i != self.max_index);
        for i in index_iter {
            if let Some(x) = self.iters[i].next() {
                self.front[i] = x;
                match (self.cmp)(&self.front[i], &self.front[self.max_index]) {
                    Ordering::Less => {
                        self.nonmax_index = i;
                        self.all_equal = false;
                        break;
                    }
                    Ordering::Greater => {
                        self.nonmax_index = self.max_index;
                        self.max_index = i;
                        self.all_equal = false;
                        break;
                    }
                    _ => (),
                }
            } else {
                self.exhausted = true;
                break;
            }
        }
        Some(res)
    }
}

/// Iterates over the intersection of many sorted deduplicated iterators and groups equal items into a [`Vec`].
///
/// # Examples
///
/// ```
/// use iter_set_ops::intersect_iters_detailed;
///
/// let it1 = 1u8..=5;
/// let it2 = 3u8..=7;
/// let it3 = 2u8..=4;
/// let mut iters = [it1, it2, it3];
/// let res: Vec<_> = intersect_iters_detailed(&mut iters).collect();
///
/// assert_eq!(res, vec![vec![3, 3, 3], vec![4, 4, 4]]);
/// ```
#[inline]
pub fn intersect_iters_detailed<'a, T: Ord + 'a, I: Iterator<Item = T>>(
    iters: &mut [I],
) -> DetailedIntersectIterator<T, I, impl Fn(&T, &T) -> Ordering + 'a> {
    intersect_iters_detailed_by(iters, T::cmp)
}

/// Iterates over the intersection of many sorted deduplicated iterators and groups equal items into a [`Vec`], using `cmp` as the comparison operator.
///
/// # Examples
///
/// ```
/// use iter_set_ops::intersect_iters_detailed_by;
///
/// let it1 = (1u8..=5).rev();
/// let it2 = (3u8..=7).rev();
/// let it3 = (2u8..=4).rev();
/// let mut iters = [it1, it2, it3];
/// let res: Vec<_> = intersect_iters_detailed_by(&mut iters, |x, y| y.cmp(x)).collect();
///
/// assert_eq!(res, vec![vec![4, 4, 4], vec![3, 3, 3]]);
/// ```
pub fn intersect_iters_detailed_by<
    'a,
    T,
    I: Iterator<Item = T>,
    F: Fn(&T, &T) -> Ordering + Copy + 'a,
>(
    iters: &mut [I],
    cmp: F,
) -> DetailedIntersectIterator<T, I, F> {
    let mut front: Vec<T> = Vec::with_capacity(iters.len());
    let mut max_index = 0;
    let mut nonmax_index = 0;
    let mut all_equal = true;
    if iters.is_empty() {
        return DetailedIntersectIterator {
            iters,
            cmp,
            front,
            max_index,
            nonmax_index,
            all_equal,
            exhausted: true,
        };
    }
    if let Some(x) = iters[0].next() {
        front.push(x);
    } else {
        return DetailedIntersectIterator {
            iters,
            cmp,
            front,
            max_index,
            nonmax_index,
            all_equal,
            exhausted: true,
        };
    }
    for (i, iter) in iters.iter_mut().enumerate().skip(1) {
        if let Some(x) = iter.next() {
            front.push(x);
            match cmp(&front[i], &front[max_index]) {
                Ordering::Less => {
                    nonmax_index = i;
                    all_equal = false;
                    break;
                }
                Ordering::Greater => {
                    nonmax_index = max_index;
                    max_index = i;
                    all_equal = false;
                    break;
                }
                _ => (),
            }
        } else {
            return DetailedIntersectIterator {
                iters,
                cmp,
                front,
                max_index,
                nonmax_index,
                all_equal,
                exhausted: true,
            };
        }
    }
    DetailedIntersectIterator {
        iters,
        cmp,
        front,
        max_index,
        nonmax_index,
        all_equal,
        exhausted: false,
    }
}

pub struct DetailedIntersectIterator<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering> {
    iters: &'a mut [I],
    cmp: F,
    front: Vec<T>,
    max_index: usize,
    nonmax_index: usize,
    all_equal: bool,
    exhausted: bool,
}

impl<T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering> Iterator
    for DetailedIntersectIterator<'_, T, I, F>
{
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }
        'until_all_equal: while !self.all_equal {
            let index_iter = ((0..=self.nonmax_index).rev())
                .chain((self.nonmax_index + 1)..self.iters.len())
                .filter(|&i| i != self.max_index);
            for i in index_iter {
                if i >= self.front.len() {
                    if let Some(x) = self.iters[i].next() {
                        self.front.push(x);
                    } else {
                        self.exhausted = true;
                        return None;
                    }
                }
                let mut ord = (self.cmp)(&self.front[i], &self.front[self.max_index]);
                while ord.is_lt() {
                    if let Some(x) = self.iters[i].next() {
                        ord = (self.cmp)(&x, &self.front[self.max_index]);
                        self.front[i] = x;
                    } else {
                        self.exhausted = true;
                        return None;
                    }
                }
                if ord.is_gt() {
                    self.nonmax_index = self.max_index;
                    self.max_index = i;
                    continue 'until_all_equal;
                }
            }
            self.all_equal = true;
        }
        self.max_index = 0;
        self.nonmax_index = 0;
        let mut res = Vec::with_capacity(self.front.len());
        for (i, iter) in self.iters.iter_mut().enumerate().rev() {
            if let Some(mut x) = iter.next() {
                swap(&mut x, &mut self.front[i]);
                res.push(x);
                if !self.exhausted {
                    match (self.cmp)(&self.front[i], &self.front[self.max_index]) {
                        Ordering::Less => {
                            self.nonmax_index = i;
                            self.all_equal = false;
                        }
                        Ordering::Greater => {
                            self.nonmax_index = self.max_index;
                            self.max_index = i;
                            self.all_equal = false;
                        }
                        _ => (),
                    }
                }
            } else {
                self.exhausted = true;
                res.push(self.front.swap_remove(i));
            }
        }
        res.reverse();
        Some(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, Rng, SeedableRng};
    use std::collections::HashSet;

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
    fn test_intersect_pair() {
        let it1 = 3u8..=7;
        let it2 = 2u8..=4;
        let mut iters = [it1, it2];
        let res: Vec<_> = intersect_iters(&mut iters).collect();

        assert_eq!(res, vec![3, 4]);
        assert!(iters[0].next().is_some());
    }

    #[test]
    fn test_intersect_by() {
        let it1 = (1u8..=5).rev();
        let it2 = (3u8..=7).rev();
        let it3 = (2u8..=4).rev();
        let mut iters = [it1, it2, it3];
        let res: Vec<_> = intersect_iters_by(&mut iters, |x, y| y.cmp(x)).collect();

        assert_eq!(res, vec![4, 3]);
        assert!(iters[0].next().is_some());
    }

    #[test]
    fn test_intersect_detailed() {
        let it1 = 1u8..=5;
        let it2 = 3u8..=7;
        let it3 = 2u8..=4;
        let mut iters = [it1, it2, it3];
        let res: Vec<_> = intersect_iters_detailed(&mut iters).collect();

        assert_eq!(res, vec![vec![3, 3, 3], vec![4, 4, 4]]);
        assert!(iters[1].next().is_some());
    }

    #[test]
    fn test_intersect_detailed_by() {
        let it1 = (1u8..=5).rev();
        let it2 = (3u8..=7).rev();
        let it3 = (2u8..=4).rev();
        let mut iters = [it1, it2, it3];
        let res: Vec<_> = intersect_iters_detailed_by(&mut iters, |x, y| y.cmp(x)).collect();

        assert_eq!(res, vec![vec![4, 4, 4], vec![3, 3, 3]]);
        assert!(iters[0].next().is_some());
    }

    #[test]
    fn test_random_intersect() {
        const C: usize = 5;
        const N: usize = 100_000;

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
        let res: HashSet<_> = intersect_iters(&mut iters).collect();
        let sets: Vec<HashSet<u16>> = vecs
            .iter()
            .map(|vec| vec.iter().copied().collect())
            .collect();

        for x in res {
            for set in sets.iter() {
                assert!(set.contains(x));
            }
        }
    }

    #[test]
    fn test_intersect_preserve_details() {
        const C: usize = 5;
        const N: usize = 100_000;

        let mut rng = StdRng::seed_from_u64(42);
        let mut vecs = Vec::with_capacity(C);
        for i in 0..C {
            let mut vec = Vec::with_capacity(N);
            for _ in 0..N {
                vec.push((i, rng.gen::<u16>()));
            }
            vec.sort_unstable();
            vec.dedup();
            vecs.push(vec);
        }
        let mut iters: Vec<_> = vecs.iter().map(|v| v.iter()).collect();
        for details in intersect_iters_detailed_by(&mut iters, |(_, x), (_, y)| x.cmp(y)) {
            let x = details[0].1;
            for (i, &&(j, y)) in details.iter().enumerate() {
                assert_eq!(x, y);
                assert_eq!(i, j);
            }
        }
    }

    #[test]
    fn test_associative_intersect() {
        const C: usize = 6;
        const N: usize = 100_000;

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
        let res6: HashSet<_> = intersect_iters(&mut iters).collect();

        let mut nested_iters: Vec<Vec<_>> = (0..C)
            .step_by(3)
            .map(|i| vecs.iter().skip(i).take(3).map(|v| v.iter()).collect())
            .collect();
        let res3: HashSet<_> = intersect_iters(
            &mut nested_iters
                .iter_mut()
                .map(|inner_iters| intersect_iters(inner_iters))
                .collect::<Vec<_>>(),
        )
        .collect();

        let mut nested_iters: Vec<Vec<_>> = (0..C)
            .step_by(2)
            .map(|i| vecs.iter().skip(i).take(2).map(|v| v.iter()).collect())
            .collect();
        let res2: HashSet<_> = intersect_iters(
            &mut nested_iters
                .iter_mut()
                .map(|inner_iters| intersect_iters(inner_iters))
                .collect::<Vec<_>>(),
        )
        .collect();

        assert_eq!(res6, res3);
        assert_eq!(res6, res2);
    }
}
