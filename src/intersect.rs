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
    if iters.is_empty() {
        return IntersectIterator {
            iters,
            cmp,
            front,
            max_index,
            nonmax_index,
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
            exhausted: true,
        };
    }
    for (i, iter) in iters.iter_mut().enumerate().skip(1) {
        if let Some(x) = iter.next() {
            front.push(x);
            if cmp(&front[i], &front[max_index]) == Ordering::Greater {
                nonmax_index = max_index;
                max_index = i;
                break;
            }
        } else {
            return IntersectIterator {
                iters,
                cmp,
                front,
                max_index,
                nonmax_index,
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
        exhausted: false,
    }
}

pub struct IntersectIterator<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering> {
    iters: &'a mut [I],
    cmp: F,
    front: Vec<T>,
    max_index: usize,
    nonmax_index: usize,
    exhausted: bool,
}

impl<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering> Iterator
    for IntersectIterator<'a, T, I, F>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }
        let mut cmp = self.max_index.cmp(&self.nonmax_index);
        while cmp != Ordering::Equal {
            let index_iter =
                ((0..=self.nonmax_index).rev()).chain((self.nonmax_index + 1)..self.iters.len());
            for i in index_iter {
                if i == self.max_index {
                    continue;
                }
                if i >= self.front.len() {
                    if let Some(x) = self.iters[i].next() {
                        self.front.push(x);
                    } else {
                        self.exhausted = true;
                        return None;
                    }
                }
                cmp = (self.cmp)(&self.front[i], &self.front[self.max_index]);
                while cmp == Ordering::Less {
                    if let Some(x) = self.iters[i].next() {
                        cmp = (self.cmp)(&x, &self.front[self.max_index]);
                        self.front[i] = x;
                    } else {
                        self.exhausted = true;
                        return None;
                    }
                }
                if cmp == Ordering::Greater {
                    self.nonmax_index = self.max_index;
                    self.max_index = i;
                    break;
                }
            }
        }
        let res = if let Some(mut x) = self.iters[0].next() {
            swap(&mut x, &mut self.front[0]);
            x
        } else {
            self.exhausted = true;
            return Some(self.front.swap_remove(0));
        };
        self.max_index = 0;
        self.nonmax_index = 0;
        for (i, iter) in self.iters.iter_mut().enumerate().skip(1) {
            if let Some(x) = iter.next() {
                self.front[i] = x;
                if (self.cmp)(&self.front[i], &self.front[self.max_index]) == Ordering::Greater {
                    self.nonmax_index = self.max_index;
                    self.max_index = i;
                    break;
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
    if iters.is_empty() {
        return DetailedIntersectIterator {
            iters,
            cmp,
            front,
            max_index,
            nonmax_index,
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
            exhausted: true,
        };
    }
    for (i, iter) in iters.iter_mut().enumerate().skip(1) {
        if let Some(x) = iter.next() {
            front.push(x);
            if cmp(&front[i], &front[max_index]) == Ordering::Greater {
                nonmax_index = max_index;
                max_index = i;
                break;
            }
        } else {
            return DetailedIntersectIterator {
                iters,
                cmp,
                front,
                max_index,
                nonmax_index,
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
        exhausted: false,
    }
}

pub struct DetailedIntersectIterator<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering> {
    iters: &'a mut [I],
    cmp: F,
    front: Vec<T>,
    max_index: usize,
    nonmax_index: usize,
    exhausted: bool,
}

impl<'a, T, I: Iterator<Item = T>, F: Fn(&T, &T) -> Ordering> Iterator
    for DetailedIntersectIterator<'a, T, I, F>
{
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }
        let mut cmp = self.max_index.cmp(&self.nonmax_index);
        while cmp != Ordering::Equal {
            let index_iter =
                ((0..=self.nonmax_index).rev()).chain((self.nonmax_index + 1)..self.iters.len());
            for i in index_iter {
                if i == self.max_index {
                    continue;
                }
                if i >= self.front.len() {
                    if let Some(x) = self.iters[i].next() {
                        self.front.push(x);
                    } else {
                        self.exhausted = true;
                        return None;
                    }
                }
                cmp = (self.cmp)(&self.front[i], &self.front[self.max_index]);
                while cmp == Ordering::Less {
                    if let Some(x) = self.iters[i].next() {
                        cmp = (self.cmp)(&x, &self.front[self.max_index]);
                        self.front[i] = x;
                    } else {
                        self.exhausted = true;
                        return None;
                    }
                }
                if cmp == Ordering::Greater {
                    self.nonmax_index = self.max_index;
                    self.max_index = i;
                    break;
                }
            }
        }
        self.max_index = 0;
        self.nonmax_index = 0;
        let mut res = Vec::with_capacity(self.front.len());
        for (i, iter) in self.iters.iter_mut().enumerate().rev() {
            if let Some(mut x) = iter.next() {
                swap(&mut x, &mut self.front[i]);
                res.push(x);
                if !self.exhausted
                    && (self.cmp)(&self.front[i], &self.front[self.max_index]) == Ordering::Greater
                {
                    self.nonmax_index = self.max_index;
                    self.max_index = i;
                }
            } else {
                self.exhausted = true;
                res.push(self.front.swap_remove(i));
            }
        }
        Some(res)
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
}
