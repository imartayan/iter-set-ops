# iter-set-ops

[![crates.io](https://img.shields.io/crates/v/iter-set-ops)](https://crates.io/crates/iter-set-ops)
[![docs](https://img.shields.io/docsrs/iter-set-ops)](https://docs.rs/iter-set-ops)

Fast set operations on an arbitrary number of sorted deduplicated iterators.

## Features

- set operations for an arbitrary number of sets
- zero copy: each item is reused from its iterator, no copy is made
- custom comparison operator with `merge_iters_by` / `intersect_iters_by`
- lazy intersection: the computation stops as soon as one of the sets is exhausted

## Example usage

```rust
use iter_set_ops::*;

let it1 = 1u8..=5;
let it2 = 3u8..=7;
let it3 = 2u8..=4;
let mut iters = [it1, it2, it3];

// intersect it1, it2 and it3
let res: Vec<_> = intersect_iters(&mut iters).collect();
assert_eq!(res, vec![3, 4]);

// the computation stops before exhausting all the iterators
assert!(iters[1].next().is_some());
```

```rust
use iter_set_ops::*;

let it1 = 1u8..=2;
let it2 = 2u8..=3;
let mut iters = [it1, it2];

// merge it1 and it2 while keeping the details of each item
let res: Vec<_> = merge_iters_detailed(&mut iters).collect();
assert_eq!(
    res,
    vec![
        vec![Some(1), None], // `1` comes from it1
        vec![Some(2), Some(2)], // `2` comes from both
        vec![None, Some(3)] // `3` comes from it2
    ]
);
```
