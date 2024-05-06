# iter-set-ops

[![crates.io](https://img.shields.io/crates/v/iter-set-ops)](https://crates.io/crates/iter-set-ops)
[![docs](https://img.shields.io/docsrs/iter-set-ops)](https://docs.rs/iter-set-ops)

Fast set operations on an arbitrary number of sorted deduplicated iterators.

## Features

- set operations for an arbitrary number of sets
- zero copy: each item is reused from its iterator, no copy is made
- custom comparison operator with `merge_iters_by` / `intersect_iters_by`
- lazy intersection: the computation stops as soon as one of the sets is exhausted
