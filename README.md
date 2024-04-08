# split_array

Split array references in two with compile-time size validation.

## This crate requires nightly!

Unstable features used:

- [`#![feature(generic_const_exprs)]`](https://github.com/rust-lang/rust/issues/76560)

# Examples

The sizes of the two halves can usually be inferred:

```rust
use split_array::SplitArray;
let mut array: [usize; 5] = [0, 1, 2, 3, 4];
let (left, right) = array.split_arr_mut();
* left = [10, 11, 12];
* right = [23, 24];
assert_eq!([10, 11, 12, 23, 24], array);
```

They can be annotated explicitly as well:

```rust
use split_array::SplitArray;
let array: [usize; 5] = [0, 1, 2, 3, 4];
let (left, right) = array.split_arr::<2 > ();
assert_eq!([0, 1, 2], *left);
assert_eq!([3, 4], *right);
```

The annotated size is validated at compile-time. This won't compile:

```rust
use split_array::SplitArray;
let array: [usize; 5] = [0, 1, 2, 3, 4];
let (left, right) = array.split_arr::<6 > ();
```