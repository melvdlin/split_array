//! Split array references in two with compile-time size validation.
//!
//! # Examples
//!
//! The sizes of the two halves can usually be inferred:
//! ```rust
//! use split_array::SplitArray;
//!
//! let mut array: [usize; 5] = [0, 1, 2, 3, 4];
//! let (left, right) = array.split_arr_mut();
//! *left = [10, 11, 12];
//! *right = [23, 24];
//! assert_eq!([10, 11, 12, 23, 24], array);
//! ```
//!
//! They can be annotated explicitly as well:
//! ```rust
//! use split_array::SplitArray;
//!
//! let array: [usize; 5] = [0, 1, 2, 3, 4];
//! let (left, right) = array.split_arr::<2>();
//! assert_eq!([0, 1, 2], *left);
//! assert_eq!([3, 4], *right);
//! ```
//!
//! The annotated size is validated at compile-time. This won't compile:
//! ```rust
//! use split_array::SplitArray;
//!
//! let array: [usize; 5] = [0, 1, 2, 3, 4];
//! let (left, right) = array.split_arr::<6>();
//! ```

#![no_std]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use bool_traits::True;

/// Split array references in two with compile-time size validation.
pub trait SplitArray<const LEN: usize> {
    /// The result of a split.
    type Output<const OUT_SIZE: usize>: SplitArray<OUT_SIZE>;

    /// Split an array reference
    /// into a reference to the left half and a reference to the right half.
    /// The sizes of the halves are validated at compile time.
    fn split_arr<const LEFT: usize>(&self) -> (&Self::Output<LEFT>, &Self::Output<{ LEN - LEFT }>)
    where
        (): True<{ LEFT <= LEN }>;

    /// Mutable version of [`Self::split_arr`]
    fn split_arr_mut<const LEFT: usize>(
        &mut self,
    ) -> (&mut Self::Output<LEFT>, &mut Self::Output<{ LEN - LEFT }>)
    where
        (): True<{ LEFT <= LEN }>;
}

/// Raw version of [`SplitArray`].
pub trait SplitArrayRaw<const LEN: usize> {
    /// The result of a split.
    type Output<const OUT_SIZE: usize>: SplitArrayRaw<OUT_SIZE>;

    /// Split an array pointer
    /// into a pointer to the left half and a pointer to the right half.
    /// The sizes of the halves are validated at compile time.
    ///
    /// # Safety
    /// `self` must be valid.
    unsafe fn split_arr_raw<const LEFT: usize>(
        self,
    ) -> (Self::Output<LEFT>, Self::Output<{ LEN - LEFT }>)
    where
        (): True<{ LEFT <= LEN }>;
}

/// Raw mutable version of [`SplitArray`].
pub trait SplitArrayRawMut<const LEN: usize> {
    type Output<const OUT_SIZE: usize>: SplitArrayRawMut<OUT_SIZE>;

    /// Split an array pointer
    /// into a pointer to the left half and a pointer to the right half.
    /// The sizes of the halves are validated at compile time.
    ///
    /// # Safety
    /// `self` must be valid.
    unsafe fn split_arr_raw_mut<const LEFT: usize>(
        self,
    ) -> (Self::Output<LEFT>, Self::Output<{ LEN - LEFT }>)
    where
        (): True<{ LEFT <= LEN }>;
}

impl<T, const LEN: usize> SplitArray<LEN> for [T; LEN] {
    type Output<const OUT_SIZE: usize> = [T; OUT_SIZE];

    #[inline]
    fn split_arr<const LEFT: usize>(&self) -> (&[T; LEFT], &[T; LEN - LEFT])
    where
        (): True<{ LEFT <= LEN }>,
    {
        split_arr(self)
    }

    #[inline]
    fn split_arr_mut<const LEFT: usize>(&mut self) -> (&mut [T; LEFT], &mut [T; LEN - LEFT])
    where
        (): True<{ LEFT <= LEN }>,
    {
        split_arr_mut(self)
    }
}

impl<T, const LEN: usize> SplitArrayRaw<LEN> for *const [T; LEN] {
    type Output<const OUT_SIZE: usize> = *const [T; OUT_SIZE];

    unsafe fn split_arr_raw<const LEFT: usize>(self) -> (*const [T; LEFT], *const [T; LEN - LEFT])
    where
        (): True<{ LEFT <= LEN }>,
    {
        unsafe { split_arr_raw(self) }
    }
}

impl<T, const LEN: usize> SplitArrayRawMut<LEN> for *mut [T; LEN] {
    type Output<const OUT_SIZE: usize> = *mut [T; OUT_SIZE];

    unsafe fn split_arr_raw_mut<const LEFT: usize>(self) -> (*mut [T; LEFT], *mut [T; LEN - LEFT])
    where
        (): True<{ LEFT <= LEN }>,
    {
        unsafe { split_arr_raw_mut(self) }
    }
}

/// Split an array reference
/// into a reference to the left half and a reference to the right half.
/// The sizes of the halves are validated at compile time.
#[inline]
pub const fn split_arr<const LEFT: usize, const N: usize, T>(
    arr: &[T; N],
) -> (&[T; LEFT], &[T; N - LEFT])
where
    (): True<{ LEFT <= N }>,
{
    unsafe {
        let (left, right) = split_arr_raw(arr);
        (&*left, &*right)
    }
}

/// Mutable version of [`split_arr`].
#[inline]
pub fn split_arr_mut<const LEFT: usize, const N: usize, T>(
    arr: &mut [T; N],
) -> (&mut [T; LEFT], &mut [T; N - LEFT])
where
    (): True<{ LEFT <= N }>,
{
    unsafe {
        let (left, right) = split_arr_raw_mut(arr);
        (&mut *left, &mut *right)
    }
}

/// Raw version of [`split_arr`].
///
/// # Safety
/// `arr` must be valid.
#[inline]
pub const unsafe fn split_arr_raw<const LEFT: usize, const N: usize, T>(
    arr: *const [T; N],
) -> (*const [T; LEFT], *const [T; N - LEFT])
where
    (): True<{ LEFT <= N }>,
{
    let left = arr.cast::<T>();
    let right = unsafe { left.add(LEFT) };

    (left.cast(), right.cast())
}

/// Raw version of [`split_arr_mut`].
///
/// # Safety
/// `arr` must be valid.
#[inline]
pub const unsafe fn split_arr_raw_mut<const LEFT: usize, const N: usize, T>(
    arr: *mut [T; N],
) -> (*mut [T; LEFT], *mut [T; N - LEFT])
where
    (): True<{ LEFT <= N }>,
{
    let left = arr as *mut T;
    let right = unsafe { left.add(LEFT) };

    (left.cast(), right.cast())
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::ptr::{addr_of, addr_of_mut};

    #[test]
    fn split_arr() {
        let arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let (left, right) = arr.split_arr::<5>();

        assert_eq!(&[0, 1, 2, 3, 4], left);
        assert_eq!(&[5, 6, 7], right);
    }

    #[test]
    fn split_arr_infer_size() {
        let arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let (left, right) = arr.split_arr();

        assert_eq!(&[0, 1, 2, 3, 4], left);
        assert_eq!(&[5, 6, 7], right);
    }

    #[test]
    fn split_arr_left_zero() {
        let arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let (left, right) = arr.split_arr::<0>();

        assert_eq!(&[0; 0], left);
        assert_eq!(&[0, 1, 2, 3, 4, 5, 6, 7], right);
    }

    #[test]
    fn split_arr_right_zero() {
        let arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let (left, right) = arr.split_arr::<8>();

        assert_eq!(&[0, 1, 2, 3, 4, 5, 6, 7], left);
        assert_eq!(&[0; 0], right);
    }

    #[test]
    fn split_arr_mut() {
        let mut arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let (left, right) = arr.split_arr_mut::<5>();
        left.clone_from(&[10, 11, 12, 13, 14]);
        right.clone_from(&[25, 26, 27]);

        assert_eq!(&[10, 11, 12, 13, 14], left);
        assert_eq!(&[25, 26, 27], right);
        assert_eq!([10, 11, 12, 13, 14, 25, 26, 27], arr);
    }

    #[test]
    fn split_arr_mut_infer_size() {
        let mut arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let (left, right) = arr.split_arr_mut();
        left.clone_from(&[10, 11, 12, 13, 14]);
        right.clone_from(&[25, 26, 27]);

        assert_eq!(&[10, 11, 12, 13, 14], left);
        assert_eq!(&[25, 26, 27], right);
        assert_eq!([10, 11, 12, 13, 14, 25, 26, 27], arr);
    }

    #[test]
    fn split_arr_mut_left_zero() {
        let mut arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let (left, right) = arr.split_arr_mut::<0>();
        left.clone_from(&[]);
        right.clone_from(&[20, 21, 22, 23, 24, 25, 26, 27]);

        assert_eq!(&[0; 0], left);
        assert_eq!(&[20, 21, 22, 23, 24, 25, 26, 27], right);
        assert_eq!([20, 21, 22, 23, 24, 25, 26, 27], arr);
    }

    #[test]
    fn split_arr_mut_right_zero() {
        let mut arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let (left, right) = arr.split_arr_mut::<8>();
        left.clone_from(&[10, 11, 12, 13, 14, 15, 16, 17]);
        right.clone_from(&[]);

        assert_eq!(&[10, 11, 12, 13, 14, 15, 16, 17], left);
        assert_eq!(&[0; 0], right);
        assert_eq!([10, 11, 12, 13, 14, 15, 16, 17], arr);
    }

    #[test]
    fn split_arr_raw() {
        let arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];

        unsafe {
            let (left, right) = addr_of!(arr).split_arr_raw::<5>();

            assert_eq!([0, 1, 2, 3, 4], *left);
            assert_eq!([5, 6, 7], *right);
        }
    }

    #[test]
    fn split_arr_raw_infer_size() {
        let arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];

        unsafe {
            let (left, right) = addr_of!(arr).split_arr_raw();

            assert_eq!([0, 1, 2, 3, 4], *left);
            assert_eq!([5, 6, 7], *right);
        }
    }

    #[test]
    fn split_arr_raw_left_zero() {
        let arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];

        unsafe {
            let (left, right) = addr_of!(arr).split_arr_raw::<0>();

            assert_eq!([0; 0], *left);
            assert_eq!([0, 1, 2, 3, 4, 5, 6, 7], *right);
        }
    }

    #[test]
    fn split_arr_raw_right_zero() {
        let arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];

        unsafe {
            let (left, right) = addr_of!(arr).split_arr_raw::<8>();

            assert_eq!([0, 1, 2, 3, 4, 5, 6, 7], *left);
            assert_eq!([0; 0], *right);
        }
    }

    #[test]
    fn split_arr_raw_mut() {
        let mut arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];

        unsafe {
            let (left, right) = addr_of_mut!(arr).split_arr_raw_mut::<5>();
            *left = [10, 11, 12, 13, 14];
            *right = [25, 26, 27];

            assert_eq!([10, 11, 12, 13, 14], *left);
            assert_eq!([25, 26, 27], *right);
        }

        assert_eq!([10, 11, 12, 13, 14, 25, 26, 27], arr);
    }

    #[test]
    fn split_arr_raw_mut_infer_size() {
        let mut arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];

        unsafe {
            let (left, right) = addr_of_mut!(arr).split_arr_raw_mut();
            *left = [10, 11, 12, 13, 14];
            *right = [25, 26, 27];

            assert_eq!([10, 11, 12, 13, 14], *left);
            assert_eq!([25, 26, 27], *right);
        }

        assert_eq!([10, 11, 12, 13, 14, 25, 26, 27], arr);
    }

    #[test]
    fn split_arr_raw_mut_left_zero() {
        let mut arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];

        unsafe {
            let (left, right) = addr_of_mut!(arr).split_arr_raw_mut::<0>();
            *left = [];
            *right = [20, 21, 22, 23, 24, 25, 26, 27];

            assert_eq!([0; 0], *left);
            assert_eq!([20, 21, 22, 23, 24, 25, 26, 27], *right);
        }

        assert_eq!([20, 21, 22, 23, 24, 25, 26, 27], arr);
    }

    #[test]
    fn split_arr_raw_mut_right_zero() {
        let mut arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];

        unsafe {
            let (left, right) = addr_of_mut!(arr).split_arr_raw_mut::<8>();
            *left = [10, 11, 12, 13, 14, 15, 16, 17];
            *right = [];

            assert_eq!([10, 11, 12, 13, 14, 15, 16, 17], *left);
            assert_eq!([0; 0], *right);
        }

        assert_eq!([10, 11, 12, 13, 14, 15, 16, 17], arr);
    }

    #[test]
    fn array_impl_defers() {
        let arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        assert_eq!(crate::split_arr(&arr), arr.split_arr::<5>());
    }

    #[test]
    fn array_impl_defers_mut() {
        let mut arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let (crate_level_left, crate_level_right) = crate::split_arr_mut(&mut arr);
        let crate_level_result = (crate_level_left as *mut _, crate_level_right as *mut _);
        let (trait_left, trait_right) = arr.split_arr_mut::<5>();
        let trait_result = (trait_left as *mut _, trait_right as *mut _);
        assert_eq!(crate_level_result, trait_result);
    }

    #[test]
    fn array_impl_defers_raw() {
        let arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        unsafe {
            assert_eq!(
                crate::split_arr_raw(addr_of!(arr)),
                addr_of!(arr).split_arr_raw::<5>()
            );
        }
    }

    #[test]
    fn array_impl_defers_raw_mut() {
        let mut arr: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        unsafe {
            assert_eq!(
                crate::split_arr_raw_mut(addr_of_mut!(arr)),
                addr_of_mut!(arr).split_arr_raw_mut::<5>()
            );
        }
    }
}
