/*!
Encoding datatypes as fractional numbers of another datatype
*/
use arrayvec::ArrayVec;

use crate::{
    be_encode_array_i16, be_encode_array_i32, be_encode_array_i64, be_encode_array_u16,
    be_encode_array_u32, be_encode_array_u64,
};
use core::{iter::Empty, marker::PhantomData};

mod ints;

/// A datatype which may be encoded as a fractional number of another datatype
///
/// For example, a `u8` can be viewed as containing half a `u16`, whereas a `u32` contains 2.
/// In general, for a datatype `T` containing `M`/`N + 1` units of `S`, `FractionalEncode` will
/// consume `M` elements of type `T` from the input iterator to yield an element of `S` and an
/// iterator over `N` elements of `S`, making `N + 1` total. This is done to optimize the handling
/// of reciprocals `1/N + 1`.
///
/// This trait encodes integers in *network order*, i.e. in *big-endian* order.
pub trait FractionalEncode<S> {
    /// The type of the iterator over output proquints
    type RestIter: Iterator<Item = S>;

    /// Consume `M` elements of input, yielding `N` elements of output.
    ///
    /// This is returned as a tuple of the first output element and an iterator over
    /// the rest, to optimize the common case where only one output element is returned.
    fn next_digits(iter: impl Iterator<Item = Self>) -> Option<(S, Self::RestIter)>;

    /// Return an empty iterator
    fn empty_rest() -> Self::RestIter;
}

/// A datatype which may be decoded from an iterator of fractional digits
pub trait FractionalDecode<S>: Sized {
    /// Coalesce a value from a stream of digits
    ///
    /// Leaves any unused digits in the iterator
    fn from_digits(iter: impl Iterator<Item = S>) -> Result<Self, FractionalDecodeError>;
}

/// An error trying to decode data from fractional digits
///
/// If the inner integer is `0`, indicates invalid input.
/// If the inner integer is `0 < n < usize::MAX`, indicates that at least `n` elements of additional data were needed.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct FractionalDecodeError(pub usize);

// impl<S> FractionalDecode<S> for S {
//     type Error = FractionalDecodeError;

//     #[cfg_attr(not(tarpaulin), inline(always))]
//     fn from_digits(mut iter: impl Iterator<Item = S>) -> Result<Self, Self::Error> {
//         iter.next().ok_or(FractionalDecodeError(1))
//     }
// }

/// Converts data into a stream of digits
///
/// Uses [`FractionalEncode`] to convert the data into a sequence of big-endian digits
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct FractionalDigits<T, S> {
    /// The input data iterator
    pub input: T,
    output: PhantomData<S>,
}

impl<T, S> FractionalDigits<T, S> {
    /// Iterate over the fractional digits of the input
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn new(input: T) -> FractionalDigits<T, S> {
        FractionalDigits {
            input,
            output: PhantomData,
        }
    }
}

impl<T, S> IntoIterator for FractionalDigits<T, S>
where
    T: IntoIterator,
    T::Item: FractionalEncode<S>,
{
    type Item = S;

    type IntoIter =
        FractionalDigitsIter<T::IntoIter, <T::Item as FractionalEncode<S>>::RestIter, S>;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn into_iter(self) -> Self::IntoIter {
        FractionalDigitsIter {
            input: self.input.into_iter(),
            rest: <T::Item as FractionalEncode<S>>::empty_rest(),
            output: PhantomData,
        }
    }
}

/// Converts an iterator over data into a stream of proquint digits
#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct FractionalDigitsIter<T, R, S> {
    /// The input data iterator
    pub input: T,
    /// An iterator over any digits not yet yielded
    pub rest: R,
    output: PhantomData<S>,
}

impl<T, S> Iterator for FractionalDigitsIter<T, <T::Item as FractionalEncode<S>>::RestIter, S>
where
    T: Iterator,
    T::Item: FractionalEncode<S>,
{
    type Item = S;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.rest.next() {
            return Some(next);
        } else {
            let (digit, rest) = T::Item::next_digits(&mut self.input)?;
            self.rest = rest;
            Some(digit)
        }
    }
}

// impl<'a, T, S> FractionalEncode<S> for &'a T
// where
//     T: Clone,
//     T: FractionalEncode<S>,
// {
//     type RestIter = T::RestIter;

//     #[cfg_attr(not(tarpaulin), inline(always))]
//     fn next_digits(iter: impl Iterator<Item = Self>) -> Option<(S, Self::RestIter)> {
//         T::next_digits(iter.cloned())
//     }

//     #[cfg_attr(not(tarpaulin), inline(always))]
//     fn empty_rest() -> Self::RestIter {
//         T::empty_rest()
//     }
// }

impl<const N: usize, T, S> FractionalEncode<S> for [T; N]
where
    T: FractionalEncode<S>,
{
    type RestIter = <FractionalDigits<arrayvec::IntoIter<T, N>, S> as IntoIterator>::IntoIter;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<(S, Self::RestIter)> {
        let next = ArrayVec::from(iter.next()?);
        let mut digits = FractionalDigits::new(next).into_iter();
        let first = digits.next()?;
        Some((first, digits))
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn empty_rest() -> Self::RestIter {
        FractionalDigits::new(ArrayVec::new()).into_iter()
    }
}

// impl<const N: usize, T, S> FractionalEncode<[S; N]> for T
// where
//     T: FractionalEncode<S>,
// {
//     type RestIter = <FractionalDigits<arrayvec::IntoIter<T, N>, S> as IntoIterator>::IntoIter;

//     #[cfg_attr(not(tarpaulin), inline(always))]
//     fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<(S, Self::RestIter)> {
//         let next = ArrayVec::from(iter.next()?);
//         let mut digits = FractionalDigits::new(next).into_iter();
//         let first = digits.next()?;
//         Some((first, digits))
//     }

//     #[cfg_attr(not(tarpaulin), inline(always))]
//     fn empty_rest() -> Self::RestIter {
//         FractionalDigits::new(ArrayVec::new()).into_iter()
//     }
// }

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;

    macro_rules! int_fractional_roundtrip {
        ($s:ty, $t:ty, $i:expr, $f:expr) => {{
            let mut i = $i.clone();

            let mut tripped =
                Vec::from_iter(FractionalDigits::<_, $s>::new(
                    FractionalDigits::<_, $t>::new(i.clone()),
                ));
            assert_eq!(tripped.len() % $f, 0);
            let diff = $f - (tripped.len() - i.len());
            for _ in 0..diff {
                assert_eq!(tripped.pop(), i.pop());
            }
            while tripped.len() > i.len() {
                assert_eq!(tripped.pop(), Some(0));
            }
            assert_eq!(tripped, i);
        }};
    }

    proptest! {
        #[test]
        fn roundtrip_u8(mut i: Vec<u8>) {
            int_fractional_roundtrip!(u8, u8, i, 1);
            int_fractional_roundtrip!(u8, u16, i, 2);
            int_fractional_roundtrip!(u8, u32, i, 4);
            int_fractional_roundtrip!(u8, u64, i, 8);
            int_fractional_roundtrip!(u8, u128, i, 16);
            int_fractional_roundtrip!(u8, i8, i, 1);
            int_fractional_roundtrip!(u8, i16, i, 2);
            int_fractional_roundtrip!(u8, i32, i, 4);
            int_fractional_roundtrip!(u8, i64, i, 8);
            int_fractional_roundtrip!(u8, i128, i, 16);
        }

        #[test]
        fn roundtrip_u16(mut i: Vec<u16>) {
            int_fractional_roundtrip!(u16, u8, i, 1);
            int_fractional_roundtrip!(u16, u16, i, 1);
            int_fractional_roundtrip!(u16, u32, i, 2);
            int_fractional_roundtrip!(u16, u64, i, 4);
            int_fractional_roundtrip!(u16, u128, i, 8);
            int_fractional_roundtrip!(u16, i8, i, 1);
            int_fractional_roundtrip!(u16, i16, i, 1);
            int_fractional_roundtrip!(u16, i32, i, 2);
            int_fractional_roundtrip!(u16, i64, i, 4);
            int_fractional_roundtrip!(u16, i128, i, 8);
        }

        #[test]
        fn roundtrip_u32(mut i: Vec<u32>) {
            int_fractional_roundtrip!(u32, u8, i, 1);
            int_fractional_roundtrip!(u32, u16, i, 1);
            int_fractional_roundtrip!(u32, u32, i, 1);
            int_fractional_roundtrip!(u32, u64, i, 2);
            int_fractional_roundtrip!(u32, u128, i, 4);
            int_fractional_roundtrip!(u32, i8, i, 1);
            int_fractional_roundtrip!(u32, i16, i, 1);
            int_fractional_roundtrip!(u32, i32, i, 1);
            int_fractional_roundtrip!(u32, i64, i, 2);
            int_fractional_roundtrip!(u32, i128, i, 4);
        }

        #[test]
        fn roundtrip_u64(mut i: Vec<u64>) {
            int_fractional_roundtrip!(u64, u8, i, 1);
            int_fractional_roundtrip!(u64, u16, i, 1);
            int_fractional_roundtrip!(u64, u32, i, 1);
            int_fractional_roundtrip!(u64, u64, i, 1);
            int_fractional_roundtrip!(u64, u128, i, 2);
            int_fractional_roundtrip!(u64, i8, i, 1);
            int_fractional_roundtrip!(u64, i16, i, 1);
            int_fractional_roundtrip!(u64, i32, i, 1);
            int_fractional_roundtrip!(u64, i64, i, 1);
            int_fractional_roundtrip!(u64, i128, i, 2);
        }

        #[test]
        fn roundtrip_u128(mut i: Vec<u128>) {
            int_fractional_roundtrip!(u128, u8, i, 1);
            int_fractional_roundtrip!(u128, u16, i, 1);
            int_fractional_roundtrip!(u128, u32, i, 1);
            int_fractional_roundtrip!(u128, u64, i, 1);
            int_fractional_roundtrip!(u128, u128, i, 1);
            int_fractional_roundtrip!(u128, i8, i, 1);
            int_fractional_roundtrip!(u128, i16, i, 1);
            int_fractional_roundtrip!(u128, i32, i, 1);
            int_fractional_roundtrip!(u128, i64, i, 1);
            int_fractional_roundtrip!(u128, i128, i, 1);
        }

        #[test]
        fn roundtrip_i8(mut i: Vec<i8>) {
            int_fractional_roundtrip!(i8, u8, i, 1);
            int_fractional_roundtrip!(i8, u16, i, 2);
            int_fractional_roundtrip!(i8, u32, i, 4);
            int_fractional_roundtrip!(i8, u64, i, 8);
            int_fractional_roundtrip!(i8, u128, i, 16);
            int_fractional_roundtrip!(i8, i8, i, 1);
            int_fractional_roundtrip!(i8, i16, i, 2);
            int_fractional_roundtrip!(i8, i32, i, 4);
            int_fractional_roundtrip!(i8, i64, i, 8);
            int_fractional_roundtrip!(i8, i128, i, 16);
        }

        #[test]
        fn roundtrip_i16(mut i: Vec<i16>) {
            int_fractional_roundtrip!(i16, u8, i, 1);
            int_fractional_roundtrip!(i16, u16, i, 1);
            int_fractional_roundtrip!(i16, u32, i, 2);
            int_fractional_roundtrip!(i16, u64, i, 4);
            int_fractional_roundtrip!(i16, u128, i, 8);
            int_fractional_roundtrip!(i16, i8, i, 1);
            int_fractional_roundtrip!(i16, i16, i, 1);
            int_fractional_roundtrip!(i16, i32, i, 2);
            int_fractional_roundtrip!(i16, i64, i, 4);
            int_fractional_roundtrip!(i16, i128, i, 8);
        }

        #[test]
        fn roundtrip_i32(mut i: Vec<i32>) {
            int_fractional_roundtrip!(i32, u8, i, 1);
            int_fractional_roundtrip!(i32, u16, i, 1);
            int_fractional_roundtrip!(i32, u32, i, 1);
            int_fractional_roundtrip!(i32, u64, i, 2);
            int_fractional_roundtrip!(i32, u128, i, 4);
            int_fractional_roundtrip!(i32, i8, i, 1);
            int_fractional_roundtrip!(i32, i16, i, 1);
            int_fractional_roundtrip!(i32, i32, i, 1);
            int_fractional_roundtrip!(i32, i64, i, 2);
            int_fractional_roundtrip!(i32, i128, i, 4);
        }

        #[test]
        fn roundtrip_i64(mut i: Vec<i64>) {
            int_fractional_roundtrip!(i64, u8, i, 1);
            int_fractional_roundtrip!(i64, u16, i, 1);
            int_fractional_roundtrip!(i64, u32, i, 1);
            int_fractional_roundtrip!(i64, u64, i, 1);
            int_fractional_roundtrip!(i64, u128, i, 2);
            int_fractional_roundtrip!(i64, i8, i, 1);
            int_fractional_roundtrip!(i64, i16, i, 1);
            int_fractional_roundtrip!(i64, i32, i, 1);
            int_fractional_roundtrip!(i64, i64, i, 1);
            int_fractional_roundtrip!(i64, i128, i, 2);
        }

        #[test]
        fn roundtrip_i128(mut i: Vec<i128>) {
            int_fractional_roundtrip!(i128, u8, i, 1);
            int_fractional_roundtrip!(i128, u16, i, 1);
            int_fractional_roundtrip!(i128, u32, i, 1);
            int_fractional_roundtrip!(i128, u64, i, 1);
            int_fractional_roundtrip!(i128, u128, i, 1);
            int_fractional_roundtrip!(i128, i8, i, 1);
            int_fractional_roundtrip!(i128, i16, i, 1);
            int_fractional_roundtrip!(i128, i32, i, 1);
            int_fractional_roundtrip!(i128, i64, i, 1);
            int_fractional_roundtrip!(i128, i128, i, 1);
        }
    }
}
