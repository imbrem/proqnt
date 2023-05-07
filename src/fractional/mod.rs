/*!
Encoding datatypes as fractional numbers of another datatype
*/
use arrayvec::ArrayVec;

use crate::{
    be_encode_array_i16, be_encode_array_i32, be_encode_array_i64, be_encode_array_u16,
    be_encode_array_u32, be_encode_array_u64,
};
use core::{fmt::Display, iter::Empty, marker::PhantomData};

mod ints;

/// A datatype which may be encoded as a fractional number of another datatype
///
/// For example, a `u8` can be viewed as containing half a `u16`, whereas a `u32` contains 2.
/// In general, for a datatype `T` containing `M`/`N` units of `S`, `IntoFraction` will
/// consume `M` elements of type `T` from the input iterator to yield an element of `S` and an
/// iterator over `N - 1` elements of `S`, making `N` total. This is done to optimize the handling
/// of reciprocals `1/N`.
///
/// This trait encodes integers in *network order*, i.e. in *big-endian* order.
pub trait IntoFraction<S> {
    /// The type of the iterator over output proquints
    type RestIter: Iterator<Item = S>;

    /// Consume `M` elements of input, yielding `N` elements of output.
    ///
    /// This is returned as a tuple of the first output element and an iterator over
    /// the rest, to optimize the common case where only one output element is returned.
    fn next_pieces(iter: impl Iterator<Item = Self>) -> Option<(S, Self::RestIter)>;

    /// Return an empty iterator
    fn empty_rest() -> Self::RestIter;
}

/// A type which can be converted into a known number of fractional pieces of another
pub trait IntoFixedFraction<S>: FromFraction<S> {
    /// How much input is consumed by one call of [`IntoFraction::next_pieces`]
    const INPUT_CONSUMED: usize;
    /// The number of pieces in an [`IntoFraction::RestIter`] produced by [`IntoFraction::next_pieces`]
    const REST_PRODUCED: usize;
}

/// A datatype which may be decoded from an iterator of fractional digits
///
/// Unlike [`IntoFraction`], for a datatype `T` containing `M`/`N + 1` units of `S`,
/// `from_digits` is fallible and guarantees that any trailing data is null, throwing
/// an error otherwise; hence, it is not necessary to return a `RestIter`.
///
/// For a more concrete example, say we wished to parse a `u8` from a list of `u32`.
/// While [`IntoFraction`] would consume one `u32` and return four `u8`s (the most
/// significant byte as output and the rest in `RestIter`), `FromFraction` would
/// consume one `u32` and return either:
/// - One `u8` corresponding to the *least* significant byte if all other bytes are zero
/// - An error
///
/// Hence, while [`IntoFraction`] supports *converting* an array `[T; N]` to digits `S`,
/// [`FromFraction`] supports *constructing* an array `[T; N]` from digits `S`, and will
/// throw an error if the most significant trailing digits are non-null.
///
/// For example, if I were to try to construct a `[u8; 7]` from a `u32`, `FromFraction`
/// would consume two `u32` and return either:
/// - An array `[u8; 7]` with
///     - The first four bytes correspond to the first `u32` in big-endian form
///     - The last three bytes corresponding to the three *least* significant bytes of
///       the second `u32` in *big* endian order, assuming the most significant byte is 0
/// - An error
///
/// Note that this is slightly unintuitive; the most natural thing to do would be to
/// have the first three bytes correspond to the first `u32` and the last four to the
/// second `u32`, asserting instead that the most significant byte of the first `u32`
/// was 0. Unfortunately, doing so would conflict with the behaviour of [`IntoFraction`]
/// for unaligned data streams, so we don't.
pub trait FromFraction<S>: Sized {
    /// Coalesce a value from a stream of pieces
    ///
    /// Leaves any unused pieces in the iterator
    fn from_pieces(iter: impl Iterator<Item = S>) -> Result<Self, FromFractionError>;
}

/// Data which might be null
pub trait MaybeNull {
    /// Check whether this data is null
    fn is_null(&self) -> bool;
}

impl<const N: usize, T> MaybeNull for [T; N]
where
    T: MaybeNull,
{
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn is_null(&self) -> bool {
        self.iter().all(MaybeNull::is_null)
    }
}

/// An error trying to decode data from fractional pieces
///
/// If the inner integer is `0`, indicates invalid input.
/// If the inner integer is `0 < n < usize::MAX`, indicates that at least `n` elements of additional data were needed.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct FromFractionError(pub usize);

impl Display for FromFractionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.0 == 0 {
            write!(f, "invalid input")
        } else {
            write!(f, "expected at least {} more fractional digits", self.0)
        }
    }
}

/// Converts data into a stream of digits
///
/// Uses [`IntoFraction`] to convert the data into a sequence of big-endian digits
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
    T::Item: IntoFraction<S>,
{
    type Item = S;

    type IntoIter = FractionalDigitsIter<T::IntoIter, <T::Item as IntoFraction<S>>::RestIter, S>;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn into_iter(self) -> Self::IntoIter {
        FractionalDigitsIter {
            input: self.input.into_iter(),
            rest: <T::Item as IntoFraction<S>>::empty_rest(),
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

impl<T, S> Iterator for FractionalDigitsIter<T, <T::Item as IntoFraction<S>>::RestIter, S>
where
    T: Iterator,
    T::Item: IntoFraction<S>,
{
    type Item = S;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.rest.next() {
            return Some(next);
        } else {
            let (digit, rest) = T::Item::next_pieces(&mut self.input)?;
            self.rest = rest;
            Some(digit)
        }
    }
}

impl<'a, T, S> IntoFraction<S> for &'a T
where
    T: Clone,
    T: IntoFraction<S>,
{
    type RestIter = T::RestIter;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn next_pieces(iter: impl Iterator<Item = Self>) -> Option<(S, Self::RestIter)> {
        T::next_pieces(iter.cloned())
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn empty_rest() -> Self::RestIter {
        T::empty_rest()
    }
}

impl<const N: usize, T, S> IntoFraction<S> for [T; N]
where
    T: IntoFraction<S>,
{
    type RestIter = <FractionalDigits<arrayvec::IntoIter<T, N>, S> as IntoIterator>::IntoIter;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<(S, Self::RestIter)> {
        let next = ArrayVec::from(iter.next()?);
        let mut digits = FractionalDigits::new(next).into_iter();
        let first: S = digits.next()?;
        Some((first, digits))
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn empty_rest() -> Self::RestIter {
        FractionalDigits::new(ArrayVec::new()).into_iter()
    }
}

impl<const N: usize, T, S> FromFraction<S> for [T; N]
where
    S: IntoFraction<T>,
    T: MaybeNull,
{
    fn from_pieces(mut iter: impl Iterator<Item = S>) -> Result<Self, FromFractionError> {
        let mut result: ArrayVec<T, N> = ArrayVec::new();
        loop {
            result = match result.into_inner() {
                Ok(result) => return Ok(result),
                Err(result) => result,
            };
            let (next, rest) =
                S::next_pieces(&mut iter).ok_or(FromFractionError(N - result.len()))?;
            let rest_head = result.len();
            let mut head = rest_head;
            result.push(next);
            for rest in rest {
                if let Err(err) = result.try_push(rest) {
                    if !result[head].is_null() {
                        return Err(FromFractionError(0));
                    }
                    result[head] = err.element();
                    head += 1;
                    if head >= result.len() {
                        head = rest_head;
                    }
                }
            }
        }
    }
}

#[cfg(feature = "std")]
mod std_ {
    use super::*;

    impl std::error::Error for FromFractionError {}
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        fn from_u8_7_2_u32(i: [u8; 7]) {
            let mut digits = FractionalDigits::<_, u32>::new(i).into_iter();
            let hi = digits.next().unwrap();
            let lo = digits.next().unwrap();
            assert_eq!(digits.next(), None);
            assert!(lo < (1 << 24));
            assert_eq!(<[u8; 7] as FromFraction<u32>>::from_pieces([hi, lo].into_iter()).unwrap(), i);
            let mut i2 = i;
            i2[0] |= 1;
            assert_eq!(<[u8; 7] as FromFraction<u32>>::from_pieces([hi | (1 << 24), lo].into_iter()).unwrap(), i2);
            assert_eq!(<[u8; 7] as FromFraction<u32>>::from_pieces([hi, lo | (1 << 24)].into_iter()), Err(FromFractionError(0)));
        }
    }

    #[test]
    fn error_formatting() {
        assert_eq!(format!("{}", FromFractionError(0)), "invalid input");
        assert_eq!(format!("{}", FromFractionError(1)), "expected at least 1 more fractional digits");
        assert_eq!(format!("{}", FromFractionError(3)), "expected at least 3 more fractional digits");
    }
}
