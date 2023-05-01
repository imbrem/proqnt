/*!
# proqnt
A **pro**nounceable **quint**uplet, or *proquint*, is a pronounceable 5-letter string encoding a unique 16-bit integer.

Proquints may be used to encode binary data such as IP addresses, public keys, and UUIDs in a more human-friendly way.
*/
#![forbid(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

use core::{
    array,
    borrow::Borrow,
    fmt::{Debug, Display},
    iter::{once, Once},
    ops::Deref,
    str::FromStr,
};

mod proquint;
pub use proquint::Proquint;

pub mod fractional;
use fractional::*;

/// The consonants which may appear in a proquint, indexed by their 4-bit binary values
pub const PROQUINT_CONSONANTS: [u8; 16] = [
    b'b', b'd', b'f', b'g', b'h', b'j', b'k', b'l', b'm', b'n', b'p', b'r', b's', b't', b'v', b'z',
];

/// The vowels which may appear in a proquint, indexed by their 2-bit binary values
pub const PROQUINT_VOWELS: [u8; 4] = [b'a', b'i', b'o', b'u'];

/// The syllables which may appear in a proquint, indexed by their 6-bit binary values
///
/// A proquint syllable consists of a consonant (encoding 4 bits) followed by a syllable (encoding 2 bits).
pub const PROQUINT_SYLLABLES: [[u8; 2]; 64] = [
    *b"ba", *b"bi", *b"bo", *b"bu", *b"da", *b"di", *b"do", *b"du", *b"fa", *b"fi", *b"fo", *b"fu",
    *b"ga", *b"gi", *b"go", *b"gu", *b"ha", *b"hi", *b"ho", *b"hu", *b"ja", *b"ji", *b"jo", *b"ju",
    *b"ka", *b"ki", *b"ko", *b"ku", *b"la", *b"li", *b"lo", *b"lu", *b"ma", *b"mi", *b"mo", *b"mu",
    *b"na", *b"ni", *b"no", *b"nu", *b"pa", *b"pi", *b"po", *b"pu", *b"ra", *b"ri", *b"ro", *b"ru",
    *b"sa", *b"si", *b"so", *b"su", *b"ta", *b"ti", *b"to", *b"tu", *b"va", *b"vi", *b"vo", *b"vu",
    *b"za", *b"zi", *b"zo", *b"zu",
];

/// A 2-bit mask for the data contained in a proquint vowel
pub const VOWEL_MASK: u16 = 0b11;
/// A 4-bit mask for the data contained in a proquint consonant
pub const CONSONANT_MASK: u16 = 0b1111;
/// A 6-bit mask for the data contained in a proquint syllable
pub const SYLLABLE_MASK: u16 = 0b111111;

/// The shift for the data contained in a proquint's first consonant
pub const FIRST_CONSONANT_SHIFT: u32 = 12;
/// The mask for the data contained in a proquint's first consonant
pub const FIRST_CONSONANT_MASK: u16 = CONSONANT_MASK << FIRST_CONSONANT_SHIFT;
/// The shift for the data contained in a proquint's first vowel
pub const FIRST_VOWEL_SHIFT: u32 = 10;
/// The mask for the data contained in a proquint's first vowel
pub const FIRST_VOWEL_MASK: u16 = VOWEL_MASK << FIRST_VOWEL_SHIFT;
/// The shift for the data contained in a proquint's second consonant
pub const SECOND_CONSONANT_SHIFT: u32 = 6;
/// The mask for the data contained in a proquint's second consonant
pub const SECOND_CONSONANT_MASK: u16 = CONSONANT_MASK << SECOND_CONSONANT_SHIFT;
/// The shift for the data contained in a proquint's second vowel
pub const SECOND_VOWEL_SHIFT: u32 = 4;
/// The mask for the data contained in a proquint's second vowel
pub const SECOND_VOWEL_MASK: u16 = VOWEL_MASK << SECOND_VOWEL_SHIFT;
/// The shift for the data contained in a proquint's final consonant
pub const FINAL_CONSONANT_SHIFT: u32 = 0;
/// The mask for the data contained in a proquint's final consonant
pub const FINAL_CONSONANT_MASK: u16 = CONSONANT_MASK << FINAL_CONSONANT_SHIFT;
/// The shift for the data contained in a proquint's first syllable
pub const FIRST_SYLLABLE_SHIFT: u32 = FIRST_VOWEL_SHIFT;
/// The mask for the data contained in a proquint's first syllable
pub const FIRST_SYLLABLE_MASK: u16 = SYLLABLE_MASK << FIRST_VOWEL_SHIFT;
/// The shift for the data contained in a proquint's second syllable
pub const SECOND_SYLLABLE_SHIFT: u32 = SECOND_VOWEL_SHIFT;
/// The mask for the data contained in a proquint's second syllable
pub const SECOND_SYLLABLE_MASK: u16 = SYLLABLE_MASK << SECOND_SYLLABLE_SHIFT;

impl FromStr for Proquint {
    type Err = ProquintParseError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let bytes: [u8; 5] = s
            .as_bytes()
            .try_into()
            .map_err(|_| ProquintParseError(None))?;
        Self::from_bytes(bytes)
    }
}

impl From<u16> for Proquint {
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn from(value: u16) -> Self {
        Self::from_u16(value)
    }
}

impl<'a> TryFrom<&'a [u8]> for Proquint {
    type Error = ProquintParseError;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
        let bytes: [u8; 5] = value.try_into().map_err(|_| ProquintParseError(None))?;
        Self::from_bytes(bytes)
    }
}

impl TryFrom<[u8; 5]> for Proquint {
    type Error = ProquintParseError;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn try_from(value: [u8; 5]) -> Result<Self, Self::Error> {
        Self::from_bytes(value)
    }
}

/// An error in parsing a proquint
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ProquintParseError(Option<[u8; 5]>);

impl Proquint {
    /// Get the value of this proquint as a `u16`
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn value(self) -> u16 {
        Self::value_from_bytes_unchecked(*self.as_bytes())
    }

    /// Parse 5 bytes as a proquint value
    ///
    /// Return an error if the input is not a valid proquint
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn value_from_bytes(bytes: [u8; 5]) -> Result<u16, ProquintParseError> {
        let first_consonant = Self::consonant(bytes[0]);
        let first_vowel = Self::vowel(bytes[1]);
        let second_consonant = Self::consonant(bytes[2]);
        let second_vowel = Self::vowel(bytes[3]);
        let final_consonant = Self::consonant(bytes[4]);
        if first_consonant != u16::MAX
            && first_vowel != u16::MAX
            && second_consonant != u16::MAX
            && second_vowel != u16::MAX
            && final_consonant != u16::MAX
        {
            Ok(first_consonant << FIRST_CONSONANT_SHIFT
                | first_vowel << FIRST_VOWEL_SHIFT
                | second_consonant << SECOND_CONSONANT_SHIFT
                | second_vowel << SECOND_VOWEL_SHIFT
                | final_consonant << FINAL_CONSONANT_SHIFT)
        } else {
            Err(ProquintParseError(Some(bytes)))
        }
    }

    /// Parse 5 bytes as a proquint value
    ///
    /// Return an arbitrary value or panic if the input is not a valid proquint
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn value_from_bytes_unchecked(bytes: [u8; 5]) -> u16 {
        Self::consonant(bytes[0]) << FIRST_CONSONANT_SHIFT
            | Self::vowel(bytes[1]) << FIRST_VOWEL_SHIFT
            | Self::consonant(bytes[2]) << SECOND_CONSONANT_SHIFT
            | Self::vowel(bytes[3]) << SECOND_VOWEL_SHIFT
            | Self::consonant(bytes[4]) << FINAL_CONSONANT_SHIFT
    }

    /// Parse a proquint from a string
    ///
    /// Returns any unconsumed input
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub fn parse_partial(input: &str) -> Result<(&str, Proquint), ProquintParseError> {
        if input.len() >= 5 {
            Ok((
                &input[5..],
                Self::from_bytes(input.as_bytes()[..5].try_into().unwrap())?,
            ))
        } else {
            Err(ProquintParseError(None))
        }
    }

    /// Parse a proquint from a string
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn parse_str(input: &str) -> Result<Proquint, ProquintParseError> {
        Self::parse_bytes(input.as_bytes())
    }

    /// Parse a proquint from bytes
    ///
    /// Returns any unconsumed input
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub fn parse_partial_bytes(input: &[u8]) -> Result<(&[u8], Proquint), ProquintParseError> {
        if input.len() >= 5 {
            Ok((
                &input[5..],
                Self::from_bytes([input[0], input[1], input[2], input[3], input[4]])?,
            ))
        } else {
            Err(ProquintParseError(None))
        }
    }

    /// Parse a proquint from bytes
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn parse_bytes(input: &[u8]) -> Result<Proquint, ProquintParseError> {
        if input.len() == 5 {
            Self::from_bytes([input[0], input[1], input[2], input[3], input[4]])
        } else {
            Err(ProquintParseError(None))
        }
    }

    /// Parse a proquint value from a string
    ///
    /// Returns any unconsumed input
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub fn parse_partial_value(input: &str) -> Result<(&str, u16), ProquintParseError> {
        let (rest, result) = Self::parse_partial_value_bytes(input.as_bytes())?;
        Ok((&input[input.len() - rest.len()..], result))
    }

    /// Parse a proquint value from a string
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn parse_value(input: &str) -> Result<u16, ProquintParseError> {
        Self::parse_value_bytes(input.as_bytes())
    }

    /// Parse a proquint value from bytes
    ///
    /// Return any unconsumed input
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub fn parse_partial_value_bytes(input: &[u8]) -> Result<(&[u8], u16), ProquintParseError> {
        if input.len() >= 5 {
            Ok((
                &input[5..],
                Self::value_from_bytes([input[0], input[1], input[2], input[3], input[4]])?,
            ))
        } else {
            Err(ProquintParseError(None))
        }
    }

    /// Parse a proquint value from bytes
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn parse_value_bytes(input: &[u8]) -> Result<u16, ProquintParseError> {
        if input.len() == 5 {
            Self::value_from_bytes([input[0], input[1], input[2], input[3], input[4]])
        } else {
            Err(ProquintParseError(None))
        }
    }

    /// Get the value of a proquint consonant
    ///
    /// Returns `u16::MAX` for an invalid consonant
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn consonant(byte: u8) -> u16 {
        match byte {
            b'b' => 0,
            b'd' => 1,
            b'f' => 2,
            b'g' => 3,
            b'h' => 4,
            b'j' => 5,
            b'k' => 6,
            b'l' => 7,
            b'm' => 8,
            b'n' => 9,
            b'p' => 10,
            b'r' => 11,
            b's' => 12,
            b't' => 13,
            b'v' => 14,
            b'z' => 15,
            _ => u16::MAX, // fallback value for all other cases
        }
    }

    /// Get the value of a proquint vowel
    ///
    /// Returns `u16::MAX` for an invalid consonant
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn vowel(byte: u8) -> u16 {
        match byte {
            b'a' => 0,
            b'i' => 1,
            b'o' => 2,
            b'u' => 3,
            _ => u16::MAX,
        }
    }
}

impl<'a> TryFrom<&'a str> for Proquint {
    type Error = ProquintParseError;

    #[inline]
    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        Self::from_str(value)
    }
}

impl From<Proquint> for u16 {
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn from(value: Proquint) -> Self {
        value.value()
    }
}

impl Debug for Proquint {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl Display for Proquint {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Encode data as proquints
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ProquintEncode<T>(pub T);

impl<T> IntoIterator for ProquintEncode<T>
where
    T: IntoIterator,
    T::Item: FractionalEncode<u16>,
{
    type Item = Proquint;

    type IntoIter = ProquintEncodeIter<<FractionalDigits<T, u16> as IntoIterator>::IntoIter>;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn into_iter(self) -> Self::IntoIter {
        ProquintEncodeIter(FractionalDigits::new(self.0).into_iter())
    }
}

/// Iterate over some data's proquint encoding
#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ProquintEncodeIter<T>(pub T);

impl<T> Iterator for ProquintEncodeIter<T>
where
    T: Iterator,
    T::Item: Into<Proquint>,
{
    type Item = Proquint;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Into::into)
    }
}

impl<T> Display for ProquintEncode<T>
where
    T: Clone + IntoIterator,
    T::Item: FractionalEncode<u16>,
{
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut copied = self.clone().into_iter();
        if let Some(first) = copied.next() {
            write!(f, "{first}")?;
        }
        for digit in copied {
            write!(f, "-{digit}")?;
        }
        Ok(())
    }
}

/// Parse a buffer as a series of dash-separated proquint digits
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]

pub struct ParseProquintDigits<T> {
    /// The buffer to parse
    pub buffer: T,
    /// Whether to expect the data to start with a dash
    pub expect_dash: bool,
}

impl<T> ParseProquintDigits<T> {
    /// Create a new iterator over proquints parsed from the input buffer
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn new(buffer: T) -> ParseProquintDigits<T> {
        ParseProquintDigits {
            buffer,
            expect_dash: false,
        }
    }

    /// Create a new iterator over proquints parsed from the input buffer, which is expected to start with a dash
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn new_trailing(buffer: T) -> ParseProquintDigits<T> {
        ParseProquintDigits {
            buffer,
            expect_dash: true,
        }
    }
}

impl<'a> Iterator for ParseProquintDigits<&'a str> {
    type Item = u16;

    fn next(&mut self) -> Option<Self::Item> {
        let mut ptr = self.buffer;
        if self.expect_dash && *ptr.as_bytes().get(0)? == b'-' {
            ptr = &ptr[1..];
        }
        let (ptr, proquint) = Proquint::parse_partial_value(ptr).ok()?;
        self.buffer = ptr;
        self.expect_dash = true;
        Some(proquint)
    }
}

impl<'a> Iterator for ParseProquintDigits<&'a [u8]> {
    type Item = u16;

    fn next(&mut self) -> Option<Self::Item> {
        let mut ptr = self.buffer;
        if self.expect_dash && *ptr.get(0)? == b'-' {
            ptr = &ptr[1..];
        }
        let (ptr, proquint) = Proquint::parse_partial_value_bytes(ptr).ok()?;
        self.buffer = ptr;
        self.expect_dash = true;
        Some(proquint)
    }
}

impl<T> ParseProquintDigits<T>
where
    ParseProquintDigits<T>: IntoIterator<Item = u16>,
{
    /// Parse a data type from a series of proquint digits
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub fn parse<U: FromProquints>(self) -> Result<U, U::FromProquintsError> {
        U::from_proquints(self)
    }
}

/// Parse a buffer as a series of dash-separated proquints
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ParseProquints<T> {
    /// The buffer to parse
    pub buffer: T,
    /// Whether to expect the data to start with a dash
    pub expect_dash: bool,
}

impl<T> ParseProquints<T> {
    /// Create a new iterator over proquints parsed from the input buffer
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub fn new(buffer: T) -> ParseProquints<T> {
        ParseProquints {
            buffer,
            expect_dash: false,
        }
    }

    /// Create a new iterator over proquints parsed from the input buffer, which is expected to start with a dash
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub fn new_trailing(buffer: T) -> ParseProquints<T> {
        ParseProquints {
            buffer,
            expect_dash: true,
        }
    }
}

impl<'a> Iterator for ParseProquints<&'a str> {
    type Item = Proquint;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut ptr = self.buffer;
        if self.expect_dash && *ptr.as_bytes().get(0)? == b'-' {
            ptr = &ptr[1..]
        }
        let proquint = Proquint::try_from(ptr.get(0..5)?).ok()?;
        self.buffer = &ptr[5..];
        self.expect_dash = true;
        Some(proquint)
    }
}

impl<'a> Iterator for ParseProquints<&'a [u8]> {
    type Item = Proquint;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut ptr = self.buffer;
        if self.expect_dash && *ptr.get(0)? == b'-' {
            ptr = &ptr[1..]
        }
        let proquint = Proquint::try_from(ptr.get(0..5)?).ok()?;
        self.buffer = &ptr[5..];
        self.expect_dash = true;
        Some(proquint)
    }
}

/// Data which can be converted to a series of proquints
pub trait IntoProquints: Sized {
    /// An iterator over the proquint digits of this data
    type DigitsIter: IntoIterator<Item = u16>;

    /// Get the proquint digits of this data
    fn proquint_digits(self) -> Self::DigitsIter;

    /// Encode this data as a sequence of proquint digits
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn proquint_encode(self) -> ProquintEncode<Self::DigitsIter> {
        ProquintEncode(self.proquint_digits())
    }
}

impl<T> IntoProquints for T
where
    T: FractionalEncode<u16>,
{
    type DigitsIter = <FractionalDigits<Once<T>, u16> as IntoIterator>::IntoIter;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn proquint_digits(self) -> Self::DigitsIter {
        FractionalDigits::new(once(self)).into_iter()
    }
}

/// Data which can be constructed from a series of proquints
pub trait FromProquints
where
    Self: Sized,
{
    /// Error returned on failure to parse
    type FromProquintsError;

    /// Attempt to parse this type from a series of proquints
    ///
    /// May leave unconsumed elements in the iterator
    fn from_proquints_partial(
        proquints: impl Iterator<Item = u16>,
    ) -> Result<Self, Self::FromProquintsError>;

    /// The error to return on failure to parse due to trailing data
    fn trailing_error(next: Option<u16>) -> Self::FromProquintsError;

    /// Attempt to parse this type from a series of proquints, fully consuming the underlying iterator
    ///
    /// Returns an error in the case of trailing data.
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn from_proquints(
        proquints: impl IntoIterator<Item = u16>,
    ) -> Result<Self, Self::FromProquintsError> {
        let mut proquints = proquints.into_iter();
        let parse = Self::from_proquints_partial(&mut proquints)?;
        if let Some(next) = proquints.next() {
            Err(Self::trailing_error(Some(next)))
        } else {
            Ok(parse)
        }
    }

    /// Attempt to parse a string consisting of a series of proquints, returning any leftover portion
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn parse_partial_proquints(proquints: &str) -> Result<(&str, Self), Self::FromProquintsError> {
        let mut proquints = ParseProquintDigits::new(proquints);
        let parse = Self::from_proquints_partial(&mut proquints)?;
        Ok((proquints.buffer, parse))
    }

    /// Attempt to parse a string consisting of a series of proquints, returning any leftover portion
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn parse_partial_proquints_bytes(
        proquints: &[u8],
    ) -> Result<(&[u8], Self), Self::FromProquintsError> {
        let mut proquints = ParseProquintDigits::new(proquints);
        let parse = Self::from_proquints_partial(&mut proquints)?;
        Ok((proquints.buffer, parse))
    }

    /// Attempt to parse a string consisting of a series of proquints, completely consuming the input data
    ///
    /// Returns an error in the case of trailing data.
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn parse_proquints(proquints: impl AsRef<[u8]>) -> Result<Self, Self::FromProquintsError> {
        let mut proquints = ParseProquintDigits::new(proquints.as_ref());
        let parse = Self::from_proquints_partial(&mut proquints)?;
        if proquints.buffer.len() > 0 {
            Err(Self::trailing_error(None))
        } else {
            Ok(parse)
        }
    }
}

/// An error which occurs in parsing a stream of proquints
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ProquintsParseError {
    /// Not enough proquints to parse the desired data
    NotEnoughProquints(usize),
    /// Trailing data leftover after parsing
    TrailingData(Option<u16>),
    /// The value parsed is invalid
    InvalidValue,
}

impl FromProquints for u8 {
    type FromProquintsError = ProquintsParseError;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn from_proquints_partial(
        mut proquints: impl Iterator<Item = u16>,
    ) -> Result<Self, Self::FromProquintsError> {
        let [hi, lo] = proquints
            .next()
            .ok_or(ProquintsParseError::NotEnoughProquints(1))?
            .to_be_bytes();
        if hi == 00 {
            Ok(lo)
        } else {
            Err(ProquintsParseError::InvalidValue)
        }
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn trailing_error(next: Option<u16>) -> Self::FromProquintsError {
        ProquintsParseError::TrailingData(next)
    }
}

impl FromProquints for u16 {
    type FromProquintsError = ProquintsParseError;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn from_proquints_partial(
        mut proquints: impl Iterator<Item = u16>,
    ) -> Result<Self, Self::FromProquintsError> {
        proquints
            .next()
            .ok_or(ProquintsParseError::NotEnoughProquints(1))
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn trailing_error(next: Option<u16>) -> Self::FromProquintsError {
        ProquintsParseError::TrailingData(next)
    }
}

impl FromProquints for i16 {
    type FromProquintsError = ProquintsParseError;

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn from_proquints_partial(
        mut proquints: impl Iterator<Item = u16>,
    ) -> Result<Self, Self::FromProquintsError> {
        proquints
            .next()
            .map(|v| v as i16)
            .ok_or(ProquintsParseError::NotEnoughProquints(1))
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn trailing_error(next: Option<u16>) -> Self::FromProquintsError {
        ProquintsParseError::TrailingData(next)
    }
}

impl<const N: usize> FromProquints for [u8; N] {
    type FromProquintsError = ProquintsParseError;

    fn from_proquints_partial(
        mut proquints: impl Iterator<Item = u16>,
    ) -> Result<Self, Self::FromProquintsError> {
        let mut data = [0; N];
        for i in 0..N / 2 {
            let [hi, lo] = proquints
                .next()
                .ok_or(ProquintsParseError::NotEnoughProquints(N / 2 + N % 2 - i))?
                .to_be_bytes();
            data[i * 2] = hi;
            data[i * 2 + 1] = lo;
        }
        if N % 2 == 1 {
            let [hi, lo] = proquints
                .next()
                .ok_or(ProquintsParseError::NotEnoughProquints(1))?
                .to_be_bytes();
            if hi != 0 {
                return Err(ProquintsParseError::InvalidValue);
            }
            data[N - 1] = lo
        }
        Ok(data)
    }

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn trailing_error(next: Option<u16>) -> Self::FromProquintsError {
        ProquintsParseError::TrailingData(next)
    }
}

macro_rules! int_as_proquints {
    ($t:ty, $e:expr) => {

        impl FromProquints for $t {
            type FromProquintsError = ProquintsParseError;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn from_proquints_partial(
                mut proquints: impl Iterator<Item = u16>,
            ) -> Result<Self, Self::FromProquintsError> {
                let mut data: [u8; { $e * 2 }] = [0; { $e * 2 }];
                let [hi, lo] = proquints
                    .next()
                    .ok_or(ProquintsParseError::NotEnoughProquints(1))?
                    .to_be_bytes();
                data[0] = hi;
                data[1] = lo;
                for i in 1..$e {
                    if let Some(digit) = proquints.next() {
                        let [hi, lo] = digit.to_be_bytes();
                        data[i * 2] = hi;
                        data[i * 2 + 1] = lo;
                    } else {
                        // For unspecified bits, the big end should be zero!
                        data.rotate_left(i * 2);
                        break
                    }
                }
                Ok(<$t>::from_be_bytes(data))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn trailing_error(next: Option<u16>) -> Self::FromProquintsError {
                ProquintsParseError::TrailingData(next)
            }
        }
    };
}

int_as_proquints!(u32, 2);
int_as_proquints!(u64, 4);
int_as_proquints!(u128, 8);
int_as_proquints!(i32, 2);
int_as_proquints!(i64, 4);
int_as_proquints!(i128, 8);

#[cfg_attr(not(tarpaulin), inline(always))]
pub(crate) fn be_encode_array_u16<const M: usize>(array: &[u8]) -> [u16; M] {
    let mut result = [0; M];
    for (i, w) in array.chunks(2).enumerate() {
        result[i] = u16::from_be_bytes(w.try_into().unwrap())
    }
    result
}

#[cfg_attr(not(tarpaulin), inline(always))]
pub(crate) fn be_encode_array_u32<const M: usize>(array: &[u8]) -> [u32; M] {
    let mut result = [0; M];
    for (i, w) in array.chunks(4).enumerate() {
        result[i] = u32::from_be_bytes(w.try_into().unwrap())
    }
    result
}

#[cfg_attr(not(tarpaulin), inline(always))]
pub(crate) fn be_encode_array_u64<const M: usize>(array: &[u8]) -> [u64; M] {
    let mut result = [0; M];
    for (i, w) in array.chunks(8).enumerate() {
        result[i] = u64::from_be_bytes(w.try_into().unwrap())
    }
    result
}

#[cfg_attr(not(tarpaulin), inline(always))]
pub(crate) fn be_encode_array_i16<const M: usize>(array: &[u8]) -> [i16; M] {
    let mut result = [0; M];
    for (i, w) in array.chunks(2).enumerate() {
        result[i] = i16::from_be_bytes(w.try_into().unwrap())
    }
    result
}

#[cfg_attr(not(tarpaulin), inline(always))]
pub(crate) fn be_encode_array_i32<const M: usize>(array: &[u8]) -> [i32; M] {
    let mut result = [0; M];
    for (i, w) in array.chunks(4).enumerate() {
        result[i] = i32::from_be_bytes(w.try_into().unwrap())
    }
    result
}

#[cfg_attr(not(tarpaulin), inline(always))]
pub(crate) fn be_encode_array_i64<const M: usize>(array: &[u8]) -> [i64; M] {
    let mut result = [0; M];
    for (i, w) in array.chunks(8).enumerate() {
        result[i] = i64::from_be_bytes(w.try_into().unwrap())
    }
    result
}

#[cfg(feature = "std")]
mod std_ {
    use super::*;
    use std::net::{Ipv4Addr, Ipv6Addr};

    impl IntoProquints for Ipv4Addr {
        type DigitsIter = array::IntoIter<u16, 2>;

        #[cfg_attr(not(tarpaulin), inline(always))]
        fn proquint_digits(self) -> Self::DigitsIter {
            be_encode_array_u16::<2>(&self.octets()).into_iter()
        }
    }

    impl FromProquints for Ipv4Addr {
        type FromProquintsError = ProquintsParseError;

        #[cfg_attr(not(tarpaulin), inline(always))]
        fn from_proquints_partial(
            mut proquints: impl Iterator<Item = u16>,
        ) -> Result<Self, Self::FromProquintsError> {
            let [b0, b1] = proquints
                .next()
                .ok_or(ProquintsParseError::NotEnoughProquints(2))?
                .to_be_bytes();
            let [b2, b3] = proquints
                .next()
                .ok_or(ProquintsParseError::NotEnoughProquints(1))?
                .to_be_bytes();
            Ok(Ipv4Addr::new(b0, b1, b2, b3))
        }

        #[cfg_attr(not(tarpaulin), inline(always))]
        fn trailing_error(next: Option<u16>) -> Self::FromProquintsError {
            ProquintsParseError::TrailingData(next)
        }
    }

    impl IntoProquints for Ipv6Addr {
        type DigitsIter = array::IntoIter<u16, 8>;

        #[cfg_attr(not(tarpaulin), inline(always))]
        fn proquint_digits(self) -> Self::DigitsIter {
            be_encode_array_u16::<8>(&self.octets()).into_iter()
        }
    }

    impl FromProquints for Ipv6Addr {
        type FromProquintsError = ProquintsParseError;

        #[cfg_attr(not(tarpaulin), inline(always))]
        fn from_proquints_partial(
            mut proquints: impl Iterator<Item = u16>,
        ) -> Result<Self, Self::FromProquintsError> {
            let a = proquints
                .next()
                .ok_or(ProquintsParseError::NotEnoughProquints(8))?;
            let b = proquints
                .next()
                .ok_or(ProquintsParseError::NotEnoughProquints(7))?;
            let c = proquints
                .next()
                .ok_or(ProquintsParseError::NotEnoughProquints(6))?;
            let d = proquints
                .next()
                .ok_or(ProquintsParseError::NotEnoughProquints(5))?;
            let e = proquints
                .next()
                .ok_or(ProquintsParseError::NotEnoughProquints(4))?;
            let f = proquints
                .next()
                .ok_or(ProquintsParseError::NotEnoughProquints(3))?;
            let g = proquints
                .next()
                .ok_or(ProquintsParseError::NotEnoughProquints(2))?;
            let h = proquints
                .next()
                .ok_or(ProquintsParseError::NotEnoughProquints(1))?;
            Ok(Ipv6Addr::new(a, b, c, d, e, f, g, h))
        }

        #[cfg_attr(not(tarpaulin), inline(always))]
        fn trailing_error(next: Option<u16>) -> Self::FromProquintsError {
            ProquintsParseError::TrailingData(next)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;

    macro_rules! roundtrip {
        ($t:ty, $i:expr) => {{
            let mut encoded = format!("{}", $i.proquint_encode());
            assert_eq!(<$t>::parse_proquints(&encoded).unwrap(), $i);
            assert_eq!(<$t>::parse_proquints(encoded.as_bytes()).unwrap(), $i);
            assert_eq!(<$t>::parse_partial_proquints(&encoded).unwrap(), ("", $i));
            assert_eq!(
                <$t>::parse_partial_proquints_bytes(encoded.as_bytes()).unwrap(),
                (&b""[..], $i)
            );
            encoded.push('a');
            assert_eq!(
                <$t>::parse_proquints(&encoded).unwrap_err(),
                ProquintsParseError::TrailingData(None)
            );
            assert_eq!(<$t>::parse_partial_proquints(&encoded).unwrap(), ("a", $i));
        }};
    }

    proptest! {
        #[test]
        fn roundtrip_proquint(i: u16) {
            let pq = Proquint::from(i);
            assert_eq!(u16::from(pq), i);
            let as_str = pq.as_str();
            assert_eq!(as_str.as_bytes(), &*pq);
            assert_eq!(as_str, <Proquint as AsRef<str>>::as_ref(&pq));
            assert_eq!(as_str.as_bytes(), <Proquint as AsRef<[u8]>>::as_ref(&pq));
            assert_eq!(as_str.as_bytes(), <Proquint as AsRef<[u8; 5]>>::as_ref(&pq));
            assert_eq!(as_str, <Proquint as Borrow<str>>::borrow(&pq));
            assert_eq!(as_str.as_bytes(), <Proquint as Borrow<[u8]>>::borrow(&pq));
            assert_eq!(as_str.as_bytes(), <Proquint as Borrow<[u8; 5]>>::borrow(&pq));
            assert_eq!(format!("{pq}").parse::<Proquint>().unwrap(), pq);
            assert_eq!(format!("{pq:?}").parse::<Proquint>().unwrap(), pq);
            assert_eq!(Proquint::try_from(*pq).unwrap(), pq);
            assert_eq!(Proquint::try_from(&pq[..]).unwrap(), pq);
        }

        #[test]
        fn roundtrip_u128(i: u128) {
            roundtrip!(u128, i);
        }

        #[test]
        fn roundtrip_u64(i: u64) {
            roundtrip!(u64, i);
            roundtrip!(u128, i as u128);
            assert_eq!(
                u128::from_proquints(i.proquint_digits()).unwrap(),
                i as u128
            );
        }

        #[test]
        fn roundtrip_u32(i: u32) {
            roundtrip!(u32, i);
        }

        #[test]
        fn roundtrip_u16(i: u16) {
            roundtrip!(u16, i);
        }

        #[test]
        fn roundtrip_u8(i: u8) {
            roundtrip!(u8, i);
        }

        #[test]
        fn roundtrip_i128(i: i128) {
            roundtrip!(i128, i);
        }

        #[test]
        fn roundtrip_i64(i: i64) {
            roundtrip!(i64, i);
        }

        #[test]
        fn roundtrip_i32(i: i32) {
            roundtrip!(i32, i);
        }

        #[test]
        fn roundtrip_i16(i: i16) {
            roundtrip!(i16, i);
        }

        #[test]
        fn roundtrip_u8_4(i: [u8; 4]) {
            roundtrip!([u8; 4], i);
        }

        #[test]
        fn roundtrip_u8_3(i: [u8; 3]) {
            roundtrip!([u8; 3], i);
        }

        #[test]
        fn parse_proquints(v: Vec<u16>) {
            let proquints = format!("{}", ProquintEncode(v.iter().cloned()));
            Iterator::eq(ParseProquintDigits::new(&proquints[..]), ParseProquints::new(&proquints[..]).map(u16::from));
            Iterator::eq(ParseProquintDigits::new(&proquints[..]).map(Proquint::from), ParseProquints::new(&proquints[..]));
            Iterator::eq(ParseProquintDigits::new(proquints.as_bytes()), ParseProquints::new(proquints.as_bytes()).map(u16::from));
            Iterator::eq(ParseProquintDigits::new(proquints.as_bytes()).map(Proquint::from), ParseProquints::new(proquints.as_bytes()));
        }
    }

    #[cfg(feature = "std")]
    proptest! {
        #[test]
        fn roundtrip_ipv4(i: std::net::Ipv4Addr) {
            roundtrip!(std::net::Ipv4Addr, i);
        }

        #[test]
        fn roundtrip_ipv6(i: std::net::Ipv6Addr) {
            roundtrip!(std::net::Ipv6Addr, i);
        }
    }

    #[test]
    fn proquint_encode_nil() {
        assert_eq!(
            format!("{}", ProquintEncode(core::iter::Empty::<u16>::default())),
            ""
        );
    }

    #[test]
    fn invalid_proquint() {
        assert_eq!(
            Proquint::try_from(*b"xxxxx"),
            Err(ProquintParseError(Some(*b"xxxxx")))
        );
        assert_eq!(
            Proquint::try_from("bxxxx"),
            Err(ProquintParseError(Some(*b"bxxxx")))
        );
        assert_eq!(
            Proquint::parse_str("bxxxx"),
            Err(ProquintParseError(Some(*b"bxxxx")))
        );
        assert_eq!(
            Proquint::parse_partial("bxxxx"),
            Err(ProquintParseError(Some(*b"bxxxx")))
        );
        assert_eq!(
            Proquint::parse_partial("bxxx"),
            Err(ProquintParseError(None))
        );
        assert_eq!(
            Proquint::parse_value_bytes(b"baxxx"),
            Err(ProquintParseError(Some(*b"baxxx")))
        );
        assert_eq!(
            Proquint::parse_value_bytes(b"baxx"),
            Err(ProquintParseError(None))
        );
        assert_eq!(
            Proquint::parse_bytes(b"baxxx"),
            Err(ProquintParseError(Some(*b"baxxx")))
        );
        assert_eq!(
            Proquint::parse_bytes(b"baxx"),
            Err(ProquintParseError(None))
        );
        assert_eq!(
            Proquint::parse_partial_bytes(b"baxxx"),
            Err(ProquintParseError(Some(*b"baxxx")))
        );
        assert_eq!(
            Proquint::parse_partial_bytes(b"baxx"),
            Err(ProquintParseError(None))
        );
        assert_eq!(
            Proquint::parse_value("babxx"),
            Err(ProquintParseError(Some(*b"babxx")))
        );
        assert_eq!(
            "12345".parse::<Proquint>(),
            Err(ProquintParseError(Some(*b"12345")))
        );
    }

    #[test]
    fn u8_overflow_proquint() {
        assert_eq!(
            u8::from_proquints(once(0x0100)),
            Err(ProquintsParseError::InvalidValue)
        );
        assert_eq!(
            u8::from_proquints([0x0010, 0x0000]),
            Err(ProquintsParseError::TrailingData(Some(0x0000)))
        )
    }

    #[cfg(feature = "std")]
    #[test]
    fn proquint_example_ips() {
        use std::net::Ipv4Addr;

        let ips = [
            (Ipv4Addr::new(127, 0, 0, 1), "lusab-babad"),
            (Ipv4Addr::new(63, 84, 220, 193), "gutih-tugad"),
            (Ipv4Addr::new(63, 118, 7, 35), "gutuk-bisog"),
            (Ipv4Addr::new(140, 98, 193, 141), "mudof-sakat"),
            (Ipv4Addr::new(64, 255, 6, 200), "haguz-biram"),
            (Ipv4Addr::new(128, 30, 52, 45), "mabiv-gibot"),
            (Ipv4Addr::new(147, 67, 119, 2), "natag-lisaf"),
            (Ipv4Addr::new(212, 58, 253, 68), "tibup-zujah"),
            (Ipv4Addr::new(216, 35, 68, 215), "tobog-higil"),
            (Ipv4Addr::new(216, 68, 232, 21), "todah-vobij"),
            (Ipv4Addr::new(198, 81, 129, 136), "sinid-makam"),
            (Ipv4Addr::new(12, 110, 110, 204), "budov-kuras"),
            (Ipv4Addr::new(255, 255, 255, 255), "zuzuz-zuzuz"),
        ];

        for (ip, name) in ips {
            assert_eq!(format!("{}", ip.proquint_encode()), name);
        }
    }
}
