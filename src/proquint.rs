/*!
The underlying representation of the `Proquint` type.

This is kept in a separate module to encapsulate usage of `unsafe`; within this module only, constructing a `Proquint` is an `unsafe` operation.
*/

use super::*;

/// A **pro**nounceable **quint**uplet, or proquint
///
/// A proquint is a representation of an arbitrary `u16` as a pronouncable 5-letter word composed of two syllables and a consonant.
/// Syllables are composed of a consonant followed by a vowel. By constructing a table of 16 consonants (encoding 4 bits of information each)
/// and 4 vowels (encoding 2 bits of information each), we may encode a 16-bit integer in big-endian order as follows:
///
/// bit  0 1 2 3 4 5 6 7 8 9 A B C D E F
/// repr c c c c v v c c c c v v c c c c
///
/// This type consists of a 16-bit integer which has been statically validated to be a proquint
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[repr(transparent)]
pub struct Proquint([u8; 5]);

impl Proquint {
    /// Borrow this proquint as a string
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn as_str(&self) -> &str {
        //SAFETY: a `Proquint` is always valid UTF-8
        unsafe { core::str::from_utf8_unchecked(&self.0) }
    }

    /// Get the bytes of this proquint
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn as_bytes(&self) -> &[u8; 5] {
        &self.0
    }

    /// Construct a proquint from a `u16`
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn from_u16(value: u16) -> Proquint {
        let first_syllable = (value & FIRST_SYLLABLE_MASK) >> FIRST_SYLLABLE_SHIFT;
        let second_syllable = (value & SECOND_SYLLABLE_MASK) >> SECOND_SYLLABLE_SHIFT;
        let consonant = (value & FINAL_CONSONANT_MASK) >> FINAL_CONSONANT_SHIFT;
        //SAFETY: this string is composed only of ASCII characters, and is therefore valid UTF-8
        //SAFETY: this string is a valid proquint
        Proquint([
            PROQUINT_SYLLABLES[first_syllable as usize][0],
            PROQUINT_SYLLABLES[first_syllable as usize][1],
            PROQUINT_SYLLABLES[second_syllable as usize][0],
            PROQUINT_SYLLABLES[second_syllable as usize][1],
            PROQUINT_CONSONANTS[consonant as usize],
        ])
    }

    /// Parse a proquint from bytes
    pub const fn from_bytes(bytes: [u8; 5]) -> Result<Proquint, ProquintParseError> {
        if Self::is_consonant(bytes[0])
            && Self::is_vowel(bytes[1])
            && Self::is_consonant(bytes[2])
            && Self::is_vowel(bytes[3])
            && Self::is_consonant(bytes[4])
        {
            //SAFETY: this string is composed only of ASCII characters, and is therefore valid UTF-8
            //SAFETY: this string is a valid proquint
            Ok(Proquint(bytes))
        } else {
            Err(ProquintParseError(Some(bytes)))
        }
    }

    /// Check whether a byte is a proquint consonant
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn is_consonant(byte: u8) -> bool {
        matches!(
            byte,
            b'b' | b'd'
                | b'f'
                | b'g'
                | b'h'
                | b'j'
                | b'k'
                | b'l'
                | b'm'
                | b'n'
                | b'p'
                | b'r'
                | b's'
                | b't'
                | b'v'
                | b'z'
        )
    }

    /// Check whether a byte is a proquint vowel
    #[cfg_attr(not(tarpaulin), inline(always))]
    pub const fn is_vowel(byte: u8) -> bool {
        matches!(byte, b'a' | b'i' | b'o' | b'u')
    }
}

impl Deref for Proquint {
    type Target = [u8; 5];

    #[cfg_attr(not(tarpaulin), inline(always))]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl AsRef<str> for Proquint {
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<[u8]> for Proquint {
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn as_ref(&self) -> &[u8] {
        &self.0[..]
    }
}

impl AsRef<[u8; 5]> for Proquint {
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn as_ref(&self) -> &[u8; 5] {
        &self.0
    }
}

impl Borrow<str> for Proquint {
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl Borrow<[u8]> for Proquint {
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn borrow(&self) -> &[u8] {
        &self.0
    }
}

impl Borrow<[u8; 5]> for Proquint {
    #[cfg_attr(not(tarpaulin), inline(always))]
    fn borrow(&self) -> &[u8; 5] {
        &self.0
    }
}
