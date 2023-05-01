use super::*;

macro_rules! equiv_fractional_encode {
    ($t:ty, $s:ty) => {
        cast_fractional_encode!($t, $t);
        cast_fractional_encode!($s, $t);
        cast_fractional_encode!($t, $s);
        cast_fractional_encode!($s, $s);
    };
}

macro_rules! cast_fractional_encode {
    ($t:ty, $s:ty) => {
        impl FractionalEncode<$s> for $t {
            type RestIter = Empty<$s>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<($s, Empty<$s>)> {
                Some((iter.next()? as $s, Empty::default()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                Default::default()
            }
        }
    };
}

macro_rules! int_fractional_encode_u8 {
    ($t:ty) => {
        impl FractionalEncode<u8> for $t {
            type RestIter = arrayvec::IntoIter<u8, { <$t>::BITS as usize / 8 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<(u8, Self::RestIter)> {
                let bytes = iter.next()?.to_be_bytes();
                let last: [u8; { <$t>::BITS as usize / 8 - 1 }] = bytes[1..].try_into().unwrap();
                Some((bytes[0], ArrayVec::from(last).into_iter()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                ArrayVec::new().into_iter()
            }
        }

        impl FractionalEncode<i8> for $t {
            type RestIter = arrayvec::IntoIter<i8, { <$t>::BITS as usize / 8 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<(i8, Self::RestIter)> {
                let bytes = iter.next()?.to_be_bytes();
                let last: [u8; { <$t>::BITS as usize / 8 - 1 }] = bytes[1..].try_into().unwrap();
                let mut last_signed = [0; { <$t>::BITS as usize / 8 - 1 }];
                for i in 0..(<$t>::BITS as usize / 8 - 1) {
                    last_signed[i] = last[i] as i8;
                }
                Some((bytes[0] as i8, ArrayVec::from(last_signed).into_iter()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                ArrayVec::new().into_iter()
            }
        }

        impl FractionalEncode<$t> for u8 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
                let mut result: $t = iter.next()? as $t;
                for _ in 1..(<$t>::BITS as usize / 8) {
                    if let Some(next) = iter.next() {
                        result <<= 8;
                        result |= next as $t;
                    } else {
                        break;
                    }
                }
                Some((result, Empty::default()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                Empty::default()
            }
        }

        impl FractionalEncode<$t> for i8 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
                let mut result: $t = iter.next()? as u8 as $t;
                //TODO: allow partial encodings?
                for _ in 1..(<$t>::BITS as usize / 8) {
                    if let Some(next) = iter.next() {
                        result <<= 8;
                        result |= next as u8 as $t;
                    } else {
                        break;
                    }
                }
                Some((result, Empty::default()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                Empty::default()
            }
        }
    };
}

macro_rules! int_fractional_encode_u16 {
    ($t:ty) => {
        impl FractionalEncode<u16> for $t {
            type RestIter = arrayvec::IntoIter<u16, { <$t>::BITS as usize / 16 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<(u16, Self::RestIter)> {
                let bytes = iter.next()?.to_be_bytes();
                Some((
                    u16::from_be_bytes([bytes[0], bytes[1]]),
                    ArrayVec::from(be_encode_array_u16::<{ <$t>::BITS as usize / 16 - 1 }>(
                        &bytes[2..],
                    ))
                    .into_iter(),
                ))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                ArrayVec::new().into_iter()
            }
        }

        impl FractionalEncode<i16> for $t {
            type RestIter = arrayvec::IntoIter<i16, { <$t>::BITS as usize / 16 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<(i16, Self::RestIter)> {
                let bytes = iter.next()?.to_be_bytes();
                Some((
                    i16::from_be_bytes([bytes[0], bytes[1]]),
                    ArrayVec::from(be_encode_array_i16::<{ <$t>::BITS as usize / 16 - 1 }>(
                        &bytes[2..],
                    ))
                    .into_iter(),
                ))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                ArrayVec::new().into_iter()
            }
        }

        impl FractionalEncode<$t> for u16 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
                let mut result: $t = iter.next()? as $t;
                //TODO: allow partial encodings?
                for _ in 1..(<$t>::BITS as usize / 16) {
                    if let Some(next) = iter.next() {
                        result <<= 16;
                        result |= next as $t;
                    } else {
                        break;
                    }
                }
                Some((result, Empty::default()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                Empty::default()
            }
        }

        impl FractionalEncode<$t> for i16 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
                let mut result: $t = iter.next()? as u16 as $t;
                //TODO: allow partial encodings?
                for _ in 1..(<$t>::BITS as usize / 16) {
                    if let Some(next) = iter.next() {
                        result <<= 16;
                        result |= next as u16 as $t;
                    } else {
                        break;
                    }
                }
                Some((result, Empty::default()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                Empty::default()
            }
        }
    };
}

macro_rules! int_fractional_encode_u32 {
    ($t:ty) => {
        impl FractionalEncode<u32> for $t {
            type RestIter = arrayvec::IntoIter<u32, { <$t>::BITS as usize / 32 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<(u32, Self::RestIter)> {
                let bytes = iter.next()?.to_be_bytes();
                Some((
                    u32::from_be_bytes(bytes[0..4].try_into().unwrap()),
                    ArrayVec::from(be_encode_array_u32::<{ <$t>::BITS as usize / 32 - 1 }>(
                        &bytes[4..],
                    ))
                    .into_iter(),
                ))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                ArrayVec::new().into_iter()
            }
        }

        impl FractionalEncode<i32> for $t {
            type RestIter = arrayvec::IntoIter<i32, { <$t>::BITS as usize / 32 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<(i32, Self::RestIter)> {
                let bytes = iter.next()?.to_be_bytes();
                Some((
                    i32::from_be_bytes(bytes[0..4].try_into().unwrap()),
                    ArrayVec::from(be_encode_array_i32::<{ <$t>::BITS as usize / 32 - 1 }>(
                        &bytes[4..],
                    ))
                    .into_iter(),
                ))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                ArrayVec::new().into_iter()
            }
        }

        impl FractionalEncode<$t> for u32 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
                let mut result: $t = iter.next()? as $t;
                for _ in 1..(<$t>::BITS as usize / 32) {
                    if let Some(next) = iter.next() {
                        result <<= 32;
                        result |= next as $t;
                    } else {
                        break;
                    }
                }
                Some((result, Empty::default()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                Empty::default()
            }
        }

        impl FractionalEncode<$t> for i32 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
                let mut result: $t = iter.next()? as u32 as $t;
                for _ in 1..(<$t>::BITS as usize / 32) {
                    if let Some(next) = iter.next() {
                        result <<= 32;
                        result |= next as u32 as $t;
                    } else {
                        break;
                    }
                }
                Some((result, Empty::default()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                Empty::default()
            }
        }
    };
}

macro_rules! int_fractional_encode_u64 {
    ($t:ty) => {
        impl FractionalEncode<u64> for $t {
            type RestIter = arrayvec::IntoIter<u64, { <$t>::BITS as usize / 64 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<(u64, Self::RestIter)> {
                let bytes = iter.next()?.to_be_bytes();
                Some((
                    u64::from_be_bytes(bytes[0..8].try_into().unwrap()),
                    ArrayVec::from(be_encode_array_u64::<{ <$t>::BITS as usize / 64 - 1 }>(
                        &bytes[8..],
                    ))
                    .into_iter(),
                ))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                ArrayVec::new().into_iter()
            }
        }

        impl FractionalEncode<i64> for $t {
            type RestIter = arrayvec::IntoIter<i64, { <$t>::BITS as usize / 64 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<(i64, Self::RestIter)> {
                let bytes = iter.next()?.to_be_bytes();
                Some((
                    i64::from_be_bytes(bytes[0..8].try_into().unwrap()),
                    ArrayVec::from(be_encode_array_i64::<{ <$t>::BITS as usize / 64 - 1 }>(
                        &bytes[8..],
                    ))
                    .into_iter(),
                ))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                ArrayVec::new().into_iter()
            }
        }

        impl FractionalEncode<$t> for u64 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
                let mut result: $t = iter.next()? as $t;
                for _ in 1..(<$t>::BITS as usize / 64) {
                    if let Some(next) = iter.next() {
                        result <<= 64;
                        result |= next as $t;
                    } else {
                        break;
                    }
                }
                Some((result, Empty::default()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                Empty::default()
            }
        }

        impl FractionalEncode<$t> for i64 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_digits(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
                let mut result: $t = iter.next()? as u64 as $t;
                for _ in 1..(<$t>::BITS as usize / 64) {
                    if let Some(next) = iter.next() {
                        result <<= 64;
                        result |= next as u64 as $t;
                    } else {
                        break;
                    }
                }
                Some((result, Empty::default()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                Empty::default()
            }
        }
    };
}

equiv_fractional_encode!(u8, i8);
int_fractional_encode_u8!(u16);
int_fractional_encode_u8!(u32);
int_fractional_encode_u8!(u64);
int_fractional_encode_u8!(u128);
int_fractional_encode_u8!(i16);
int_fractional_encode_u8!(i32);
int_fractional_encode_u8!(i64);
int_fractional_encode_u8!(i128);

equiv_fractional_encode!(u16, i16);
int_fractional_encode_u16!(u32);
int_fractional_encode_u16!(u64);
int_fractional_encode_u16!(u128);
int_fractional_encode_u16!(i32);
int_fractional_encode_u16!(i64);
int_fractional_encode_u16!(i128);

equiv_fractional_encode!(u32, i32);
int_fractional_encode_u32!(u64);
int_fractional_encode_u32!(i64);
int_fractional_encode_u32!(u128);
int_fractional_encode_u32!(i128);

equiv_fractional_encode!(u64, i64);
int_fractional_encode_u64!(u128);
int_fractional_encode_u64!(i128);

equiv_fractional_encode!(u128, i128);