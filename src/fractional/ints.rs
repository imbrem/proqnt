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
        impl IntoFraction<$s> for $t {
            type RestIter = Empty<$s>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<($s, Empty<$s>)> {
                Some((iter.next()? as $s, Empty::default()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                Default::default()
            }
        }

        impl FromFraction<$s> for $t {
            #[cfg_attr(not(tarpaulin), inline(always))]
            fn from_pieces(mut iter: impl Iterator<Item = $s>) -> Result<$t, FromFractionError> {
                if let Some(next) = iter.next() {
                    Ok(next as $t)
                } else {
                    Err(FromFractionError(1))
                }
            }
        }
    };
}

macro_rules! maybe_null_impl {
    ($t:ty) => {
        impl MaybeNull for $t {
            #[cfg_attr(not(tarpaulin), inline(always))]
            fn is_null(&self) -> bool {
                *self == 0
            }
        }
    };
}

macro_rules! into_fixed_fraction_impl {
    ($s:ty, $t:ty) => {
        impl $crate::fractional::IntoFixedFraction<$s> for $t {
            const INPUT_CONSUMED: usize = if <$t>::BITS > <$s>::BITS {
                1
            } else {
                <$s>::BITS / <$t>::BITS
            } as usize;
            const REST_PRODUCED: usize = (<$s>::BITS / <$t>::BITS).saturating_sub(1) as usize;
        }
    };
}

/// Implement [`FromFraction<S>`] using [`IntoFraction<T>`] where multiple `S` are required to make one `T`
#[macro_export]
macro_rules! fractional_decode_from_big {
    ($s:ty, $t:ty) => {
        impl $crate::fractional::FromFraction<$s> for $t {
            #[cfg_attr(not(tarpaulin), inline(always))]
            fn from_pieces(
                mut iter: impl Iterator<Item = $s>,
            ) -> Result<$t, $crate::fractional::FromFractionError> {
                if let Some((next, mut rest)) =
                    $crate::fractional::IntoFraction::<$t>::next_pieces(&mut iter)
                {
                    debug_assert_eq!(rest.next(), None);
                    Ok(next)
                } else {
                    Err($crate::fractional::FromFractionError(1))
                }
            }
        }
    };
}

/// Implement [`FromFraction<S>`] using [`IntoFraction<T>`] where one `S` produces multiple `T`
///
/// Requires that `T` implements [`MaybeNull`] to detect invalid trailing input
#[macro_export]
macro_rules! fractional_decode_from_small {
    ($s:ty, $t:ty) => {
        impl $crate::fractional::FromFraction<$s> for $t {
            #[cfg_attr(not(tarpaulin), inline(always))]
            fn from_pieces(
                mut iter: impl Iterator<Item = $s>,
            ) -> Result<$t, $crate::fractional::FromFractionError> {
                use $crate::fractional::MaybeNull;
                if let Some((mut curr, mut rest)) =
                    $crate::fractional::IntoFraction::<$t>::next_pieces(&mut iter)
                {
                    loop {
                        if let Some(next) = rest.next() {
                            if !curr.is_null() {
                                return Err($crate::fractional::FromFractionError(0));
                            }
                            curr = next;
                        } else {
                            return Ok(curr);
                        }
                    }
                } else {
                    Err($crate::fractional::FromFractionError(1))
                }
            }
        }
    };
}

macro_rules! int_fractional_encode_u8 {
    ($t:ty) => {
        impl IntoFraction<u8> for $t {
            type RestIter = arrayvec::IntoIter<u8, { <$t>::BITS as usize / 8 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<(u8, Self::RestIter)> {
                let bytes = iter.next()?.to_be_bytes();
                let last: [u8; { <$t>::BITS as usize / 8 - 1 }] = bytes[1..].try_into().unwrap();
                Some((bytes[0], ArrayVec::from(last).into_iter()))
            }

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn empty_rest() -> Self::RestIter {
                ArrayVec::new().into_iter()
            }
        }

        impl IntoFraction<i8> for $t {
            type RestIter = arrayvec::IntoIter<i8, { <$t>::BITS as usize / 8 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<(i8, Self::RestIter)> {
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

        impl IntoFraction<$t> for u8 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
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

        impl IntoFraction<$t> for i8 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
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
        impl IntoFraction<u16> for $t {
            type RestIter = arrayvec::IntoIter<u16, { <$t>::BITS as usize / 16 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<(u16, Self::RestIter)> {
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

        impl IntoFraction<i16> for $t {
            type RestIter = arrayvec::IntoIter<i16, { <$t>::BITS as usize / 16 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<(i16, Self::RestIter)> {
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

        impl IntoFraction<$t> for u16 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
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

        impl IntoFraction<$t> for i16 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
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
        impl IntoFraction<u32> for $t {
            type RestIter = arrayvec::IntoIter<u32, { <$t>::BITS as usize / 32 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<(u32, Self::RestIter)> {
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

        impl IntoFraction<i32> for $t {
            type RestIter = arrayvec::IntoIter<i32, { <$t>::BITS as usize / 32 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<(i32, Self::RestIter)> {
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

        impl IntoFraction<$t> for u32 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
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

        impl IntoFraction<$t> for i32 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
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
        impl IntoFraction<u64> for $t {
            type RestIter = arrayvec::IntoIter<u64, { <$t>::BITS as usize / 64 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<(u64, Self::RestIter)> {
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

        impl IntoFraction<i64> for $t {
            type RestIter = arrayvec::IntoIter<i64, { <$t>::BITS as usize / 64 - 1 }>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<(i64, Self::RestIter)> {
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

        impl IntoFraction<$t> for u64 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
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

        impl IntoFraction<$t> for i64 {
            type RestIter = Empty<$t>;

            #[cfg_attr(not(tarpaulin), inline(always))]
            fn next_pieces(mut iter: impl Iterator<Item = Self>) -> Option<($t, Self::RestIter)> {
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

maybe_null_impl!(u8);
maybe_null_impl!(u16);
maybe_null_impl!(u32);
maybe_null_impl!(u64);
maybe_null_impl!(u128);
maybe_null_impl!(i8);
maybe_null_impl!(i16);
maybe_null_impl!(i32);
maybe_null_impl!(i64);
maybe_null_impl!(i128);

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

fractional_decode_from_big!(u8, u16);
fractional_decode_from_big!(u8, u32);
fractional_decode_from_big!(u8, u64);
fractional_decode_from_big!(u8, u128);
fractional_decode_from_big!(u8, i16);
fractional_decode_from_big!(u8, i32);
fractional_decode_from_big!(u8, i64);
fractional_decode_from_big!(u8, i128);

fractional_decode_from_small!(u16, u8);
fractional_decode_from_big!(u16, u32);
fractional_decode_from_big!(u16, u64);
fractional_decode_from_big!(u16, u128);
fractional_decode_from_small!(u16, i8);
fractional_decode_from_big!(u16, i32);
fractional_decode_from_big!(u16, i64);
fractional_decode_from_big!(u16, i128);

fractional_decode_from_small!(u32, u8);
fractional_decode_from_small!(u32, u16);
fractional_decode_from_big!(u32, u64);
fractional_decode_from_big!(u32, u128);
fractional_decode_from_small!(u32, i8);
fractional_decode_from_small!(u32, i16);
fractional_decode_from_big!(u32, i64);
fractional_decode_from_big!(u32, i128);

fractional_decode_from_small!(u64, u8);
fractional_decode_from_small!(u64, u16);
fractional_decode_from_small!(u64, u32);
fractional_decode_from_big!(u64, u128);
fractional_decode_from_small!(u64, i8);
fractional_decode_from_small!(u64, i16);
fractional_decode_from_small!(u64, i32);
fractional_decode_from_big!(u64, i128);

fractional_decode_from_small!(u128, u8);
fractional_decode_from_small!(u128, u16);
fractional_decode_from_small!(u128, u32);
fractional_decode_from_small!(u128, u64);
fractional_decode_from_small!(u128, i8);
fractional_decode_from_small!(u128, i16);
fractional_decode_from_small!(u128, i32);
fractional_decode_from_small!(u128, i64);

fractional_decode_from_big!(i8, u16);
fractional_decode_from_big!(i8, u32);
fractional_decode_from_big!(i8, u64);
fractional_decode_from_big!(i8, u128);
fractional_decode_from_big!(i8, i16);
fractional_decode_from_big!(i8, i32);
fractional_decode_from_big!(i8, i64);
fractional_decode_from_big!(i8, i128);

fractional_decode_from_small!(i16, u8);
fractional_decode_from_big!(i16, u32);
fractional_decode_from_big!(i16, u64);
fractional_decode_from_big!(i16, u128);
fractional_decode_from_small!(i16, i8);
fractional_decode_from_big!(i16, i32);
fractional_decode_from_big!(i16, i64);
fractional_decode_from_big!(i16, i128);

fractional_decode_from_small!(i32, u8);
fractional_decode_from_small!(i32, u16);
fractional_decode_from_big!(i32, u64);
fractional_decode_from_big!(i32, u128);
fractional_decode_from_small!(i32, i8);
fractional_decode_from_small!(i32, i16);
fractional_decode_from_big!(i32, i64);
fractional_decode_from_big!(i32, i128);

fractional_decode_from_small!(i64, u8);
fractional_decode_from_small!(i64, u16);
fractional_decode_from_small!(i64, u32);
fractional_decode_from_big!(i64, u128);
fractional_decode_from_small!(i64, i8);
fractional_decode_from_small!(i64, i16);
fractional_decode_from_small!(i64, i32);
fractional_decode_from_big!(i64, i128);

fractional_decode_from_small!(i128, u8);
fractional_decode_from_small!(i128, u16);
fractional_decode_from_small!(i128, u32);
fractional_decode_from_small!(i128, u64);
fractional_decode_from_small!(i128, i8);
fractional_decode_from_small!(i128, i16);
fractional_decode_from_small!(i128, i32);
fractional_decode_from_small!(i128, i64);

into_fixed_fraction_impl!(u8, u8);
into_fixed_fraction_impl!(u8, u16);
into_fixed_fraction_impl!(u8, u32);
into_fixed_fraction_impl!(u8, u64);
into_fixed_fraction_impl!(u8, u128);
into_fixed_fraction_impl!(u8, i8);
into_fixed_fraction_impl!(u8, i16);
into_fixed_fraction_impl!(u8, i32);
into_fixed_fraction_impl!(u8, i64);
into_fixed_fraction_impl!(u8, i128);

into_fixed_fraction_impl!(u16, u8);
into_fixed_fraction_impl!(u16, u16);
into_fixed_fraction_impl!(u16, u32);
into_fixed_fraction_impl!(u16, u64);
into_fixed_fraction_impl!(u16, u128);
into_fixed_fraction_impl!(u16, i8);
into_fixed_fraction_impl!(u16, i16);
into_fixed_fraction_impl!(u16, i32);
into_fixed_fraction_impl!(u16, i64);
into_fixed_fraction_impl!(u16, i128);

into_fixed_fraction_impl!(u32, u8);
into_fixed_fraction_impl!(u32, u16);
into_fixed_fraction_impl!(u32, u32);
into_fixed_fraction_impl!(u32, u64);
into_fixed_fraction_impl!(u32, u128);
into_fixed_fraction_impl!(u32, i8);
into_fixed_fraction_impl!(u32, i16);
into_fixed_fraction_impl!(u32, i32);
into_fixed_fraction_impl!(u32, i64);
into_fixed_fraction_impl!(u32, i128);

into_fixed_fraction_impl!(u64, u8);
into_fixed_fraction_impl!(u64, u16);
into_fixed_fraction_impl!(u64, u32);
into_fixed_fraction_impl!(u64, u64);
into_fixed_fraction_impl!(u64, u128);
into_fixed_fraction_impl!(u64, i8);
into_fixed_fraction_impl!(u64, i16);
into_fixed_fraction_impl!(u64, i32);
into_fixed_fraction_impl!(u64, i64);
into_fixed_fraction_impl!(u64, i128);

into_fixed_fraction_impl!(u128, u8);
into_fixed_fraction_impl!(u128, u16);
into_fixed_fraction_impl!(u128, u32);
into_fixed_fraction_impl!(u128, u64);
into_fixed_fraction_impl!(u128, u128);
into_fixed_fraction_impl!(u128, i8);
into_fixed_fraction_impl!(u128, i16);
into_fixed_fraction_impl!(u128, i32);
into_fixed_fraction_impl!(u128, i64);
into_fixed_fraction_impl!(u128, i128);

into_fixed_fraction_impl!(i8, u8);
into_fixed_fraction_impl!(i8, u16);
into_fixed_fraction_impl!(i8, u32);
into_fixed_fraction_impl!(i8, u64);
into_fixed_fraction_impl!(i8, u128);
into_fixed_fraction_impl!(i8, i8);
into_fixed_fraction_impl!(i8, i16);
into_fixed_fraction_impl!(i8, i32);
into_fixed_fraction_impl!(i8, i64);
into_fixed_fraction_impl!(i8, i128);

into_fixed_fraction_impl!(i16, u8);
into_fixed_fraction_impl!(i16, u16);
into_fixed_fraction_impl!(i16, u32);
into_fixed_fraction_impl!(i16, u64);
into_fixed_fraction_impl!(i16, u128);
into_fixed_fraction_impl!(i16, i8);
into_fixed_fraction_impl!(i16, i16);
into_fixed_fraction_impl!(i16, i32);
into_fixed_fraction_impl!(i16, i64);
into_fixed_fraction_impl!(i16, i128);

into_fixed_fraction_impl!(i32, u8);
into_fixed_fraction_impl!(i32, u16);
into_fixed_fraction_impl!(i32, u32);
into_fixed_fraction_impl!(i32, u64);
into_fixed_fraction_impl!(i32, u128);
into_fixed_fraction_impl!(i32, i8);
into_fixed_fraction_impl!(i32, i16);
into_fixed_fraction_impl!(i32, i32);
into_fixed_fraction_impl!(i32, i64);
into_fixed_fraction_impl!(i32, i128);

into_fixed_fraction_impl!(i64, u8);
into_fixed_fraction_impl!(i64, u16);
into_fixed_fraction_impl!(i64, u32);
into_fixed_fraction_impl!(i64, u64);
into_fixed_fraction_impl!(i64, u128);
into_fixed_fraction_impl!(i64, i8);
into_fixed_fraction_impl!(i64, i16);
into_fixed_fraction_impl!(i64, i32);
into_fixed_fraction_impl!(i64, i64);
into_fixed_fraction_impl!(i64, i128);

into_fixed_fraction_impl!(i128, u8);
into_fixed_fraction_impl!(i128, u16);
into_fixed_fraction_impl!(i128, u32);
into_fixed_fraction_impl!(i128, u64);
into_fixed_fraction_impl!(i128, u128);
into_fixed_fraction_impl!(i128, i8);
into_fixed_fraction_impl!(i128, i16);
into_fixed_fraction_impl!(i128, i32);
into_fixed_fraction_impl!(i128, i64);
into_fixed_fraction_impl!(i128, i128);

#[cfg(test)]
mod test {
    use super::*;
    use proptest::prelude::*;

    #[cfg(feature = "std")]
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

    macro_rules! from_int {
        ($s:ty, $t:ty, $i:expr) => {{
            let s = $i;
            match <$t as FromFraction<$s>>::from_pieces([s].into_iter()) {
                Ok(t) => {
                    let mut nz = false;
                    for digit in FractionalDigits::<_, $t>::new([s]) {
                        assert!(!nz);
                        if digit != 0 {
                            assert_eq!(digit, t);
                            nz = true;
                        }
                    }
                    assert_eq!(FromFraction::<$t>::from_pieces([t].into_iter()), Ok(s));
                }
                Err(e) => {
                    let mut digits = FractionalDigits::<_, $t>::new([s]).into_iter();
                    loop {
                        let next = digits.next().unwrap();
                        if next != 0 {
                            digits.next().unwrap();
                            break;
                        }
                    }
                    debug_assert_eq!(e, FromFractionError(0));
                }
            }
        }};
    }

    #[cfg(feature = "std")]
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
    proptest! {

        #[test]
        fn from_i8(i: i8) {
            from_int!(i8, u8, i);
            from_int!(i8, u16, i);
            from_int!(i8, u32, i);
            from_int!(i8, u64, i);
            from_int!(i8, u128, i);
            from_int!(i8, i8, i);
            from_int!(i8, i16, i);
            from_int!(i8, i32, i);
            from_int!(i8, i64, i);
            from_int!(i8, i128, i);
        }

        #[test]
        fn from_i16(i: i16) {
            from_int!(i16, u8, i);
            from_int!(i16, u16, i);
            from_int!(i16, u32, i);
            from_int!(i16, u64, i);
            from_int!(i16, u128, i);
            from_int!(i16, i8, i);
            from_int!(i16, i16, i);
            from_int!(i16, i32, i);
            from_int!(i16, i64, i);
            from_int!(i16, i128, i);
        }

        #[test]
        fn from_i32(i: i32) {
            from_int!(i32, u8, i);
            from_int!(i32, u16, i);
            from_int!(i32, u32, i);
            from_int!(i32, u64, i);
            from_int!(i32, u128, i);
            from_int!(i32, i8, i);
            from_int!(i32, i16, i);
            from_int!(i32, i32, i);
            from_int!(i32, i64, i);
            from_int!(i32, i128, i);
        }

        #[test]
        fn from_i64(i: i64) {
            from_int!(i64, u8, i);
            from_int!(i64, u16, i);
            from_int!(i64, u32, i);
            from_int!(i64, u64, i);
            from_int!(i64, u128, i);
            from_int!(i64, i8, i);
            from_int!(i64, i16, i);
            from_int!(i64, i32, i);
            from_int!(i64, i64, i);
            from_int!(i64, i128, i);
        }

        #[test]
        fn from_i128(i: i128) {
            from_int!(i128, u8, i);
            from_int!(i128, u16, i);
            from_int!(i128, u32, i);
            from_int!(i128, u64, i);
            from_int!(i128, u128, i);
            from_int!(i128, i8, i);
            from_int!(i128, i16, i);
            from_int!(i128, i32, i);
            from_int!(i128, i64, i);
            from_int!(i128, i128, i);
        }

        #[test]
        fn from_u8(i: u8) {
            from_int!(u8, u8, i);
            from_int!(u8, u16, i);
            from_int!(u8, u32, i);
            from_int!(u8, u64, i);
            from_int!(u8, u128, i);
            from_int!(u8, i8, i);
            from_int!(u8, i16, i);
            from_int!(u8, i32, i);
            from_int!(u8, i64, i);
            from_int!(u8, i128, i);
        }

        #[test]
        fn from_u16(i: u16) {
            from_int!(u16, u8, i);
            from_int!(u16, u16, i);
            from_int!(u16, u32, i);
            from_int!(u16, u64, i);
            from_int!(u16, u128, i);
            from_int!(u16, i8, i);
            from_int!(u16, i16, i);
            from_int!(u16, i32, i);
            from_int!(u16, i64, i);
            from_int!(u16, i128, i);
        }

        #[test]
        fn from_u32(i: u32) {
            from_int!(u32, u8, i);
            from_int!(u32, u16, i);
            from_int!(u32, u32, i);
            from_int!(u32, u64, i);
            from_int!(u32, u128, i);
            from_int!(u32, i8, i);
            from_int!(u32, i16, i);
            from_int!(u32, i32, i);
            from_int!(u32, i64, i);
            from_int!(u32, i128, i);
        }

        #[test]
        fn from_u64(i: u64) {
            from_int!(u64, u8, i);
            from_int!(u64, u16, i);
            from_int!(u64, u32, i);
            from_int!(u64, u64, i);
            from_int!(u64, u128, i);
            from_int!(u64, i8, i);
            from_int!(u64, i16, i);
            from_int!(u64, i32, i);
            from_int!(u64, i64, i);
            from_int!(u64, i128, i);
        }

        #[test]
        fn from_u128(i: u128) {
            from_int!(u128, u8, i);
            from_int!(u128, u16, i);
            from_int!(u128, u32, i);
            from_int!(u128, u64, i);
            from_int!(u128, u128, i);
            from_int!(u128, i8, i);
            from_int!(u128, i16, i);
            from_int!(u128, i32, i);
            from_int!(u128, i64, i);
            from_int!(u128, i128, i);
        }
    }
}
