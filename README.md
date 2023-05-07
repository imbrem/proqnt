# proqnt
A **pro**nounceable **quint**uplet, or *proquint*, is a pronounceable 5-letter string encoding a unique 16-bit integer.

Proquints may be used to encode binary data such as IP addresses, public keys, and UUIDs in a more human-friendly way.
For more information, check out the [specification](https://arxiv.org/html/0901.4016)

## Basic Usage

```rust
# use std::net::Ipv4Addr;
use proqnt::{FromProquints, IntoProquints, Proquint};
assert_eq!(
    format!("{}", Ipv4Addr::new(127, 0, 0, 1).proquint_encode()),
    "lusab-babad"
);
assert!(
    Ipv4Addr::new(127, 0, 0, 1).proquint_digits().eq([
        u16::parse_proquints("lusab").unwrap(),
        u16::parse_proquints("babad").unwrap()
    ].into_iter())
);
assert_eq!(
    format!("{}", [127u8, 0, 0, 1].proquint_encode()),
    "lusab-babad"
);
assert!(
    Ipv4Addr::new(127, 0, 0, 1).proquint_encode().into_iter().eq([
        "lusab".parse::<Proquint>().unwrap(),
        "babad".parse::<Proquint>().unwrap()
    ].into_iter())
);
// NOTE: [127, 0, 0, 1] will yield an array of i32, which will give the wrong result!
```