# proqnt

[![Version](https://img.shields.io/crates/v/proqnt)](https://crates.io/crates/proqnt)
[![Documentation](https://img.shields.io/docsrs/proqnt)](https://docs.rs/proqnt/latest/proqnt/)
[![Build](https://img.shields.io/github/actions/workflow/status/imbrem/proqnt/rust.yml)](https://github.com/imbrem/proqnt/actions)
[![License](https://img.shields.io/crates/l/proqnt/0.1.0)](https://crates.io/crates/proqnt)
[![Downloads](https://img.shields.io/crates/d/proqnt)](https://crates.io/crates/proqnt)

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