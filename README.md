# `enum-unitary`

*Deprecation notice*: this crate is more or less deprecated as the
`enum-iterator` and `num-derive` crates provide procedural macros to implement
the required traits. The only thing this crate provides are `Into` for `usize`,
`isize`, `i64`, and `u64`, which are trivial to implement. See also the
`num_enum` crate which will safely derive `Into` for enums with `#[repr(T)]`
attributes. `strum` and `strum_macros` also provide procedural macros and traits
for enum iterators, variant counts, and conversions.

> Trait and macro for unitary enums

[Documentation](https://docs.rs/enum-unitary)

The `EnumUnitary` trait carries a number of constraints for primitive
conversions iterating over variants of a unitary enum (i.e. enum variants do not
have payloads).

The `enum_unitary!` macro defines a new enum implementing `EnumUnitary` and
required traits.

## Usage

For the macro to derive `Sequence`, the `enum-iterator` crate must also be added
to `Cargo.toml`:
```toml
enum-iterator = "1.0"
enum-unitary = "0.5"
```

Define a unitary enum:
```rust
use enum_unitary::{enum_unitary, EnumUnitary, FromPrimitive, ToPrimitive};

enum_unitary! {
  #[derive(Debug, PartialEq)]
  pub enum E {
    A, B, C
  }
}

assert_eq!(enum_iterator::cardinality::<E>(), 3);
assert_eq!(Into::<usize>::into (E::A), 0);
assert_eq!(Into::<usize>::into (E::B), 1);
assert_eq!(Into::<usize>::into (E::C), 2);
assert_eq!(enum_iterator::first::<E>().unwrap(), E::A);
assert_eq!(enum_iterator::last::<E>().unwrap(),  E::C);
let mut i = enum_iterator::all::<E>();
assert_eq!(i.next(), Some (E::A));
assert_eq!(i.next(), Some (E::B));
assert_eq!(i.next(), Some (E::C));
assert_eq!(i.next(), None);
assert_eq!(enum_iterator::next (&E::A), Some (E::B));
assert_eq!(enum_iterator::previous (&E::A), None);
assert_eq!(enum_iterator::next (&E::B), Some (E::C));
assert_eq!(enum_iterator::previous (&E::B), Some (E::A));
assert_eq!(enum_iterator::next (&E::C), None);
assert_eq!(enum_iterator::previous (&E::C), Some (E::B));
```
