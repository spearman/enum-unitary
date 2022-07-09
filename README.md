# `enum-unitary`

> Trait and macro for unitary enums

[Documentation](https://docs.rs/enum-unitary)

*NOTE*: this crate is more or less obsolete now that
[`enum_iterator` v1.0](https://crates.io/crates/enum-iterator) exists

The `EnumUnitary` trait carries a number of constraints for primitive
conversions and limits and iterating over variants of a unitary enum (i.e. enum
variants do not have payloads).

The `enum_unitary!` macro defines a new enum implementing `EnumUnitary` and
required traits.

## Usage

For the macro to derive `IntoEnumIterator`, the `enum-iterator` crate must also
be added to `Cargo.toml`:
```toml
enum-iterator = "0.7"
enum-unitary = "0.4"
```

Define a unitary enum:
```rust
use enum_unitary::{enum_unitary, EnumUnitary, Bounded};
enum_unitary! {
  #[derive(Debug, PartialEq)]
  pub enum E {
    A, B, C
  }
}
assert_eq!(E::count(), 3);
assert_eq!(Into::<usize>::into (E::A), 0);
assert_eq!(Into::<usize>::into (E::B), 1);
assert_eq!(Into::<usize>::into (E::C), 2);
assert_eq!(E::min_value(), E::A);
assert_eq!(E::max_value(), E::C);
let mut i = E::iter_variants();
assert_eq!(i.next(), Some (E::A));
assert_eq!(i.next(), Some (E::B));
assert_eq!(i.next(), Some (E::C));
assert_eq!(i.next(), None);
assert_eq!(E::A.next_variant(), Some (E::B));
assert_eq!(E::A.prev_variant(), None);
assert_eq!(E::B.next_variant(), Some (E::C));
assert_eq!(E::B.prev_variant(), Some (E::A));
assert_eq!(E::C.next_variant(), None);
assert_eq!(E::C.prev_variant(), Some (E::B));
```
