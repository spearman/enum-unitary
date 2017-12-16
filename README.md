# `enum-unitary`

> Trait and macro for unitary enums

The `EnumUnitary` trait carries a number of constraints and exposes some
methods for working with variants.

The `enum_unitary!` macro defines new enum implementing `EnumUnitary` and an
additional const function `count` returning the number of variants in the enum.

## Usage

Using the `enum_unitary!` macro requires external dependencies:

```toml
[dependencies]
num = "0.1.*"
macro-attr = "0.2.*"
enum_derive = "0.1.*"
```

and the following directives:

```rust
#![feature(const_fn)]

extern crate num;
#[macro_use] extern crate macro_attr;
#[macro_use] extern crate enum_derive;
#[macro_use] extern crate enum_unitary;
```

Define a unitary enum:

```rust
enum_unitary! {
  pub enum E (EVariants) {
    A, B, C
  }
}
use num::Bounded;
use enum_unitary::EnumUnitary;
assert_eq!(E::count(), 3);
assert_eq!(Into::<usize>::into (E::A), 0);
assert_eq!(Into::<usize>::into (E::A), 1);
assert_eq!(Into::<usize>::into (E::A), 2);
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
