//! `EnumUnitary` trait and `enum_unitary!` macro.
//!
//! [Repository](https://github.com/spearman/enum-unitary)

extern crate num_traits;

pub use enum_iterator;
pub use num_traits::{FromPrimitive, ToPrimitive};

//
//  trait EnumUnitary
//
/// A collection of constraints for unitary enums.
///
/// See the `enum_unitary!` macro for defining instances of this trait.
// TODO: expose more constraints ?
pub trait EnumUnitary : Clone
  // NB: as of Rust 1.22, the *last* of the following `Into` constraints
  // seems to be chosen by default and using `.into` for one of the other
  // types requires using disambiguation syntax; we choose `usize` here since
  // it is commonly used as an index type.
  + Into <i64> + Into <u64> + Into <isize> + Into <usize>
  + ToPrimitive + FromPrimitive + enum_iterator::Sequence
{ }

//
//  enum_unitary!
//
/// Derive and implement extra traits for "unitary" enums (i.e. enums where
/// variants do not have payloads):
///
/// - implements `num_traits` traits `Bounded`, `ToPrimitive`, `FromPrimitive`
/// - implements primitive conversion types
///
/// Note that `Clone` is also automatically derived so there will be an error if
/// it is given in a derive attribute.
///
/// Currently explicit discriminators are not allowed: enum variants will be
/// numbered consecutively starting from `0`.
///
/// # Examples
///
/// ```
/// use enum_unitary::{enum_unitary, EnumUnitary, FromPrimitive,
///   ToPrimitive};
///
/// fn main () {
///   enum_unitary! {
///     #[derive(Debug, PartialEq)]
///     pub enum E {
///       A, B, C
///     }
///   }
///   assert_eq!(enum_iterator::cardinality::<E>(), 3);
///   assert_eq!(Into::<usize>::into (E::A), 0);
///   assert_eq!(Into::<usize>::into (E::B), 1);
///   assert_eq!(Into::<usize>::into (E::C), 2);
///   assert_eq!(enum_iterator::first::<E>().unwrap(), E::A);
///   assert_eq!(enum_iterator::last::<E>().unwrap(),  E::C);
///   let mut i = enum_iterator::all::<E>();
///   assert_eq!(i.next(), Some (E::A));
///   assert_eq!(i.next(), Some (E::B));
///   assert_eq!(i.next(), Some (E::C));
///   assert_eq!(i.next(), None);
///   assert_eq!(enum_iterator::next (&E::A), Some (E::B));
///   assert_eq!(enum_iterator::previous (&E::A), None);
///   assert_eq!(enum_iterator::next (&E::B), Some (E::C));
///   assert_eq!(enum_iterator::previous (&E::B), Some (E::A));
///   assert_eq!(enum_iterator::next (&E::C), None);
///   assert_eq!(enum_iterator::previous (&E::C), Some (E::B));
/// }
/// ```

#[macro_export]
macro_rules! enum_unitary {
  //
  //  private
  //
  (
    $(#[$attrs:meta])*
    enum $enum:ident { $($variant:ident),* }
  ) => {
    $(#[$attrs])*
    #[derive(Clone, $crate::enum_iterator::Sequence)]
    enum $enum {
      $($variant),*
    }

    impl From <$enum> for isize {
      fn from (x : $enum) -> Self {
        x as isize
      }
    }
    impl From <$enum> for usize {
      fn from (x : $enum) -> Self {
        x as usize
      }
    }
    impl From <$enum> for i64 {
      fn from (x : $enum) -> Self {
        x as i64
      }
    }
    impl From <$enum> for u64 {
      fn from (x : $enum) -> Self {
        x as u64
      }
    }

    impl $crate::FromPrimitive for $enum {
      fn from_i64 (x : i64) -> Option <Self> {
        const VARIANTS : [$enum; $crate::enum_iterator::cardinality::<$enum>()]
          = [$($enum::$variant),*];
        VARIANTS.get (x as usize).cloned()
      }
      fn from_u64 (x : u64) -> Option <Self> {
        const VARIANTS : [$enum; $crate::enum_iterator::cardinality::<$enum>()]
          = [$($enum::$variant),*];
        VARIANTS.get (x as usize).cloned()
      }
    }

    impl $crate::ToPrimitive for $enum {
      fn to_i64 (&self) -> Option <i64> {
        Some (self.clone() as i64)
      }
      fn to_u64 (&self) -> Option <u64> {
        Some (self.clone() as u64)
      }
    }

    impl $crate::EnumUnitary for $enum { }
  };

  //
  //  public
  //
  (
    $(#[$attrs:meta])*
    pub enum $enum:ident { $($variant:ident),* }
  ) => {
    $(#[$attrs])*
    #[derive(Clone, $crate::enum_iterator::Sequence)]
    pub enum $enum {
      $($variant),*
    }

    impl From <$enum> for isize {
      fn from (x : $enum) -> Self {
        x as isize
      }
    }
    impl From <$enum> for usize {
      fn from (x: $enum) -> Self {
        x as usize
      }
    }
    impl From <$enum> for i64 {
      fn from (x : $enum) -> Self {
        x as i64
      }
    }
    impl From <$enum> for u64 {
      fn from (x: $enum) -> Self {
        x as u64
      }
    }

    impl $crate::FromPrimitive for $enum {
      fn from_i64 (x : i64) -> Option <Self> {
        const VARIANTS : [$enum; $crate::enum_iterator::cardinality::<$enum>()]
          = [$($enum::$variant),*];
        VARIANTS.get (x as usize).cloned()
      }
      fn from_u64 (x: u64) -> Option <Self> {
        const VARIANTS : [$enum; $crate::enum_iterator::cardinality::<$enum>()]
          = [$($enum::$variant),*];
        VARIANTS.get (x as usize).cloned()
      }
    }

    impl $crate::ToPrimitive for $enum {
      fn to_i64 (&self) -> Option <i64> {
        Some (self.clone() as i64)
      }
      fn to_u64 (&self) -> Option <u64> {
        Some (self.clone() as u64)
      }
    }

    impl $crate::EnumUnitary for $enum { }
  };
}

//
//  example enum
//
#[cfg(doc)]
enum_unitary!{
  /// This is an example enum generated by `enum_unitary!`
  pub enum Example {
    A, B, C
  }
}

//
//  mod tests
//
#[cfg(test)]
mod tests {
  #[test]
  fn test_unit() {
    use crate::{FromPrimitive, ToPrimitive};

    // private enum
    enum_unitary!{
      #[derive(Debug, PartialEq)]
      enum Myenum1 {
        A, B, C
      }
    }
    assert_eq!(enum_iterator::cardinality::<Myenum1>(), 3);
    assert_eq!(Into::<usize>::into (Myenum1::A), 0);
    assert_eq!(Into::<usize>::into (Myenum1::B), 1);
    assert_eq!(Into::<usize>::into (Myenum1::C), 2);
    assert_eq!(Some (Myenum1::A), Myenum1::from_usize (0));
    assert_eq!(Some (Myenum1::B), Myenum1::from_usize (1));
    assert_eq!(Some (Myenum1::C), Myenum1::from_usize (2));
    assert_eq!(None, Myenum1::from_usize (3));
    assert_eq!(Some (0), Myenum1::A.to_usize());
    assert_eq!(Some (1), Myenum1::B.to_usize());
    assert_eq!(Some (2), Myenum1::C.to_usize());
    assert_eq!(enum_iterator::first::<Myenum1>().unwrap(), Myenum1::A);
    assert_eq!(enum_iterator::last::<Myenum1>().unwrap(), Myenum1::C);
    let mut i = enum_iterator::all::<Myenum1>();
    assert_eq!(i.next(), Some (Myenum1::A));
    assert_eq!(i.next(), Some (Myenum1::B));
    assert_eq!(i.next(), Some (Myenum1::C));
    assert_eq!(i.next(), None);
    assert_eq!(enum_iterator::next (&Myenum1::A), Some (Myenum1::B));
    assert_eq!(enum_iterator::previous (&Myenum1::A), None);
    assert_eq!(enum_iterator::next (&Myenum1::B), Some (Myenum1::C));
    assert_eq!(enum_iterator::previous (&Myenum1::B), Some (Myenum1::A));
    assert_eq!(enum_iterator::next (&Myenum1::C), None);
    assert_eq!(enum_iterator::previous (&Myenum1::C), Some (Myenum1::B));

    // public enum
    enum_unitary!{
      #[derive(Debug, PartialEq)]
      pub enum Myenum2 {
        A, B, C
      }
    }
    assert_eq!(enum_iterator::cardinality::<Myenum2>(), 3);
    assert_eq!(Into::<usize>::into (Myenum2::A), 0);
    assert_eq!(Into::<usize>::into (Myenum2::B), 1);
    assert_eq!(Into::<usize>::into (Myenum2::C), 2);
    assert_eq!(Some (Myenum2::A), Myenum2::from_usize (0));
    assert_eq!(Some (Myenum2::B), Myenum2::from_usize (1));
    assert_eq!(Some (Myenum2::C), Myenum2::from_usize (2));
    assert_eq!(None, Myenum2::from_usize (3));
    assert_eq!(Some (0), Myenum2::A.to_usize());
    assert_eq!(Some (1), Myenum2::B.to_usize());
    assert_eq!(Some (2), Myenum2::C.to_usize());
    assert_eq!(enum_iterator::first::<Myenum2>().unwrap(), Myenum2::A);
    assert_eq!(enum_iterator::last::<Myenum2>().unwrap(), Myenum2::C);
    let mut i = enum_iterator::all::<Myenum2>();
    assert_eq!(i.next(), Some (Myenum2::A));
    assert_eq!(i.next(), Some (Myenum2::B));
    assert_eq!(i.next(), Some (Myenum2::C));
    assert_eq!(i.next(), None);
    assert_eq!(enum_iterator::next (&Myenum2::A), Some (Myenum2::B));
    assert_eq!(enum_iterator::previous (&Myenum2::A), None);
    assert_eq!(enum_iterator::next (&Myenum2::B), Some (Myenum2::C));
    assert_eq!(enum_iterator::previous (&Myenum2::B), Some (Myenum2::A));
    assert_eq!(enum_iterator::next (&Myenum2::C), None);
    assert_eq!(enum_iterator::previous (&Myenum2::C), Some (Myenum2::B));

    // private singleton enum
    enum_unitary!{
      #[derive(Debug, PartialEq)]
      enum Myenum3 {
        X
      }
    }
    assert_eq!(enum_iterator::cardinality::<Myenum3>(), 1);
    assert_eq!(Into::<usize>::into (Myenum3::X), 0);
    assert_eq!(Some (Myenum3::X), Myenum3::from_usize (0));
    assert_eq!(None, Myenum3::from_usize (1));
    assert_eq!(Some (0), Myenum3::X.to_usize());
    assert_eq!(enum_iterator::first::<Myenum3>().unwrap(), Myenum3::X);
    assert_eq!(enum_iterator::last::<Myenum3>().unwrap(), Myenum3::X);
    let mut i = enum_iterator::all::<Myenum3>();
    assert_eq!(i.next(), Some (Myenum3::X));
    assert_eq!(i.next(), None);
    assert_eq!(enum_iterator::next (&Myenum3::X), None);
    assert_eq!(enum_iterator::previous (&Myenum3::X), None);

    // public singleton enum
    enum_unitary!{
      #[derive(Debug, PartialEq)]
      pub enum Myenum4 {
        X
      }
    }
    assert_eq!(enum_iterator::cardinality::<Myenum4>(), 1);
    assert_eq!(Into::<usize>::into (Myenum4::X), 0);
    assert_eq!(Some (Myenum4::X), Myenum4::from_usize (0));
    assert_eq!(None, Myenum4::from_usize (1));
    assert_eq!(Some (0), Myenum4::X.to_usize());
    assert_eq!(enum_iterator::first::<Myenum4>().unwrap(), Myenum4::X);
    assert_eq!(enum_iterator::last::<Myenum4>().unwrap(), Myenum4::X);
    let mut i = enum_iterator::all::<Myenum4>();
    assert_eq!(i.next(), Some (Myenum4::X));
    assert_eq!(i.next(), None);
    assert_eq!(enum_iterator::next (&Myenum4::X), None);
    assert_eq!(enum_iterator::previous (&Myenum4::X), None);

    // private nullary enum
    enum_unitary!{
      #[derive(Debug, PartialEq)]
      enum Myenum5 { }
    }
    assert_eq!(enum_iterator::cardinality::<Myenum5>(), 0);
    assert_eq!(None, Myenum5::from_usize (0));
    assert_eq!(enum_iterator::first::<Myenum5>(), None);
    assert_eq!(enum_iterator::last::<Myenum5>(), None);
    let mut i = enum_iterator::all::<Myenum5>();
    assert_eq!(i.next(), None);

    // public nullary enum
    enum_unitary!{
      #[derive(Debug, PartialEq)]
      pub enum Myenum6 { }
    }
    assert_eq!(enum_iterator::cardinality::<Myenum6>(), 0);
    assert_eq!(None, Myenum6::from_usize (0));
    assert_eq!(enum_iterator::first::<Myenum6>(), None);
    assert_eq!(enum_iterator::last::<Myenum6>(), None);
    let mut i = enum_iterator::all::<Myenum6>();
    assert_eq!(i.next(), None);
  }
} // end mod tests
