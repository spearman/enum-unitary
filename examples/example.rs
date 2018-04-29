#![feature(const_fn)]

#[macro_use] extern crate enum_unitary;

enum_unitary!{
  pub enum Myenum (MyenumVariants) {
    A, B, C
  }
}

fn main() {
  use enum_unitary::{EnumUnitary, Bounded, FromPrimitive, ToPrimitive};

  assert_eq!(Myenum::count(), 3);
  assert_eq!(Myenum::count_variants(), 3);
  assert_eq!(Into::<usize>::into (Myenum::A), 0);
  assert_eq!(Into::<usize>::into (Myenum::B), 1);
  assert_eq!(Into::<usize>::into (Myenum::C), 2);
  assert_eq!(Some (Myenum::A), Myenum::from_usize (0));
  assert_eq!(Some (Myenum::B), Myenum::from_usize (1));
  assert_eq!(Some (Myenum::C), Myenum::from_usize (2));
  assert_eq!(None, Myenum::from_usize (3));
  assert_eq!(Some (0), Myenum::A.to_usize());
  assert_eq!(Some (1), Myenum::B.to_usize());
  assert_eq!(Some (2), Myenum::C.to_usize());
  assert_eq!(Myenum::min_value(), Myenum::A);
  assert_eq!(Myenum::max_value(), Myenum::C);
  let mut i = Myenum::iter_variants();
  assert_eq!(i.next(), Some (Myenum::A));
  assert_eq!(i.next(), Some (Myenum::B));
  assert_eq!(i.next(), Some (Myenum::C));
  assert_eq!(i.next(), None);
  assert_eq!(Myenum::A.next_variant(), Some (Myenum::B));
  assert_eq!(Myenum::A.prev_variant(), None);
  assert_eq!(Myenum::B.next_variant(), Some (Myenum::C));
  assert_eq!(Myenum::B.prev_variant(), Some (Myenum::A));
  assert_eq!(Myenum::C.next_variant(), None);
  assert_eq!(Myenum::C.prev_variant(), Some (Myenum::B));
}
