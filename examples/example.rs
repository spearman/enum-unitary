extern crate enum_unitary;
use enum_unitary::enum_unitary;

enum_unitary!{
  #[derive(Debug, PartialEq)]
  pub enum Myenum {
    A, B, C
  }
}

fn main() {
  use enum_unitary::{FromPrimitive, ToPrimitive};

  assert_eq!(enum_iterator::cardinality::<Myenum>(), 3);
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
  assert_eq!(enum_iterator::first::<Myenum>().unwrap(), Myenum::A);
  assert_eq!(enum_iterator::last::<Myenum>().unwrap(),  Myenum::C);
  let mut i = enum_iterator::all::<Myenum>();
  assert_eq!(i.next(), Some (Myenum::A));
  assert_eq!(i.next(), Some (Myenum::B));
  assert_eq!(i.next(), Some (Myenum::C));
  assert_eq!(i.next(), None);
  assert_eq!(enum_iterator::next (&Myenum::A), Some (Myenum::B));
  assert_eq!(enum_iterator::previous (&Myenum::A), None);
  assert_eq!(enum_iterator::next (&Myenum::B), Some (Myenum::C));
  assert_eq!(enum_iterator::previous (&Myenum::B), Some (Myenum::A));
  assert_eq!(enum_iterator::next (&Myenum::C), None);
  assert_eq!(enum_iterator::previous (&Myenum::C), Some (Myenum::B));
}
