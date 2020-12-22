//!
//! GetField reference (like a member pointer to non-static data field in C++) for Rust￼
//!
//! # Examples
//!
//! Subfield of type `U` which is contained by `T` can be obtained via `FieldRef<T, U>`.
//!
//! ```
//! use field_ref::{GetField, GetFieldMut, field_ref_of};
//!
//! struct Foo(u32, u32, f64);
//! struct Bar {
//!     foo: Foo,
//!     x: u32,
//! }
//!
//! # fn main() {
//! let fr1 = field_ref_of!(Bar => x);
//! let fr2 = field_ref_of!(Bar => foo);
//! let fr3 = field_ref_of!(Foo => 1);
//! let fr4 = field_ref_of!(Bar => foo => 0);
//!
//! let mut bar = Bar { foo: Foo(10, 20, 0.5), x: 30 };
//!
//! assert_eq!(bar.get_field(fr1), &30);
//! assert_eq!(fr1.get(&bar), &30);
//!
//! *bar.get_field_mut(fr1) = 100;
//! assert_eq!(bar.x, 100);
//!
//! *fr1.get_mut(&mut bar) = 200;
//! assert_eq!(bar.x, 200);
//!
//! assert_eq!(bar.get_field(fr2.chain(fr3)), &20);
//! assert_eq!(bar.get_field(fr4), &10);
//! # }
//! ```
//!
//! Enum field of type `T` can be obtain as `Option<&T>` via `OptionFieldRef`.
//! Other field such as struct field of type `T` can also be obtain as `Option<&T>` via `OptionFieldRef`.
//!
//! ```
//! use field_ref::{GetField, GetFieldMut, OptionFieldRef, opt_field_ref_of};
//!
//! struct Foo {
//!     x: i32,
//!     y: f64,
//! }
//!
//! enum E1 {
//!     A(i32),
//!     B(i32, Foo),
//! }
//!
//! enum E2 {
//!     X(E1),
//!     Y,
//! }
//!
//! # fn main() {
//! let fr1 = opt_field_ref_of!(E1::A{0});
//! let fr2 = opt_field_ref_of!(E2::X{0} & E1::B{1} => y);
//! let fr3 = opt_field_ref_of!(Foo => x);
//!
//! let e1_1 = E1::A(10);
//! let e1_2 = E1::B(20, Foo{ x: 25, y: 2.5 });
//! let e2_1 = E2::X(E1::B(10, Foo{ x: 30, y: 3.5 }));
//! let e2_2 = E2::Y;
//!
//! let mut foo = Foo{ x: 40, y: 4.5 };
//!
//! assert_eq!(e1_1.try_get_field(fr1), Some(&10));
//! assert_eq!(e1_2.try_get_field(fr1), None);
//!
//! assert_eq!(e2_1.try_get_field(fr2), Some(&3.5));
//! assert_eq!(e2_2.try_get_field(fr2), None);
//!
//! assert_eq!(foo.try_get_field(fr3), Some(&40));
//! *foo.try_get_field_mut(fr3).unwrap() = 50;
//! assert_eq!(foo.x, 50)
//! # }
//! ```
//!

use std::marker::PhantomData;
use std::cmp::{Eq, PartialEq, Ord, PartialOrd, Ordering};


///
/// A reference to field of type `U` (recursively) contained by an object of type `T`.
///
pub struct FieldRef<T, U> {
    offset: usize,
    phantom: PhantomData<(T, U)>,
}

impl<T, U> FieldRef<T, U> {
    /// Creates a new `FieldRef` with offset bytes from the first byte of an object of type `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use field_ref::FieldRef;
    ///
    /// #[repr(C)]
    /// struct Foo(u32, u32);
    ///
    /// # fn main() {
    /// // references Foo.1
    /// let fr = unsafe { FieldRef::<Foo, u32>::from_offset(4) };
    /// let foo = Foo(10, 20);
    /// assert_eq!(fr.get(&foo), &20);
    /// # }
    /// ```
    pub unsafe fn from_offset(offset: usize) -> Self {
        Self { offset, phantom: PhantomData }
    }

    /// Creates a new `FieldRef` from a reference to concrete object of type `T` and a reference to concrete field of type `U`.
    ///
    /// # Examples
    ///
    /// ```
    /// use field_ref::FieldRef;
    ///
    /// struct Foo(u32, u32, f64);
    ///
    /// # fn main() {
    /// let foo1 = Foo(10, 20, 0.5);
    /// let foo2 = Foo(30, 40, 1.5);
    /// let fr = unsafe { FieldRef::from_pointers(&foo1, &foo1.1) };
    /// assert_eq!(fr.get(&foo2), &40);
    /// # }
    /// ```
    pub unsafe fn from_pointers(obj: *const T, field: *const U) -> Self {
        Self::from_offset(field as usize - obj as usize)
    }

    /// Creates a new `FieldRef` from a pointer to concrete object of type `T` and a pointer to concrete field of type `U`.
    ///
    /// # Examples
    ///
    /// ```
    /// use field_ref::FieldRef;
    ///
    /// struct Foo(u32, u32, f64);
    ///
    /// # fn main() {
    /// let foo1 = Foo(10, 20, 0.5);
    /// let foo2 = Foo(30, 40, 1.5);
    /// let fr = unsafe { FieldRef::from_references(&foo1, &foo1.1) };
    /// assert_eq!(fr.get(&foo2), &40);
    /// # }
    /// ```
    pub unsafe fn from_references(obj: &T, field: &U) -> Self {
        Self::from_pointers(obj, field)
    }

    /// Get the offset of target field.
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Get a reference of value in an object to which `FieldRef` refers.
    ///
    /// # Examples
    ///
    /// ```
    /// use field_ref::field_ref_of;
    ///
    /// struct Foo(u32, u32, f64);
    ///
    /// # fn main() {
    /// let fr = field_ref_of!(Foo => 1);
    /// let foo = Foo(10, 20, 0.5);
    /// assert_eq!(fr.get(&foo), &20);
    /// # }
    /// ```
    pub fn get<'a, 'b>(&'a self, obj: &'b T) -> &'b U {
        let addr = obj as *const _ as usize + self.offset;
        unsafe { &*(addr as *const U) }
    }

    #[deprecated(note = "Use `get` instead")]
    pub fn get_ref<'a, 'b>(&'a self, obj: &'b T) -> &'b U {
        self.get(obj)
    }

    /// Get a mutable reference of value in an object to which `FieldRef` refers.
    ///
    /// # Examples
    ///
    /// ```
    /// use field_ref::field_ref_of;
    ///
    /// struct Foo(u32, u32, f64);
    ///
    /// # fn main() {
    /// let fr = field_ref_of!(Foo => 1);
    /// let mut foo = Foo(10, 20, 0.5);
    /// *fr.get_mut(&mut foo) = 30;
    /// assert_eq!(foo.1, 30);
    /// # }
    /// ```
    pub fn get_mut<'a, 'b>(&'a self, obj: &'b mut T) -> &'b mut U {
        let addr = obj as *mut _ as usize + self.offset;
        unsafe { &mut *(addr as *mut U) }
    }

    /// Chains two field references.
    ///
    /// # Examples
    ///
    /// ```
    /// use field_ref::field_ref_of;
    ///
    /// struct Foo(u32, u32, f64);
    /// struct Bar {
    ///     foo: Foo,
    ///     x: u32,
    /// }
    ///
    /// # fn main() {
    /// let fr1 = field_ref_of!(Bar => foo);
    /// let fr2 = field_ref_of!(Foo => 1);
    /// let bar = Bar { foo: Foo(10, 20, 0.5), x: 30 };
    /// assert_eq!(fr1.chain(fr2).get(&bar), &20);
    /// # }
    /// ```
    pub fn chain<V>(&self, fr: FieldRef<U, V>) -> FieldRef<T, V> {
        unsafe { FieldRef::<T, V>::from_offset(self.offset + fr.offset) }
    }

    /// Convert `FieldRef<T, U>` into an instance of trait `OptionFieldRef<'x, Input = T, Output = U>`.
    pub fn as_opt_field_ref(&self) -> FieldRefAsOptionFieldRef<T, U> {
        FieldRefAsOptionFieldRef(*self)
    }
}

impl<T, U> Clone for FieldRef<T, U> {
    fn clone(&self) -> Self {
        Self { offset: self.offset, phantom: PhantomData }
    }
}

impl<T, U> Copy for FieldRef<T, U> {}

impl<T, U> std::fmt::Debug for FieldRef<T, U> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "FieldRef {{ offset: {} }}", self.offset)
    }
}

impl<T, U> PartialEq for FieldRef<T, U> {
    fn eq(&self, other: &Self) -> bool {
        self.offset == other.offset
    }
}

impl<T, U> Eq for FieldRef<T, U> {}

impl<T, U> PartialOrd for FieldRef<T, U> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.offset.partial_cmp(&other.offset)
    }
}

impl<T, U> Ord for FieldRef<T, U> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.offset.cmp(&other.offset)
    }
}


///
/// A reference to field of type `Input` (recursively) contained by an object of type `Output`
/// and that may fail dereference.
///
pub trait OptionFieldRef<'x> where Self: Copy {
    type Input;
    type Output;

    /// Get a reference of value in an object to which `OptionFieldRef` refers.
    ///
    /// # Examples
    ///
    /// ```
    /// use field_ref::{OptionFieldRef, opt_field_ref_of};
    ///
    /// enum E {
    ///     A(i32, char),
    ///     B(i32)
    /// }
    ///
    /// # fn main() {
    /// let fr = opt_field_ref_of!(E::A{0});
    /// let e1 = E::A(10, 'a');
    /// let e2 = E::B(20);
    /// assert_eq!(fr.get(&e1), Some(&10));
    /// assert_eq!(fr.get(&e2), None);
    /// # }
    /// ```
    fn get<'a>(&'a self, obj: &'x Self::Input) -> Option<&'x Self::Output>;

    /// Get a mutable reference of value in an object to which `OptionFieldRef` refers.
    ///
    /// # Examples
    ///
    /// ```
    /// use field_ref::{OptionFieldRef, opt_field_ref_of};
    ///
    /// #[derive(Debug, Eq, PartialEq)]
    /// enum E {
    ///     A(i32, char),
    ///     B(i32)
    /// }
    ///
    /// # fn main() {
    /// let fr = opt_field_ref_of!(E::B{0});
    /// let mut e = E::B(10);
    /// *fr.get_mut(&mut e).unwrap() = 20;
    /// assert_eq!(e, E::B(20));
    /// # }
    /// ```
    fn get_mut<'a>(&'a self, obj: &'x mut Self::Input) -> Option<&'x mut Self::Output>;

    /// Chains two field references.
    ///
    /// # Examples
    ///
    /// ```
    /// use field_ref::{OptionFieldRef, opt_field_ref_of};
    ///
    /// enum E1 {
    ///     A(i32),
    ///     B(i32, char),
    /// }
    ///
    /// enum E2 {
    ///     X(E1),
    ///     Y,
    /// }
    ///
    /// # fn main() {
    /// let fr1 = opt_field_ref_of!(E2::X{0});
    /// let fr2 = opt_field_ref_of!(E1::A{0});
    /// let e2 = E2::X(E1::A(10));
    /// assert_eq!(fr1.chain(fr2).get(&e2), Some(&10));
    /// # }
    /// ```
    fn chain<FR, R: 'x>(&self, fr: FR) -> OptionFieldRefChain<Self, FR>
    where
        FR: OptionFieldRef<'x, Input = Self::Output, Output = R> + Copy
    {
        OptionFieldRefChain(*self, fr)
    }
}

///
/// A `OptionFieldRef` references a field within an enum constant.
///
pub struct EnumFieldRef<E, T> {
    extractor: fn(&E) -> Option<&T>,
    mut_extractor: fn(&mut E) -> Option<&mut T>,
}

impl<E, T> EnumFieldRef<E, T> {
    /// Creates a new `EnumFieldRef` from a field extracting function and a mutable field extracting function.
    pub fn new(extractor: fn(&E) -> Option<&T>, mut_extractor: fn(&mut E) -> Option<&mut T>) -> Self {
        Self { extractor, mut_extractor }
    }
}

impl<'x, E: 'x, T: 'x> OptionFieldRef<'x> for EnumFieldRef<E, T> {
    type Input = E;
    type Output = T;

    fn get<'a>(&'a self, e: &'x Self::Input) -> Option<&'x Self::Output> {
        (self.extractor)(e)
    }

    fn get_mut<'a>(&'a self, e: &'x mut Self::Input) -> Option<&'x mut Self::Output> {
        (self.mut_extractor)(e)
    }
}

impl<E, T> Clone for EnumFieldRef<E, T> {
    fn clone(&self) -> Self {
        Self { extractor: self.extractor, mut_extractor: self.mut_extractor }
    }
}

impl<E, T> Copy for EnumFieldRef<E, T> {}

///
/// A `OptionFieldRef` which chains two `OptionFieldRef`s.
///
pub struct OptionFieldRefChain<FR1: Copy, FR2: Copy>(FR1, FR2);

impl<'x, T: 'x, U: 'x, V: 'x, FR1, FR2> OptionFieldRef<'x> for OptionFieldRefChain<FR1, FR2> where
    FR1: OptionFieldRef<'x, Input = T, Output = U>,
    FR2: OptionFieldRef<'x, Input = U, Output = V>,
{
    type Input = T;
    type Output = V;

    fn get<'a>(&'a self, obj: &'x Self::Input) -> Option<&'x Self::Output> {
        self.0.get(obj).and_then(|y| self.1.get(y))
    }

    fn get_mut<'a>(&'a self, obj: &'x mut Self::Input) -> Option<&'x mut Self::Output> {
        self.0.get_mut(obj).and_then(|y| self.1.get_mut(y))
    }
}

impl <FR1: Copy, FR2: Copy> Clone for OptionFieldRefChain<FR1, FR2> {
    fn clone(&self) -> Self {
        OptionFieldRefChain(self.0, self.1)
    }
}

impl <FR1: Copy, FR2: Copy> Copy for OptionFieldRefChain<FR1, FR2> {}

///
/// A `OptionFieldRef` which converted from A `FieldRef`.
///
pub struct FieldRefAsOptionFieldRef<T, U>(FieldRef<T, U>);

impl<'x, T, U> OptionFieldRef<'x> for FieldRefAsOptionFieldRef<T, U> {
    type Input = T;
    type Output = U;

    fn get<'a>(&'a self, obj: &'x Self::Input) -> Option<&'x Self::Output> {
        Some(self.0.get(obj))
    }

    fn get_mut<'a>(&'a self, obj: &'x mut Self::Input) -> Option<&'x mut Self::Output> {
        Some(self.0.get_mut(obj))
    }
}

impl<T, U> Clone for FieldRefAsOptionFieldRef<T, U> {
    fn clone(&self) -> Self {
        FieldRefAsOptionFieldRef(self.0)
    }
}

impl<T, U> Copy for FieldRefAsOptionFieldRef<T, U> {}

///
/// A trait to obtain a value to which `FieldRef` references via description like `obj.get_field(field_ref)`.
///
pub trait GetField where Self: Sized {
    /// # Examples
    ///
    /// ```
    /// use field_ref::{GetField, field_ref_of};
    ///
    /// struct Foo(u32, u32, f64);
    ///
    /// # fn main() {
    /// let fr = field_ref_of!(Foo => 1);
    /// let foo = Foo(10, 20, 0.5);
    /// assert_eq!(foo.get_field(fr), &20);
    /// # }
    /// ```
    fn get_field<T>(&self, fr: FieldRef<Self, T>) -> &T;

    fn try_get_field<'x, FR, T>(&'x self, fr: FR) -> Option<&'x T>
    where
        FR: OptionFieldRef<'x, Input = Self, Output = T>;
}

///
/// Creates a new `FieldRef` from basic type and fields which are (recursively) contained by that type.
///
/// # Examples
///
/// ```
/// use field_ref::{FieldRef, field_ref_of};
///
/// struct Foo(u32, u32);
///
/// # fn main() {
/// // references Foo.1
/// let fr = field_ref_of!(Foo => 1);
/// let foo = Foo(10, 20);
/// assert_eq!(fr.get(&foo), &20);
/// # }
/// ```
#[macro_export]
macro_rules! field_ref_of {
    ($t:ty $(=> $f:tt)+) => {
        unsafe {
            let base = ::std::ptr::null() as *const $t;
            $crate::FieldRef::from_pointers(base, &(*base)$(.$f)+)
        }
    };
}

///
/// A trait to obtain a mutable value to which `FieldRef` references via description like `obj.get_field_mut(field_ref)`.
///
pub trait GetFieldMut where Self: Sized {
    /// # Examples
    ///
    /// ```
    /// use field_ref::{GetFieldMut, field_ref_of};
    ///
    /// struct Foo(u32, u32, f64);
    ///
    /// # fn main() {
    /// let fr = field_ref_of!(Foo => 1);
    /// let mut foo = Foo(10, 20, 0.5);
    /// *foo.get_field_mut(fr) = 30;
    /// assert_eq!(foo.1, 30);
    /// # }
    /// ```
    fn get_field_mut<T>(&mut self, fr: FieldRef<Self, T>) -> &mut T;

    fn try_get_field_mut<'x, FR, T>(&'x mut self, fr: FR) -> Option<&'x mut T>
    where
        FR: OptionFieldRef<'x, Input = Self, Output = T>;
}

impl<S: Sized> GetField for S {
    fn get_field<T>(&self, fr: FieldRef<Self, T>) -> &T {
        fr.get(self)
    }

    fn try_get_field<'x, FR, T>(&'x self, fr: FR) -> Option<&'x T>
    where
        FR: OptionFieldRef<'x, Input = Self, Output = T>
    {
        fr.get(self)
    }
}

impl<S: Sized> GetFieldMut for S {
    fn get_field_mut<T>(&mut self, fr: FieldRef<Self, T>) -> &mut T {
        fr.get_mut(self)
    }

    fn try_get_field_mut<'x, FR, T>(&'x mut self, fr: FR) -> Option<&'x mut T>
    where
        FR: OptionFieldRef<'x, Input = Self, Output = T>
    {
        fr.get_mut(self)
    }
}

/// Creates a new instance of `OptionFieldRef` from basic type (enum constansts, structs or tuples) and these fields.
///
/// # Examples
///
/// ```
/// use field_ref::{GetField, GetFieldMut, OptionFieldRef, opt_field_ref_of};
///
/// struct Foo {
///     x: i32,
///     y: f64,
/// }
///
/// enum E1 {
///     A(i32),
///     B(i32, Foo),
/// }
///
/// enum E2 {
///     X(E1),
///     Y,
/// }
///
/// # fn main() {
/// let fr1 = opt_field_ref_of!(E1::A{0});
/// let fr2 = opt_field_ref_of!(E2::X{0} & E1::B{1} => y);
/// let fr3 = opt_field_ref_of!(Foo => x);
///
/// let e1_1 = E1::A(10);
/// let e1_2 = E1::B(20, Foo{ x: 25, y: 2.5 });
/// let e2_1 = E2::X(E1::B(10, Foo{ x: 30, y: 3.5 }));
/// let e2_2 = E2::Y;
///
/// let mut foo = Foo{ x: 40, y: 4.5 };
///
/// assert_eq!(e1_1.try_get_field(fr1), Some(&10));
/// assert_eq!(e1_2.try_get_field(fr1), None);
///
/// assert_eq!(e2_1.try_get_field(fr2), Some(&3.5));
/// assert_eq!(e2_2.try_get_field(fr2), None);
///
/// assert_eq!(foo.try_get_field(fr3), Some(&40));
/// *foo.try_get_field_mut(fr3).unwrap() = 50;
/// assert_eq!(foo.x, 50)
/// # }
/// ```
#[macro_export]
macro_rules! opt_field_ref_of {
    ($e:path { $f:tt } $(=> $fs:tt)*) => {
        $crate::EnumFieldRef::new(
            $crate::enum_field_extractor!($e => $f $(=> $fs)*),
            $crate::enum_field_extractor!($e => $f $(=> $fs)*, mut)
        )
    };

    ($e:path { $f:tt } $(=> $fs:tt)* & $($tts:tt)+) => {
        $crate::EnumFieldRef::new(
            $crate::enum_field_extractor!($e => $f $(=> $fs)*),
            $crate::enum_field_extractor!($e => $f $(=> $fs)*, mut)
        )
            .chain($crate::opt_field_ref_of!($($tts)+))
    };

    ($t:ty $(=> $f:tt)+) => {
        $crate::field_ref_of!($t $(=> $f)+).as_opt_field_ref()
    };

    ($t:ty $(=> $f:tt)+ & $($tts:tt)+) => {
        $crate::field_ref_of!($t $(=> $f)+).as_opt_field_ref()
            .chain($crate::opt_field_ref_of!($($tts)+))
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! enum_field_extractor {
    ($e:path => $f:tt $(=> $fs:tt)* $(, $mut:tt)*) => {
        #[allow(non_shorthand_field_patterns)]
        |e| if let &$($mut)* $e { $f: ref $($mut)* x, .. } = e {
            Some(&$($mut)*(*x) $(.$fs)*)
        } else {
            None
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[repr(C)] // to guarantee the result of Ord test
    struct Foo(u32, u32);

    struct Bar {
        foo: Foo,
        x: u32,
    }

    #[test]
    fn basic_test() {
        let mut foo = Foo(10, 20);
        let fr1 = field_ref_of!(Foo => 0);
        let fr2 = field_ref_of!(Foo => 1);

        assert_eq!(fr1.get(&foo), &10);
        assert_eq!(foo.get_field(fr2), &20);

        *fr2.get_mut(&mut foo) = 30;
        *foo.get_field_mut(fr1) = 40;
        assert_eq!(foo.0, 40);
        assert_eq!(foo.1, 30);
    }

    #[test]
    fn multi_level_test() {
        let bar = Bar{ foo: Foo(10, 20), x: 30 };
        let fr1 = field_ref_of!(Bar => foo => 1);
        let fr2 = field_ref_of!(Bar => foo);
        let fr3 = field_ref_of!(Foo => 1);
        let fr4 = field_ref_of!(Bar => x);

        assert_eq!(bar.get_field(fr1), &20);
        assert_eq!(bar.get_field(fr2.chain(fr3)), &20);
        assert_eq!(bar.get_field(fr4), &30);
    }

    #[test]
    fn debug_test() {
        let fr = unsafe { FieldRef::<Foo, u32>::from_offset(100) };
        assert_eq!(format!("{:?}", fr), "FieldRef { offset: 100 }");
    }

    #[test]
    fn eq_test() {
        let fr1 = field_ref_of!(Bar => foo => 1);
        let fr2 = field_ref_of!(Bar => foo);
        let fr3 = field_ref_of!(Foo => 1);
        let fr4 = field_ref_of!(Bar => x);

        assert!(fr1 != fr4);
        assert!(fr1 == fr2.chain(fr3));
    }

    #[test]
    fn ord_test() {
        let fr1 = field_ref_of!(Bar => foo => 0);
        let fr2 = field_ref_of!(Bar => foo => 1);
        let fr3 = field_ref_of!(Bar => foo);
        let fr4 = field_ref_of!(Foo => 1);

        assert_eq!(fr1.cmp(&fr2), Ordering::Less);
        assert_eq!(fr2.cmp(&fr1), Ordering::Greater);
        assert_eq!(fr2.cmp(&fr3.chain(fr4)), Ordering::Equal);
    }

    #[derive(Debug, Eq, PartialEq)]
    enum E {
        A(u32, u32),
        B{ x: u32, y: u32 },
        C,
    }

    mod sub {
        #[allow(dead_code)]
        pub enum E2 {
            X(u32),
            Y,
        }
    }

    #[test]
    fn enum_field_basic_test() {
        let fr1 = opt_field_ref_of!(E::A{1});
        let fr2 = opt_field_ref_of!(E::B{x});
        let mut e1 = E::A(10, 20);
        let e2 = E::B{ x: 30, y: 40 };
        let e3 = E::C;

        assert_eq!(fr1.get(&e1), Some(&20));
        assert_eq!(fr1.get(&e2), None);
        assert_eq!(fr1.get(&e3), None);
        *fr1.get_mut(&mut e1).unwrap() = 100;
        assert_eq!(e1, E::A(10, 100));

        assert_eq!(fr2.get(&e2), Some(&30));
    }

    #[test]
    fn enum_field_enum_with_path_test() {
        let fr1 = opt_field_ref_of!(sub::E2::X{0});
        let e1 = sub::E2::X(10);

        assert_eq!(fr1.get(&e1), Some(&10));
    }
}
