//!
//! Field reference (like a member pointer to non-static data field in C++) for Rust￼
//! 
//! # Examples
//! 
//! ```
//! #[macro_use]
//! extern crate field_ref;
//! 
//! use field_ref::{Field, FieldMut};
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
//! assert_eq!(bar.field(fr1), &30);
//! assert_eq!(fr1.get_ref(&bar), &30);
//! 
//! *bar.field_mut(fr1) = 100;
//! assert_eq!(bar.x, 100);
//! 
//! *fr1.get_mut(&mut bar) = 200;
//! assert_eq!(bar.x, 200);
//! 
//! assert_eq!(bar.field(fr2.chain(fr3)), &20);
//! assert_eq!(bar.field(fr4), &10);
//! # }
//! ```
//!

use std::marker::PhantomData;

///
/// Creates a new `FieldRef` from basic type and fields which are (recursively) contained by that type.
/// 
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
    /// #[macro_use]
    /// extern crate field_ref;
    /// 
    /// use field_ref::FieldRef;
    /// 
    /// struct Foo(u32, u32);
    /// 
    /// # fn main() {
    /// // references Foo.1
    /// let fr = unsafe { FieldRef::<Foo, u32>::from_offset(4) };
    /// let foo = Foo(10, 20);
    /// assert_eq!(fr.get_ref(&foo), &20);
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
    /// extern crate field_ref;
    /// 
    /// use field_ref::FieldRef;
    /// 
    /// struct Foo(u32, u32, f64);
    /// 
    /// # fn main() {
    /// let foo1 = Foo(10, 20, 0.5);
    /// let foo2 = Foo(30, 40, 1.5);
    /// let fr = unsafe { FieldRef::from_pointers(&foo1, &foo1.1) };
    /// assert_eq!(fr.get_ref(&foo2), &40);
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
    /// extern crate field_ref;
    /// 
    /// use field_ref::FieldRef;
    /// 
    /// struct Foo(u32, u32, f64);
    /// 
    /// # fn main() {
    /// let foo1 = Foo(10, 20, 0.5);
    /// let foo2 = Foo(30, 40, 1.5);
    /// let fr = unsafe { FieldRef::from_references(&foo1, &foo1.1) };
    /// assert_eq!(fr.get_ref(&foo2), &40);
    /// # }
    /// ```
    pub unsafe fn from_references(obj: &T, field: &U) -> Self {
        Self::from_pointers(obj, field)
    }

    /// Get a reference of value in an object to which `FieldRef` refers.
    /// 
    /// # Examples
    /// 
    /// ```
    /// #[macro_use]
    /// extern crate field_ref;
    /// 
    /// struct Foo(u32, u32, f64);
    /// 
    /// # fn main() {
    /// let fr = field_ref_of!(Foo => 1);
    /// let foo = Foo(10, 20, 0.5);
    /// assert_eq!(fr.get_ref(&foo), &20);
    /// # }
    /// ```
    pub fn get_ref<'a, 'b>(&'a self, obj: &'b T) -> &'b U {
        let addr = obj as *const _ as usize + self.offset;
        unsafe { &*(addr as *const U) }
    }

    /// Get a mutable reference of value in an object to which `FieldRef` refers.
    /// 
    /// # Examples
    /// 
    /// ```
    /// #[macro_use]
    /// extern crate field_ref;
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
    pub fn get_mut<'a, 'b>(self, obj: &'b mut T) -> &'b mut U {
        let addr = obj as *mut _ as usize + self.offset;
        unsafe { &mut *(addr as *mut U) }
    }

    /// Chains two field references.
    /// 
    /// # Examples
    /// 
    /// ```
    /// #[macro_use]
    /// extern crate field_ref;
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
    /// assert_eq!(fr1.chain(fr2).get_ref(&bar), &20);
    /// # }
    /// ```
    pub fn chain<V>(&self, fr: FieldRef<U, V>) -> FieldRef<T, V> {
        unsafe { FieldRef::<T, V>::from_offset(self.offset + fr.offset) }
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

///
/// A trait to obtain a value to which `FieldRef` references via description like `obj.field(field_ref)'.
/// 
pub trait Field where Self: Sized {
    /// # Examples
    /// 
    /// ```
    /// #[macro_use]
    /// extern crate field_ref;
    /// 
    /// use field_ref::Field;
    /// 
    /// struct Foo(u32, u32, f64);
    /// 
    /// # fn main() {
    /// let fr = field_ref_of!(Foo => 1);
    /// let foo = Foo(10, 20, 0.5);
    /// assert_eq!(foo.field(fr), &20);
    /// # }
    /// ```
    fn field<T>(&self, fr: FieldRef<Self, T>) -> &T;
}

///
/// A trait to obtain a mutable value to which `FieldRef` references via description like `obj.field_mut(field_ref)'.
/// 
pub trait FieldMut where Self: Sized {
    /// # Examples
    /// 
    /// ```
    /// #[macro_use]
    /// extern crate field_ref;
    /// 
    /// use field_ref::FieldMut;
    /// 
    /// struct Foo(u32, u32, f64);
    /// 
    /// # fn main() {
    /// let fr = field_ref_of!(Foo => 1);
    /// let mut foo = Foo(10, 20, 0.5);
    /// *foo.field_mut(fr) = 30;
    /// assert_eq!(foo.1, 30);
    /// # }
    /// ```
    fn field_mut<T>(&mut self, fr: FieldRef<Self, T>) -> &mut T;
}

impl<S: Sized> Field for S {
    fn field<T>(&self, fr: FieldRef<Self, T>) -> &T {
        fr.get_ref(self)
    }
}

impl<S: Sized> FieldMut for S {
    fn field_mut<T>(&mut self, fr: FieldRef<Self, T>) -> &mut T {
        fr.get_mut(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

        assert_eq!(fr1.get_ref(&foo), &10);
        assert_eq!(foo.field(fr2), &20);

        *fr2.get_mut(&mut foo) = 30;
        *foo.field_mut(fr1) = 40;
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

        assert_eq!(bar.field(fr1), &20);
        assert_eq!(bar.field(fr2.chain(fr3)), &20);
        assert_eq!(bar.field(fr4), &30);
    }

    #[test]
    fn debug_test() {
        let fr = unsafe { FieldRef::<Foo, u32>::from_offset(100) };
        assert_eq!(format!("{:?}", fr), "FieldRef { offset: 100 }");
    }
}
