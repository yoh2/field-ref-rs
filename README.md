# field-ref

Field reference (like a member pointer to non-static data field in C++) for Rust

*This version does not have upper compatibility with version 0.1.x.*

Examples:

```Rust
use field_ref::{GetField, GetFieldMut, field_ref_of};

struct Foo(u32, u32, f64);
struct Bar {
    foo: Foo,
    x: u32,
}

fn main() {
    let fr1 = field_ref_of!(Bar => x);
    let fr2 = field_ref_of!(Bar => foo);
    let fr3 = field_ref_of!(Foo => 1);
    let fr4 = field_ref_of!(Bar => foo => 0);

    let mut bar = Bar { foo: Foo(10, 20, 0.5), x: 30 };

    assert_eq!(bar.get_field(fr1), &30);
    assert_eq!(fr1.get_ref(&bar), &30);

    *bar.get_field_mut(fr1) = 100;
    assert_eq!(bar.x, 100);

    *fr1.get_mut(&mut bar) = 200;
    assert_eq!(bar.x, 200);

    assert_eq!(bar.get_field(fr2.chain(fr3)), &20);
    assert_eq!(bar.get_field(fr4), &10);
}
```


```Rust
use field_ref::{GetField, GetFieldMut, OptionFieldRef, opt_field_ref_of};

struct Foo {
    x: i32,
    y: f64,
}

enum E1 {
    A(i32),
    B(i32, Foo),
}

enum E2 {
    X(E1),
    Y,
}

fn main() {
    let fr1 = opt_field_ref_of!(E1::A{0});
    let fr2 = opt_field_ref_of!(E2::X{0} & E1::B{1} => y);
    let fr3 = opt_field_ref_of!(Foo => x);

    let e1_1 = E1::A(10);
    let e1_2 = E1::B(20, Foo{ x: 25, y: 2.5 });
    let e2_1 = E2::X(E1::B(10, Foo{ x: 30, y: 3.5 }));
    let e2_2 = E2::Y;

    let mut foo = Foo{ x: 40, y: 4.5 };

    assert_eq!(e1_1.try_get_field(fr1), Some(&10));
    assert_eq!(e1_2.try_get_field(fr1), None);

    assert_eq!(e2_1.try_get_field(fr2), Some(&3.5));
    assert_eq!(e2_2.try_get_field(fr2), None);

    assert_eq!(foo.try_get_field(fr3), Some(&40));
    *foo.try_get_field_mut(fr3).unwrap() = 50;
    assert_eq!(foo.x, 50)
}
```
