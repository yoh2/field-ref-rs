# field-ref: Field reference (like a member pointer to non-static data field in C++) for Rust

Example:

```Rust
#[macro_use]
extern crate field_ref;

use field_ref::{Field, FieldMut};

struct Foo(u32, u32, f64);
struct Bar {
    foo: Foo,
    x: u32,
}

let fr1 = field_ref_of!(Bar => x);
let fr2 = field_ref_of!(Bar => foo);
let fr3 = field_ref_of!(Foo => 1);
let fr4 = field_ref_of!(Bar => foo => 0);

let mut bar = Bar { foo: Foo(10, 20, 0.5), x: 30 };

assert_eq!(bar.field(fr1), &30);
assert_eq!(fr1.get_ref(&bar), &30);

*bar.field_mut(fr1) = 100;
assert_eq!(bar.x, 100);

*fr1.get_mut(&mut bar) = 200;
assert_eq!(bar.x, 200);

assert_eq!(bar.field(fr2.chain(fr3)), &20);
assert_eq!(bar.field(fr4), &10);
```
