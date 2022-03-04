![Pipeline](https://github.com/rustne-kretser/atomic_once_cell/actions/workflows/rust.yml/badge.svg)
[![Crates.io](https://img.shields.io/crates/v/atomic_once_cell.svg)](https://crates.io/crates/atomic_once_cell)
[![API reference](https://docs.rs/atomic_once_cell/badge.svg)](https://docs.rs/atomic_once_cell/)

# atomic_once_cell

`atomic_once_cell` provides two new types, [`AtomicOnceCell`] and
[`AtomicLazy`], which are thread-safe and lock-free versions of
[`core::lazy::OnceCell`] and [`core::lazy::Lazy`] suitable for use
in `#[no_std]` environments.

### Blocking

Both types can be used in a non-blocking way, but there are some
blocking calls that should not be used from interrupt handlers or
other contexts where blocking will lead to a deadlock. Blocking is
based on
[`crossbeam::utils::Backoff`](https://docs.rs/crossbeam/latest/crossbeam/utils/struct.Backoff.html),
and will be reduced to a spin lock in `#[no_std]` environments.

### Examples
#### `AtomicOnceCell`

```rust
use atomic_once_cell::AtomicOnceCell;

static CELL: AtomicOnceCell<String> = AtomicOnceCell::new();

fn main() {
    CELL.set("Hello, World!".to_owned()).unwrap();

    assert_eq!(*CELL.get().unwrap(), "Hello, World!");
}
```

#### `AtomicLazy`

```rust
use atomic_once_cell::AtomicLazy;

static LAZY: AtomicLazy<String> = AtomicLazy::new(|| "Hello, World!".to_owned());

fn main() {
    assert_eq!(*LAZY, "Hello, World!");
}
```

For more details, see [docs](https://docs.rs/atomic_once_cell/).

# Usage

Add this to your Cargo.toml:

```toml
[dependencies]
atomic_once_cell = "0.1.3"
```

# License

MPL-2.0
