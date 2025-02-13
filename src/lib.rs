// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! `atomic_once_cell` provides two new types, [`AtomicOnceCell`] and
//! [`AtomicLazy`], which are thread-safe and mostly lock-free drop-in
//! replacements of [`core::lazy::OnceCell`] and [`core::lazy::Lazy`]
//! suitable for use in `#[no_std]` environments.
//!
//! ## Blocking
//!
//! Because dereferencing [`AtomicLazy`] can't fail, it can't be
//! lock-free (if you know a way, please tell me).
//!
//! Both types can be used in a non-blocking way, but there are some
//! blocking calls that should not be used from interrupt handlers or
//! other contexts where blocking will lead to a deadlock. Blocking is
//! based on
//! [`crossbeam::utils::Backoff`](https://docs.rs/crossbeam/latest/crossbeam/utils/struct.Backoff.html),
//! and will be reduced to a spinlock in `#[no_std]` environments.
//!
//! ## Examples
//! ### `AtomicOnceCell`
//!
//! ```
//! use atomic_once_cell::AtomicOnceCell;
//!
//! static CELL: AtomicOnceCell<String> = AtomicOnceCell::new();
//!
//! fn main() {
//!     CELL.set("Hello, World!".to_owned()).unwrap();
//!
//!     assert_eq!(*CELL.get().unwrap(), "Hello, World!");
//! }
//! ```
//!
//! ### `AtomicLazy`
//!
//! ```
//! use atomic_once_cell::AtomicLazy;
//!
//! static LAZY: AtomicLazy<String> = AtomicLazy::new(|| "Hello, World!".to_owned());
//!
//! fn main() {
//!     assert_eq!(*LAZY, "Hello, World!");
//! }
//! ```

#![no_std]

use core::{
    cell::{Cell, UnsafeCell},
    fmt,
    ops::Deref,
    sync::atomic::Ordering,
};
use crossbeam_utils::Backoff;

#[cfg(not(loom))]
use portable_atomic::AtomicU8;

#[cfg(loom)]
use loom::sync::atomic::AtomicU8;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[repr(u8)]
#[derive(Eq, PartialEq)]
enum State {
    Empty,
    Busy,
    Ready,
}

impl From<State> for u8 {
    fn from(state: State) -> Self {
        state as u8
    }
}

/// A thread-safe cell which can be written to only once.
///
/// # Examples
///
/// ```
/// use atomic_once_cell::AtomicOnceCell;
///
/// let cell = AtomicOnceCell::new();
/// assert!(cell.get().is_none());
///
/// let value: &String = cell.get_or_init(|| {
///     "Hello, World!".to_string()
/// });
/// assert_eq!(value, "Hello, World!");
/// assert!(cell.get().is_some());
/// ```
pub struct AtomicOnceCell<T> {
    inner: UnsafeCell<Option<T>>,
    state: AtomicU8,
}

impl<T> Default for AtomicOnceCell<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: fmt::Debug> fmt::Debug for AtomicOnceCell<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.get() {
            Some(v) => f.debug_tuple("AtomicOnceCell").field(v).finish(),
            None => f.write_str("AtomicOnceCell(Uninit)"),
        }
    }
}

impl<T: Clone> Clone for AtomicOnceCell<T> {
    fn clone(&self) -> AtomicOnceCell<T> {
        let res = AtomicOnceCell::new();
        if let Some(value) = self.get() {
            match res.set(value.clone()) {
                Ok(()) => (),
                Err(_) => unreachable!(),
            }
        }
        res
    }
}

impl<T: PartialEq> PartialEq for AtomicOnceCell<T> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl<T: Eq> Eq for AtomicOnceCell<T> {}

impl<T> From<T> for AtomicOnceCell<T> {
    fn from(value: T) -> Self {
        AtomicOnceCell {
            inner: UnsafeCell::new(Some(value)),
            state: AtomicU8::new(State::Ready.into()),
        }
    }
}

impl<T> AtomicOnceCell<T> {
    /// Creates a new empty cell.
    #[cfg(not(loom))]
    pub const fn new() -> Self {
        Self {
            inner: UnsafeCell::new(None),
            state: AtomicU8::new(0),
        }
    }

    #[cfg(loom)]
    pub fn new() -> Self {
        Self {
            inner: UnsafeCell::new(None),
            state: AtomicU8::new(0),
        }
    }

    fn update_state(&self, old: State, new: State) -> bool {
        self.state
            .compare_exchange(old.into(), new.into(), Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
    }

    fn is_ready(&self) -> bool {
        self.state.load(Ordering::Acquire) == State::Ready as u8
    }

    unsafe fn cell(&self) -> &Option<T> {
        &*self.inner.get()
    }

    unsafe fn cell_mut(&self) -> &mut Option<T> {
        &mut *self.inner.get()
    }

    /// Gets the reference to the underlying value.
    ///
    /// Returns `None` if the cell is empty.
    pub fn get(&self) -> Option<&T> {
        if self.is_ready() {
            let cell = unsafe { self.cell() };

            cell.as_ref()
        } else {
            None
        }
    }

    /// Gets the mutable reference to the underlying value.
    ///
    /// Returns `None` if the cell is empty.
    pub fn get_mut(&mut self) -> Option<&mut T> {
        if self.is_ready() {
            self.inner.get_mut().as_mut()
        } else {
            None
        }
    }

    /// Sets the contents of the cell to `value`.
    ///
    /// # Errors
    ///
    /// This method returns `Ok(())` if the cell was empty and `Err(value)` if
    /// it was full.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_once_cell::AtomicOnceCell;
    ///
    /// let cell = AtomicOnceCell::new();
    /// assert!(cell.get().is_none());
    ///
    /// assert_eq!(cell.set(92), Ok(()));
    /// assert_eq!(cell.set(62), Err(62));
    ///
    /// assert!(cell.get().is_some());
    /// ```
    pub fn set(&self, value: T) -> Result<(), T> {
        if self.update_state(State::Empty, State::Busy) {
            let cell = unsafe { self.cell_mut() };

            *cell = Some(value);

            assert!(self.update_state(State::Busy, State::Ready));

            Ok(())
        } else {
            Err(value)
        }
    }

    /// Gets the contents of the cell, initializing it with `f`
    /// if the cell was empty.
    ///
    /// # Blocking
    ///
    /// This method might block and should not be used from an
    /// interrupt handler. Blocking is based on
    /// [`crossbeam::utils::Backoff`](https://docs.rs/crossbeam/latest/crossbeam/utils/struct.Backoff.html),
    /// and will be reduced to a spin lock in `#[no_std]`
    /// environments.
    ///
    /// # Panics
    ///
    /// If `f` panics, the panic is propagated to the caller, and the cell
    /// remains uninitialized.
    ///
    /// It is an error to reentrantly initialize the cell from `f`. Doing
    /// so results in a panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_once_cell::AtomicOnceCell;
    ///
    /// let cell = AtomicOnceCell::new();
    /// let value = cell.get_or_init(|| 92);
    /// assert_eq!(value, &92);
    /// let value = cell.get_or_init(|| unreachable!());
    /// assert_eq!(value, &92);
    /// ```
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        self.get_or_try_init::<_, ()>(|| Ok(f()))
            .unwrap_or_else(|_| unreachable!())
    }

    /// Gets the contents of the cell, initializing it with `f` if
    /// the cell was empty. If the cell was empty and `f` failed, an
    /// error is returned.
    ///
    /// # Blocking
    ///
    /// This method might block and should not be used from an
    /// interrupt handler. Blocking is based on
    /// [`crossbeam::utils::Backoff`](https://docs.rs/crossbeam/latest/crossbeam/utils/struct.Backoff.html),
    /// and will be reduced to a spin lock in `#[no_std]`
    /// environments.
    ///
    /// # Panics
    ///
    /// If `f` panics, the panic is propagated to the caller, and the cell
    /// remains uninitialized.
    ///
    /// It is an error to reentrantly initialize the cell from `f`. Doing
    /// so results in a panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_once_cell::AtomicOnceCell;
    ///
    /// let cell = AtomicOnceCell::new();
    /// assert_eq!(cell.get_or_try_init(|| Err(())), Err(()));
    /// assert!(cell.get().is_none());
    /// let value = cell.get_or_try_init(|| -> Result<i32, ()> {
    ///     Ok(92)
    /// });
    /// assert_eq!(value, Ok(&92));
    /// assert_eq!(cell.get(), Some(&92))
    /// ```
    pub fn get_or_try_init<F, E>(&self, f: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        if self.update_state(State::Empty, State::Busy) {
            let cell = unsafe { self.cell_mut() };

            match f() {
                Ok(value) => {
                    *cell = Some(value);

                    assert!(self.update_state(State::Busy, State::Ready));
                }
                Err(err) => {
                    assert!(self.update_state(State::Busy, State::Empty));
                    return Err(err);
                }
            }
        }

        let backoff = Backoff::new();

        loop {
            if let Some(value) = self.get() {
                break Ok(value);
            }

            backoff.spin();

            #[cfg(loom)]
            loom::thread::yield_now();
        }
    }

    /// Consumes the cell, returning the wrapped value.
    ///
    /// Returns `None` if the cell was empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_once_cell::AtomicOnceCell;
    ///
    /// let cell: AtomicOnceCell<String> = AtomicOnceCell::new();
    /// assert_eq!(cell.into_inner(), None);
    ///
    /// let cell = AtomicOnceCell::new();
    /// cell.set("hello".to_string()).unwrap();
    /// assert_eq!(cell.into_inner(), Some("hello".to_string()));
    /// ```
    pub fn into_inner(self) -> Option<T> {
        let mut this = self;
        this.take()
    }

    /// Takes the value out of this `OnceCell`, moving it back to an uninitialized state.
    ///
    /// Has no effect and returns `None` if the `OnceCell` hasn't been initialized.
    ///
    /// Safety is guaranteed by requiring a mutable reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_once_cell::AtomicOnceCell;
    ///
    /// let mut cell: AtomicOnceCell<String> = AtomicOnceCell::new();
    /// assert_eq!(cell.take(), None);
    ///
    /// let mut cell = AtomicOnceCell::new();
    /// cell.set("hello".to_string()).unwrap();
    /// assert_eq!(cell.take(), Some("hello".to_string()));
    /// assert_eq!(cell.get(), None);
    /// ```
    pub fn take(&mut self) -> Option<T> {
        if self.update_state(State::Ready, State::Busy) {
            let cell = unsafe { self.cell_mut() };
            let item = cell.take();

            assert!(self.update_state(State::Busy, State::Empty));

            item
        } else {
            None
        }
    }
}

unsafe impl<T> Sync for AtomicOnceCell<T> where T: Send + Sync {}

#[cfg(feature = "serde")]
impl<'de, T: Deserialize<'de>> Deserialize<'de> for AtomicOnceCell<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        // deserialize the inner value
        let inner_value = Option::<T>::deserialize(deserializer)?;

        // if the inner value is Some, then return AtomicRefCell with the inner value, otherwise return an empty AtomicRefCell
        match inner_value {
            Some(inner_value) => Ok(Self::from(inner_value)),
            None => Ok(Self::default()),
        }
    }
}

#[cfg(feature = "serde")]
impl<T: Serialize> Serialize for AtomicOnceCell<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.get().serialize(serializer)
    }
}

/// A thread-safe value which is initialized on the first access.
///
/// # Blocking
///
/// Calling [`AtomicLazy::force()`] – directly or through `Deref`
/// – might block and should not be called from an interrupt
/// handler. To use `AtomicLazy` in an interrupt handler, the
/// following pattern is recommended:
///
/// ```
/// use atomic_once_cell::AtomicLazy;
///
/// static LAZY: AtomicLazy<String> = AtomicLazy::new(|| "Hello, World!".to_owned());
///
/// fn interrupt_handler() {
///     let item = AtomicLazy::get(&LAZY).unwrap_or_else(|| unreachable!());
///     assert_eq!(*item, "Hello, World!");
///     // [...]
/// }
///
/// fn main() {
///     AtomicLazy::init(&LAZY);
///     assert_eq!(*LAZY, "Hello, World!");
///     // [...] <- Enable interrupt here
///     interrupt_handler(); // interrupt handler called
///                          // asynchronously at some point
///     // [...]
/// }

pub struct AtomicLazy<T, F = fn() -> T> {
    cell: AtomicOnceCell<T>,
    init: Cell<Option<F>>,
}

impl<T: fmt::Debug, F> fmt::Debug for AtomicLazy<T, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AtomicLazy")
            .field("cell", &self.cell)
            .field("init", &"..")
            .finish()
    }
}

impl<T: Default> Default for AtomicLazy<T> {
    /// Creates a new lazy value using `Default` as the initializing function.
    fn default() -> AtomicLazy<T> {
        AtomicLazy::new(T::default)
    }
}

unsafe impl<T, F> Sync for AtomicLazy<T, F>
where
    T: Send + Sync,
    F: Send,
{
}

impl<T, F> AtomicLazy<T, F> {
    /// Creates a new lazy value with the given initializing function.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() {
    /// use atomic_once_cell::AtomicLazy;
    ///
    /// let hello = "Hello, World!".to_string();
    ///
    /// let lazy = AtomicLazy::new(|| hello.to_uppercase());
    ///
    /// assert_eq!(&*lazy, "HELLO, WORLD!");
    /// # }
    /// ```
    #[cfg(not(loom))]
    pub const fn new(f: F) -> Self {
        Self {
            cell: AtomicOnceCell::new(),
            init: Cell::new(Some(f)),
        }
    }

    #[cfg(loom)]
    pub fn new(f: F) -> Self {
        Self {
            cell: AtomicOnceCell::new(),
            init: Cell::new(Some(f)),
        }
    }
}

impl<T, F> AtomicLazy<T, F>
where
    F: FnOnce() -> T,
{
    /// Forces the evaluation of this lazy value and returns a reference to
    /// the result.
    ///
    /// This is equivalent to the `Deref` impl, but is explicit.
    ///
    /// # Blocking
    ///
    /// This method might block and should not be used from an
    /// interrupt handler. Blocking is based on
    /// [`crossbeam::utils::Backoff`](https://docs.rs/crossbeam/latest/crossbeam/utils/struct.Backoff.html),
    /// and will be reduced to a spin lock in `#[no_std]`
    /// environments.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_once_cell::AtomicLazy;
    ///
    /// let lazy = AtomicLazy::new(|| 92);
    ///
    /// assert_eq!(AtomicLazy::force(&lazy), &92);
    /// assert_eq!(&*lazy, &92);
    /// ```
    pub fn force(this: &Self) -> &T {
        this.cell.get_or_init(|| this.init.take().unwrap()())
    }

    /// Like [`AtomicLazy::force()`], but without returing a reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_once_cell::AtomicLazy;
    ///
    /// let lazy = AtomicLazy::new(|| 92);
    ///
    /// AtomicLazy::init(&lazy);
    /// assert_eq!(&*lazy, &92);
    /// ```
    pub fn init(this: &Self) {
        Self::force(this);
    }

    /// Gets the reference to the underlying value.
    ///
    /// Returns `None` if the cell is not initialized.
    ///
    /// # Examples
    ///
    /// ```
    /// use atomic_once_cell::AtomicLazy;
    ///
    /// let lazy = AtomicLazy::new(|| 92);
    ///
    /// assert_eq!(AtomicLazy::get(&lazy), None);
    /// assert_eq!(AtomicLazy::force(&lazy), &92);
    /// assert_eq!(AtomicLazy::get(&lazy), Some(&92));
    /// ```
    pub fn get(this: &Self) -> Option<&T> {
        this.cell.get()
    }
}

impl<T, F> Deref for AtomicLazy<T, F>
where
    F: FnOnce() -> T,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        Self::force(self)
    }
}

#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(test)]
#[cfg(not(loom))]
mod tests {
    use core::sync::atomic::AtomicUsize;
    use std::thread;

    use std::vec::Vec;

    use std::boxed::Box;

    use std::sync::Arc;

    use super::*;

    #[test]
    fn cell() {
        let mut cell = AtomicOnceCell::new();

        assert!(cell.get().is_none());
        assert!(cell.take().is_none());

        assert!(cell.set(42).is_ok());
        assert_eq!(cell.set(42), Err(42));

        assert_eq!(*cell.get().unwrap(), 42);
        assert_eq!(cell.take(), Some(42));
        assert!(cell.take().is_none());

        assert!(cell.set(43).is_ok());
        assert_eq!(cell.set(43), Err(43));

        assert_eq!(*cell.get().unwrap(), 43);
    }

    #[test]
    fn cell_mut() {
        let mut cell = AtomicOnceCell::new();
        assert!(cell.set(42).is_ok());

        let inner = cell.get_mut().unwrap();

        *inner = 44;

        assert_eq!(*cell.get().unwrap(), 44);
    }

    #[test]
    fn get_or_init() {
        let cell = AtomicOnceCell::new();

        assert_eq!(*cell.get_or_init(|| 42), 42);
        assert_eq!(*cell.get_or_init(|| 43), 42);
    }

    #[test]
    fn get_or_try_init() {
        let cell = AtomicOnceCell::new();

        assert!(cell.get_or_try_init(|| Err(())).is_err());
        assert_eq!(*cell.get_or_try_init::<_, ()>(|| Ok(42)).unwrap(), 42);
        assert_eq!(*cell.get_or_try_init::<_, ()>(|| Ok(43)).unwrap(), 42);
        assert_eq!(*cell.get_or_try_init(|| Err(())).unwrap(), 42);
    }

    #[test]
    fn threads() {
        let cell = Arc::new(AtomicOnceCell::new());

        let handles: Vec<_> = (0..10)
            .map(|i| {
                let cell = cell.clone();

                thread::spawn(move || {
                    let value = Box::new(i);
                    let res = cell.set(value);

                    if res.is_ok() {
                        Some(i)
                    } else {
                        None
                    }
                })
            })
            .collect();

        let values: Vec<_> = handles
            .into_iter()
            .map(|handle| handle.join().unwrap())
            .collect();

        for value in values {
            if let Some(value) = value {
                assert_eq!(value, **cell.get().unwrap());
            }
        }
    }

    #[test]
    fn lazy() {
        let init = Cell::new(0);
        let counter = AtomicLazy::new(|| {
            init.set(init.get() + 1);
            AtomicUsize::new(0)
        });

        for _ in 0..10 {
            counter.fetch_add(1, Ordering::Relaxed);
        }

        assert_eq!(init.get(), 1);
        assert_eq!(counter.load(Ordering::Relaxed), 10);
    }

    #[test]
    fn lazy_threads() {
        const N: usize = 100;
        let counter = Arc::new(AtomicLazy::new(|| AtomicUsize::new(0)));

        let handles: Vec<_> = (0..N)
            .map(|_| {
                let counter = counter.clone();
                thread::spawn(move || {
                    counter.fetch_add(1, Ordering::Relaxed);
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(counter.load(Ordering::Relaxed), N);
    }
}

#[cfg(test)]
#[cfg(loom)]
mod loom_tests {
    use std::boxed::Box;
    use std::vec::Vec;

    use loom::thread;

    use super::*;

    #[test]
    fn concurrent_set() {
        loom::model(|| {
            let cell: &'static AtomicOnceCell<_> = Box::leak(Box::new(AtomicOnceCell::new()));

            let handles: Vec<_> = (0..2)
                .map(|i| {
                    thread::spawn(move || {
                        let res = cell.set(i);

                        if res.is_ok() {
                            Some(i)
                        } else {
                            None
                        }
                    })
                })
                .collect();

            let values: Vec<_> = handles
                .into_iter()
                .map(|handle| handle.join().unwrap())
                .collect();

            for value in values {
                if let Some(value) = value {
                    assert_eq!(value, *cell.get().unwrap());
                }
            }
        });
    }

    #[test]
    fn concurrent_set_get() {
        loom::model(|| {
            let cell: &'static AtomicOnceCell<_> = Box::leak(Box::new(AtomicOnceCell::new()));

            let setter = thread::spawn(|| {
                cell.set(42).unwrap();
            });

            let getter = thread::spawn(|| cell.get());

            setter.join().unwrap();

            let value = if let Some(value) = getter.join().unwrap() {
                assert_eq!(cell.get(), Some(value));
                value
            } else {
                cell.get().unwrap()
            };

            assert_eq!(*value, 42);
        });
    }

    #[test]
    fn concurrent_get_or_init() {
        loom::model(|| {
            let cell: &'static AtomicOnceCell<_> = Box::leak(Box::new(AtomicOnceCell::new()));

            let handles: Vec<_> = (0..2)
                .map(|i| {
                    thread::spawn(move || {
                        let res = cell.get_or_init(|| i);

                        *res
                    })
                })
                .collect();

            let values: Vec<_> = handles
                .into_iter()
                .map(|handle| handle.join().unwrap())
                .collect();

            for value in values {
                assert_eq!(value, *cell.get().unwrap());
            }
        });
    }

    #[test]
    fn concurrent_lazy() {
        loom::model(|| {
            let lazy: &'static AtomicLazy<_, _> =
                Box::leak(Box::new(AtomicLazy::new(|| AtomicU8::new(0))));

            let handles: Vec<_> = (0..2)
                .map(|_| thread::spawn(move || lazy.fetch_add(1, Ordering::AcqRel)))
                .collect();

            for handle in handles {
                handle.join().unwrap();
            }

            assert_eq!(lazy.load(Ordering::Relaxed), 2);
        });
    }
}

#[cfg(test)]
mod serde_tests {
    #[test]
    #[cfg(feature = "serde")]
    fn cell_serde() {
        use crate::AtomicOnceCell;

        let cell = AtomicOnceCell::new();

        let empty_serialized = serde_json::to_string(&cell).unwrap();
        let empty_deserialized =
            serde_json::from_str::<AtomicOnceCell<usize>>(&empty_serialized).unwrap();
        assert_eq!(empty_deserialized.get(), None);

        let value = 10;
        assert!(cell.set(value).is_ok());

        let serialized = serde_json::to_string(&cell).unwrap();
        let deserialized = serde_json::from_str::<AtomicOnceCell<usize>>(&serialized).unwrap();

        assert_eq!(*deserialized.get().unwrap(), value);
    }
}
