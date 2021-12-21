//! AtomicOnceCell provides two new types, [`AtomicOnceCell`] and
//! [`AtomicLazy`], which are thread-safe and lock-free versions of
//! [`core::lazy::OnceCell`] and [`core::lazy::Lazy`].

#![no_std]

use core::{
    cell::{Cell, UnsafeCell},
    fmt,
    ops::Deref,
    sync::atomic::Ordering,
};
use crossbeam_utils::Backoff;

#[cfg(not(loom))]
use core::sync::atomic::AtomicU8;

#[cfg(loom)]
use loom::sync::atomic::AtomicU8;

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

pub struct AtomicOnceCell<T> {
    cell: UnsafeCell<Option<T>>,
    state: AtomicU8,
}

/// A thread-safe cell which can be written to only once
///
/// Like `OnceCell`, but thread-safe.
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
impl<T> AtomicOnceCell<T> {
    /// Creates a new empty cell.
    #[cfg(not(loom))]
    pub const fn new() -> Self {
        Self {
            cell: UnsafeCell::new(None),
            state: AtomicU8::new(0),
        }
    }

    #[cfg(loom)]
    pub fn new() -> Self {
        Self {
            cell: UnsafeCell::new(None),
            state: AtomicU8::new(0),
        }
    }

    fn update_state(&self, old: State, new: State) -> bool {
        self.state
            .compare_exchange_weak(old.into(), new.into(), Ordering::AcqRel, Ordering::Relaxed)
            .is_ok()
    }

    fn is_ready(&self) -> bool {
        self.state.load(Ordering::Acquire) == State::Ready.into()
    }

    unsafe fn cell_mut(&self) -> &mut Option<T> {
        &mut *self.cell.get()
    }

    /// Gets the reference to the underlying value.
    ///
    /// Returns `None` if the cell is empty.
    pub fn get(&self) -> Option<&T> {
        if self.is_ready() {
            let cell = unsafe { self.cell_mut() };

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
            self.cell.get_mut().as_mut()
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
        self.get_or_try_init::<_, ()>(|| Ok(f())).unwrap()
    }

    /// Gets the contents of the cell, initializing it with `f` if
    /// the cell was empty. If the cell was empty and `f` failed, an
    /// error is returned.
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
            let value = self.get();

            if value.is_some() {
                break Ok(value.unwrap());
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

/// A thread-safe value which is initialized on the first access.
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
        let cell: &'static AtomicOnceCell<_> = Box::leak(Box::new(AtomicOnceCell::new()));

        let handles: Vec<_> = (0..10)
            .map(|i| {
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
            Cell::new(0)
        });

        for _ in 0..10 {
            counter.set(counter.get() + 1);
        }

        assert_eq!(init.get(), 1);
        assert_eq!(counter.get(), 10);
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
