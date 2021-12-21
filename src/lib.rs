#![no_std]

use core::{cell::UnsafeCell, sync::atomic::Ordering};
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

impl<T> AtomicOnceCell<T> {
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

    pub fn get(&self) -> Option<&T> {
        if self.is_ready() {
            let cell = unsafe { self.cell_mut() };

            cell.as_ref()
        } else {
            None
        }
    }

    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        self.get_or_try_init::<_, ()>(|| Ok(f())).unwrap()
    }

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

    pub fn into_inner(self) -> Option<T> {
        self.take()
    }

    pub fn get_mut(&mut self) -> Option<&mut T> {
        if self.is_ready() {
            self.cell.get_mut().as_mut()
        } else {
            None
        }
    }

    pub fn take(&self) -> Option<T> {
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

#[cfg(test)]
#[macro_use]
extern crate std;

#[cfg(test)]
#[cfg(not(loom))]
mod tests {
    use std::thread;

    use std::vec::Vec;

    use std::boxed::Box;

    use super::*;

    #[test]
    fn cell() {
        let cell = AtomicOnceCell::new();

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
                assert_eq!(value, *cell.take().unwrap());
            }
        }
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
                    assert_eq!(value, cell.take().unwrap());
                }
            }
        });
    }

    #[test]
    fn concurrent_set_take() {
        loom::model(|| {
            let cell: &'static AtomicOnceCell<_> = Box::leak(Box::new(AtomicOnceCell::new()));

            let setter = thread::spawn(|| {
                cell.set(42).unwrap();
            });

            let taker = thread::spawn(|| cell.take());

            setter.join().unwrap();

            let value = if let Some(value) = taker.join().unwrap() {
                assert!(cell.take().is_none());
                value
            } else {
                cell.take().unwrap()
            };

            assert_eq!(value, 42);
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
}
