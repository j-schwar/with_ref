#![no_std]

//! [`WithRef`] provides additional methods to [`RefCell`] and friends that aid in explicitly
//! controlling the lifetime of runtime borrows.
//!
//! The original use case for these methods was to prevent accidentally holding onto runtime borrows
//! over an `await` boundary in a single-threaded async environment.
//!
//! ```no_run
//! # use std::{rc::Rc, cell::RefCell};
//! # struct Object;
//! # async fn do_other_stuff() {}
//! async fn do_stuff(ptr: Rc<RefCell<Object>>) {
//!     let mut obj = ptr.borrow_mut();
//!     // do stuff with obj...
//!
//!     // Could panic if another future wants to mutable borrow `ptr` since `obj` lives until the
//!     // end of this function.
//!     do_other_stuff().await;
//! }
//! ```
//!
//! Of course, wrapping the borrow in a scope block will limit it's lifetime, but it's easy to
//! forget and can get a bit messy. [`WithRef`] adds some convenience functions to make this a
//! little more explicit. The above example can be written as:
//!
//! ```no_run
//! # use std::{rc::Rc, cell::RefCell};
//! # use with_ref::WithRef;
//! # struct Object;
//! # async fn do_other_stuff() {}
//! async fn do_stuff(ptr: Rc<RefCell<Object>>) {
//!     ptr.with_mut_ref(|obj| {
//!         // do stuff with obj...
//!     });
//!
//!     // Safe as `ptr` is no longer mutably borrowed at this line.
//!     do_other_stuff().await;
//! }
//! ```

use core::cell::RefCell;

/// Provides [`WithRef::with_ref`] and [`WithRef::with_mut_ref`] for explicitly controlling the
/// lifetime of runtime borrows.
pub trait WithRef {
    /// Wrapped value type.
    type Inner: ?Sized;

    /// Executes the specified closure while holding an immutable reference to the wrapped value.
    ///
    /// ```rust
    /// # use std::cell::RefCell;
    /// # use std::rc::Rc;
    /// # use with_ref::WithRef;
    /// #[derive(Default)]
    /// struct Object {
    ///     // ...
    /// }
    ///
    /// let ptr: Rc<RefCell<Object>> = Default::default();
    /// ptr.with_ref(|obj: &Object| {
    ///     // do stuff with obj...
    /// });
    /// ```
    fn with_ref<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&Self::Inner) -> T;

    /// Executes the specified closure while holding a mutable reference to the wrapped value.
    ///
    /// ```rust
    /// # use std::cell::RefCell;
    /// # use std::rc::Rc;
    /// # use with_ref::WithRef;
    /// #[derive(Default)]
    /// struct Object {
    ///     // ...
    /// }
    ///
    /// let ptr: Rc<RefCell<Object>> = Default::default();
    /// ptr.with_mut_ref(|obj: &mut Object| {
    ///     // do stuff with obj...
    /// });
    ///
    /// // Safe to take another mutable reference outside of the closure.
    /// let _ = ptr.borrow_mut();
    /// ```
    fn with_mut_ref<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&mut Self::Inner) -> T;
}

impl<I: ?Sized> WithRef for RefCell<I> {
    type Inner = I;

    fn with_ref<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&Self::Inner) -> T,
    {
        f(&self.borrow())
    }

    fn with_mut_ref<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&mut Self::Inner) -> T,
    {
        f(&mut self.borrow_mut())
    }
}

/// A cell which provides interior mutability via the [`WithRef`] interface.
#[derive(Debug, Default)]
#[repr(transparent)]
pub struct ScopedRefCell<T: ?Sized>(RefCell<T>);

impl<T> ScopedRefCell<T> {
    /// Constructs a new [`ScopedRefCell`] instance wrapping the specified value.
    pub fn new(value: T) -> Self {
        Self(RefCell::new(value))
    }

    /// Unwraps the value consuming the cell.
    ///
    /// ```rust
    /// # use with_ref::ScopedRefCell;
    /// let cell = ScopedRefCell::new(42);
    /// let value = cell.into_inner();
    /// ```
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

impl<T: ?Sized> ScopedRefCell<T> {
    /// Returns a mutable reference to the underlying value.
    ///
    /// ```rust
    /// # use with_ref::ScopedRefCell;
    /// let mut cell = ScopedRefCell::new(42);
    /// let value: &mut i32 = cell.get_mut();
    /// ```
    ///
    /// This call mutably borrows the [`ScopedRefCell`] using compile time borrow checking rules.
    /// Because of this, it's not possible to call `with_ref` or `with_mut_ref` while the mutable
    /// borrow is held:
    ///
    /// ```compile_fail
    /// # use with_ref::{ScopedRefCell, WithRef};
    /// let mut cell = ScopedRefCell::new(42);
    /// let value: &mut i32 = cell.get_mut();
    ///
    /// cell.with_mut_ref(|x| *x = 10); // borrow error
    /// assert_eq!(10, *value);
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        self.0.get_mut()
    }
}

impl<T: ?Sized> WithRef for ScopedRefCell<T> {
    type Inner = T;

    /// Executes the specified closure while holding an immutable reference to the wrapped value.
    ///
    /// ```rust
    /// # use with_ref::{ScopedRefCell, WithRef};
    /// #[derive(Default)]
    /// struct Object {
    ///     // ...
    /// }
    ///
    /// let cell: ScopedRefCell<Object> = Default::default();
    /// cell.with_ref(|obj: &Object| {
    ///     // do stuff with obj...
    /// });
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the wrapped value is already mutably borrowed.
    ///
    /// By only exposing the reference via the [`WithRef`] interface, it's more difficult to
    /// accidentally cause a panic, but one simple way to do is it recursively call `with_mut_ref`:
    ///
    /// ```should_panic
    /// # use with_ref::{ScopedRefCell, WithRef};
    /// let cell = ScopedRefCell::new(42);
    /// cell.with_mut_ref(|_| {
    ///     cell.with_ref(|x| { // already mutably borrowed
    ///         println!("{}", x);
    ///     });
    /// });
    /// ```
    fn with_ref<F, U>(&self, f: F) -> U
    where
        F: FnOnce(&Self::Inner) -> U,
    {
        f(&self.0.borrow())
    }

    /// Executes the specified closure while holding a mutable reference to the wrapped value.
    ///
    /// ```rust
    /// # use with_ref::{ScopedRefCell, WithRef};
    /// #[derive(Default)]
    /// struct Object {
    ///     // ...
    /// }
    ///
    /// let cell: ScopedRefCell<Object> = Default::default();
    /// cell.with_mut_ref(|obj: &mut Object| {
    ///     // do stuff with obj...
    /// });
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the wrapped value is already mutably borrowed.
    ///
    /// By only exposing the reference via the [`WithRef`] interface, it's more difficult to
    /// accidentally cause a panic, but one simple way to do is it recursively call `with_mut_ref`:
    ///
    /// ```should_panic
    /// # use with_ref::{ScopedRefCell, WithRef};
    /// let cell = ScopedRefCell::new(42);
    /// cell.with_mut_ref(|_| {
    ///     cell.with_mut_ref(|x| { // already mutably borrowed
    ///         println!("{}", x);
    ///     });
    /// });
    /// ```
    fn with_mut_ref<F, U>(&self, f: F) -> U
    where
        F: FnOnce(&mut Self::Inner) -> U,
    {
        f(&mut self.0.borrow_mut())
    }
}
