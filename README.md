# with_ref

`WithRef` provides additional methods to `RefCell` and friends that aid in explicitly
controlling the lifetime of runtime borrows.

The original use case for these methods was to prevent accidentally holding onto runtime borrows
over an `await` boundary in a single-threaded async environment.

```rust
async fn do_stuff(ptr: Rc<RefCell<Object>>) {
    let mut obj = ptr.borrow_mut();
    // do stuff with obj...

    // Could panic if another future wants to mutable borrow `ptr` since `obj` lives until the
    // end of this function.
    do_other_stuff().await;
}
```

Of course, wrapping the borrow in a scope block will limit it's lifetime, but it's easy to
forget and can get a bit messy. `WithRef` adds some convenience functions to make this a
little more explicit. The above example can be written as:

```rust
async fn do_stuff(ptr: Rc<RefCell<Object>>) {
    ptr.with_mut_ref(|obj| {
        // do stuff with obj...
    });

    // Safe as `ptr` is no longer mutably borrowed at this line.
    do_other_stuff().await;
}
```
