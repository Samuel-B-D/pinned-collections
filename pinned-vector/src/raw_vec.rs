#![allow(dead_code)]
#![allow(unused_variables)]

// Trimmed-down version of RawVec from Rust's standard library.
//
// std's RawVec is currently unstable, so copied from the standard library 2024-05-10
// https://github.com/rust-lang/rust/blob/f7d54fa6cb8d5a31914de285efbb79f55b60abb2/library/alloc/src/raw_vec.rs
//
// Some alteration such as dropping support for custom allocator were also made to build without
// any unstable features.
//
// TODO: Remove this file and use the one from the standard library if `raw_vec_internals`
//       is ever stabilized / exposed publicly.

use core::alloc::LayoutError;
use core::cmp;
use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ptr::{self, NonNull};

use std::alloc::handle_alloc_error;
use std::alloc::{Layout};
use std::boxed::Box;
use std::collections::TryReserveError;

// One central function responsible for reporting capacity overflows. This'll
// ensure that the code generation related to these panics is minimal as there's
// only one location which panics rather than a bunch throughout the module.
#[cfg(not(no_global_oom_handling))]
#[cfg_attr(not(feature = "panic_immediate_abort"), inline(never))]
fn capacity_overflow() -> ! {
    panic!("capacity overflow");
}

#[cfg(not(no_global_oom_handling))]
#[cfg_attr(not(feature = "panic_immediate_abort"), inline(never))]
fn handle_try_reserve_error(error: TryReserveError) -> ! {
    panic!("TryReserveError: {:?}", error);
}

pub enum RawVecError {
    TryReserveError(TryReserveError),
    CapacityOverflow,
    LayoutError(Layout),
    AllocError(Layout),
}

impl From<TryReserveError> for RawVecError {
    fn from(e: TryReserveError) -> Self {
        RawVecError::TryReserveError(e)
    }
}

enum AllocInit {
    /// The contents of the new memory are uninitialized.
    Uninitialized,
    #[cfg(not(no_global_oom_handling))]
    /// The new memory is guaranteed to be zeroed.
    Zeroed,
}

#[repr(transparent)]
struct Cap(usize);

impl Cap {
    const ZERO: Cap = Cap(0);
}

/// A low-level utility for more ergonomically allocating, reallocating, and deallocating
/// a buffer of memory on the heap without having to worry about all the corner cases
/// involved. This type is excellent for building your own data structures like Vec and VecDeque.
/// In particular:
///
/// * Produces `Unique::dangling()` on zero-sized types.
/// * Produces `Unique::dangling()` on zero-length allocations.
/// * Avoids freeing `Unique::dangling()`.
/// * Catches all overflows in capacity computations (promotes them to "capacity overflow" panics).
/// * Guards against 32-bit systems allocating more than isize::MAX bytes.
/// * Guards against overflowing your length.
/// * Calls `handle_alloc_error` for fallible allocations.
/// * Contains a `ptr::Unique` and thus endows the user with all related benefits.
/// * Uses the excess returned from the allocator to use the largest available capacity.
///
/// This type does not in anyway inspect the memory that it manages. When dropped it *will*
/// free its memory, but it *won't* try to drop its contents. It is up to the user of `RawVec`
/// to handle the actual things *stored* inside of a `RawVec`.
///
/// Note that the excess of a zero-sized types is always infinite, so `capacity()` always returns
/// `usize::MAX`. This means that you need to be careful when round-tripping this type with a
/// `Box<[T]>`, since `capacity()` won't yield the length.
#[allow(missing_debug_implementations)]
pub(crate) struct RawVec<T> {
    ptr: NonNull<T>,
    /// # Safety
    ///
    /// `cap` must be in the `0..=isize::MAX` range.
    cap: Cap,
}

impl<T> RawVec<T> {
    /// Creates the biggest possible `RawVec` (on the system heap)
    /// without allocating. If `T` has positive size, then this makes a
    /// `RawVec` with capacity `0`. If `T` is zero-sized, then it makes a
    /// `RawVec` with capacity `usize::MAX`. Useful for implementing
    /// delayed allocation.
    #[must_use]
    pub fn new() -> Self {
        // This branch should be stripped at compile time.
        let cap = if mem::size_of::<T>() == 0 { Cap(usize::MAX) } else { Cap::ZERO };

        // `cap: 0` means "unallocated". zero-sized types are ignored.
        Self { ptr: NonNull::dangling(), cap }
    }

    /// Creates a `RawVec` (on the system heap) with exactly the
    /// capacity and alignment requirements for a `[T; capacity]`. This is
    /// equivalent to calling `RawVec::new` when `capacity` is `0` or `T` is
    /// zero-sized. Note that if `T` is zero-sized this means you will
    /// *not* get a `RawVec` with the requested capacity.
    ///
    /// Non-fallible version of `try_with_capacity`
    ///
    /// # Panics
    ///
    /// Panics if the requested capacity exceeds `isize::MAX` bytes.
    ///
    /// # Aborts
    ///
    /// Aborts on OOM.
    #[cfg(not(no_global_oom_handling))]
    #[must_use]
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        assert_ne!(mem::size_of::<T>(), 0, "TODO: implement ZST support");
        match Self::try_allocate(capacity, AllocInit::Uninitialized) {
            Ok(res) => res,
            Err(err) => handle_error(err),
        }
    }

    /// Like `with_capacity`, but guarantees the buffer is zeroed.
    #[must_use]
    #[inline]
    pub fn with_capacity_zeroed(capacity: usize) -> Self {
        assert_ne!(mem::size_of::<T>(), 0, "TODO: implement ZST support");
        match Self::try_allocate(capacity, AllocInit::Zeroed) {
            Ok(res) => res,
            Err(err) => handle_error(err),
        }
    }

    // Tiny Vecs are dumb. Skip to:
    // - 8 if the element size is 1, because any heap allocators is likely
    //   to round up a request of less than 8 bytes to at least 8 bytes.
    // - 4 if elements are moderate-sized (<= 1 KiB).
    // - 1 otherwise, to avoid wasting too much space for very short Vecs.
    pub(crate) const MIN_NON_ZERO_CAP: usize = if mem::size_of::<T>() == 1 {
        8
    } else if mem::size_of::<T>() <= 1024 {
        4
    } else {
        1
    };

    /// Converts the entire buffer into `Box<[MaybeUninit<T>]>` with the specified `len`.
    ///
    /// Note that this will correctly reconstitute any `cap` changes
    /// that may have been performed. (See description of type for details.)
    ///
    /// # Safety
    ///
    /// * `len` must be greater than or equal to the most recently requested capacity, and
    /// * `len` must be less than or equal to `self.capacity()`.
    ///
    /// Note, that the requested capacity and `self.capacity()` could differ, as
    /// an allocator could overallocate and return a greater memory block than requested.
    pub unsafe fn into_box(self, len: usize) -> Box<[MaybeUninit<T>]> {
        // Sanity-check one half of the safety requirement (we cannot check the other half).
        debug_assert!(
            len <= self.capacity(),
            "`len` must be smaller than or equal to `self.capacity()`"
        );

        let me = ManuallyDrop::new(self);
        unsafe {
            let slice = ptr::slice_from_raw_parts_mut(me.ptr() as *mut MaybeUninit<T>, len);
            Box::from_raw(slice)
        }
    }

    fn try_allocate(
        capacity: usize,
        init: AllocInit,
    ) -> Result<Self, RawVecError> {
        // Don't allocate here because `Drop` will not deallocate when `capacity` is 0.

        if capacity == 0 {
            Ok(Self::new())
        } else {
            // We avoid `unwrap_or_else` here because it bloats the amount of
            // LLVM IR generated.
            let layout = match Layout::array::<T>(capacity) {
                Ok(layout) => layout,
                Err(_) => return Err(RawVecError::CapacityOverflow),
            };

            alloc_guard(layout.size())?;

            let ptr = match init {
                AllocInit::Uninitialized => unsafe { std::alloc::alloc(layout) },
                #[cfg(not(no_global_oom_handling))]
                AllocInit::Zeroed => unsafe { std::alloc::alloc_zeroed(layout) },
            };

            // Allocators currently return a `NonNull<[u8]>` whose length
            // matches the size requested. If that ever changes, the capacity
            // here should change to `ptr.len() / mem::size_of::<T>()`.
            unsafe {
                Ok(Self { ptr: NonNull::new_unchecked(ptr.cast()), cap: Cap(capacity) })
            }
        }
    }

    /// Reconstitutes a `RawVec` from a pointer, capacity, and allocator.
    ///
    /// # Safety
    ///
    /// The `ptr` must be allocated (via the given allocator `alloc`), and with the given
    /// `capacity`.
    /// The `capacity` cannot exceed `isize::MAX` for sized types. (only a concern on 32-bit
    /// systems).
    /// If the `ptr` and `capacity` come from a `RawVec` created via `alloc`, then this is
    /// guaranteed.
    #[inline]
    pub unsafe fn from_raw_parts(ptr: *mut T, capacity: usize) -> Self {
        Self { ptr: unsafe { NonNull::new_unchecked(ptr) }, cap: Cap(capacity) }
    }

    /// Gets a raw pointer to the start of the allocation. Note that this is
    /// `Unique::dangling()` if `capacity == 0` or `T` is zero-sized. In the former case, you must
    /// be careful.
    #[inline]
    pub fn ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    #[inline]
    pub fn non_null(&self) -> NonNull<T> {
        NonNull::from(self.ptr)
    }

    /// Gets the capacity of the allocation.
    ///
    /// This will always be `usize::MAX` if `T` is zero-sized.
    #[inline(always)]
    pub fn capacity(&self) -> usize {
        self.cap.0
    }

    fn current_memory(&self) -> Option<(NonNull<u8>, Layout)> {
        if self.cap.0 == 0 {
            None
        } else {
            // We could use Layout::array here which ensures the absence of isize and usize overflows
            // and could hypothetically handle differences between stride and size, but this memory
            // has already been allocated so we know it can't overflow and currently Rust does not
            // support such types. So we can do better by skipping some checks and avoid an unwrap.
            assert_eq!(mem::size_of::<T>() % mem::align_of::<T>(), 0);
            unsafe {
                let align = mem::align_of::<T>();
                let size = mem::size_of::<T>() * self.cap.0;
                let layout = Layout::from_size_align_unchecked(size, align);
                Some((self.ptr.cast().into(), layout))
            }
        }
    }

    /// Ensures that the buffer contains at least enough space to hold `len +
    /// additional` elements. If it doesn't already have enough capacity, will
    /// reallocate enough space plus comfortable slack space to get amortized
    /// *O*(1) behavior. Will limit this behavior if it would needlessly cause
    /// itself to panic.
    ///
    /// If `len` exceeds `self.capacity()`, this may fail to actually allocate
    /// the requested space. This is not really unsafe, but the unsafe
    /// code *you* write that relies on the behavior of this function may break.
    ///
    /// This is ideal for implementing a bulk-push operation like `extend`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Aborts
    ///
    /// Aborts on OOM.
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn reserve(&mut self, len: usize, additional: usize) {
        // Callers expect this function to be very cheap when there is already sufficient capacity.
        // Therefore, we move all the resizing and error-handling logic from grow_amortized and
        // handle_reserve behind a call, while making sure that this function is likely to be
        // inlined as just a comparison and a call if the comparison fails.
        #[cold]
        fn do_reserve_and_handle<T>(
            slf: &mut RawVec<T>,
            len: usize,
            additional: usize,
        ) {
            if let Err(err) = slf.grow_amortized(len, additional) {
                handle_error(err.into());
            }
        }

        if self.needs_to_grow(len, additional) {
            do_reserve_and_handle(self, len, additional);
        }
    }

    /// A specialized version of `self.reserve(len, 1)` which requires the
    /// caller to ensure `len == self.capacity()`.
    #[cfg(not(no_global_oom_handling))]
    #[inline(never)]
    pub fn grow_one(&mut self) -> usize {
        match self.grow_amortized(self.cap.0, 1) {
            Ok(grew_by) => grew_by,
            Err(err) => handle_error(err.into()),
        }
    }

    /// Ensures that the buffer contains at least enough space to hold `len +
    /// additional` elements. If it doesn't already, will reallocate the
    /// minimum possible amount of memory necessary. Generally this will be
    /// exactly the amount of memory necessary, but in principle the allocator
    /// is free to give back more than we asked for.
    ///
    /// If `len` exceeds `self.capacity()`, this may fail to actually allocate
    /// the requested space. This is not really unsafe, but the unsafe code
    /// *you* write that relies on the behavior of this function may break.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Aborts
    ///
    /// Aborts on OOM.
    #[cfg(not(no_global_oom_handling))]
    pub fn reserve_exact(&mut self, len: usize, additional: usize) {
        if self.needs_to_grow(len, additional) {
            if let Err(err) = self.grow_exact(len, additional) {
                handle_error(err.into());
            }
        }
    }

    /// Shrinks the buffer down to the specified capacity. If the given amount
    /// is 0, actually completely deallocates.
    ///
    /// # Panics
    ///
    /// Panics if the given amount is *larger* than the current capacity.
    ///
    /// # Aborts
    ///
    /// Aborts on OOM.
    #[cfg(not(no_global_oom_handling))]
    pub fn shrink_to_fit(&mut self, cap: usize) -> usize {
        match self.shrink(cap) {
            Ok(shrank_by) => shrank_by,
            Err(err) => handle_error(err.into()),
        }
    }
}

impl<T> RawVec<T> {
    /// Returns if the buffer needs to grow to fulfill the needed extra capacity.
    /// Mainly used to make inlining reserve-calls possible without inlining `grow`.
    fn needs_to_grow(&self, len: usize, additional: usize) -> bool {
        additional > self.capacity().wrapping_sub(len)
    }

    /// # Safety:
    ///
    /// `cap` must not exceed `isize::MAX`.
    unsafe fn set_ptr_and_cap(&mut self, ptr: NonNull<u8>, cap: usize) {
        // Allocators currently return a `NonNull<[u8]>` whose length matches
        // the size requested. If that ever changes, the capacity here should
        // change to `ptr.len() / mem::size_of::<T>()`.
        self.ptr = NonNull::new_unchecked(ptr.as_ptr() as *mut T);
        self.cap = Cap(cap);
    }

    // This method is usually instantiated many times. So we want it to be as
    // small as possible, to improve compile times. But we also want as much of
    // its contents to be statically computable as possible, to make the
    // generated code run faster. Therefore, this method is carefully written
    // so that all of the code that depends on `T` is within it, while as much
    // of the code that doesn't depend on `T` as possible is in functions that
    // are non-generic over `T`.
    fn grow_amortized(&mut self, len: usize, additional: usize) -> Result<usize, RawVecError> {
        // since we set the capacity to usize::MAX when T has size 0,
        // getting to here necessarily means the Vec is overfull.
        assert_ne!(mem::size_of::<T>(), 0, "capacity overflow");

        // This is ensured by the calling contexts.
        debug_assert!(additional > 0);

        let original_cap = self.cap.0;

        // Nothing we can really do about these checks, sadly.
        let required_cap = len.checked_add(additional).ok_or(RawVecError::CapacityOverflow)?;

        // This guarantees exponential growth. The doubling cannot overflow
        // because `cap <= isize::MAX` and the type of `cap` is `usize`.
        let cap = cmp::max(self.cap.0 * 2, required_cap);
        let cap = cmp::max(Self::MIN_NON_ZERO_CAP, cap);

        let new_layout = Layout::array::<T>(cap);

        // `finish_grow` is non-generic over `T`.
        let ptr = finish_grow(new_layout, self.current_memory())?;
        // SAFETY: finish_grow would have resulted in a capacity overflow if we tried to allocate more than isize::MAX items
        unsafe { self.set_ptr_and_cap(ptr, cap) };
        Ok(cap - original_cap)
    }

    // The constraints on this method are much the same as those on
    // `grow_amortized`, but this method is usually instantiated less often so
    // it's less critical.
    fn grow_exact(&mut self, len: usize, additional: usize) -> Result<(), RawVecError> {
        let cap = len.checked_add(additional).ok_or(RawVecError::CapacityOverflow)?;
        let new_layout = Layout::array::<T>(cap);

        // `finish_grow` is non-generic over `T`.
        let ptr = finish_grow(new_layout, self.current_memory())?;
        // SAFETY: finish_grow would have resulted in a capacity overflow if we tried to allocate more than isize::MAX items
        unsafe {
            self.set_ptr_and_cap(ptr, cap);
        }
        Ok(())
    }

    #[cfg(not(no_global_oom_handling))]
    fn shrink(&mut self, cap: usize) -> Result<usize, RawVecError> {
        assert!(cap <= self.capacity(), "Tried to shrink to a larger capacity");

        let original_cap = self.cap.0;

        let (ptr, layout) = if let Some(mem) = self.current_memory() { mem } else { return Ok(0) };
        // See current_memory() why this assert is here
        assert_eq!(mem::size_of::<T>() % mem::align_of::<T>(), 0);

        // If shrinking to 0, deallocate the buffer.
        if cap == 0 {
            unsafe { std::alloc::dealloc(ptr.as_ptr(), layout) };
            self.ptr = NonNull::dangling();
            self.cap = Cap::ZERO;
        } else {
            let ptr = unsafe {
                // `Layout::array` cannot overflow here because it would have
                // overflowed earlier when capacity was larger.
                let new_size = mem::size_of::<T>() * cap;
                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                std::alloc::realloc(ptr.as_ptr(), layout, new_layout.size())
            };
            // SAFETY: if the allocation is valid, then the capacity is too
            unsafe {
                self.ptr = NonNull::new_unchecked(ptr as *mut T);
                self.cap = Cap(cap);
            }
        }
        Ok(original_cap - self.cap.0)
    }
}

// This function is outside `RawVec` to minimize compile times. See the comment
// above `RawVec::grow_amortized` for details. (The `A` parameter isn't
// significant, because the number of different `A` types seen in practice is
// much smaller than the number of `T` types.)
#[inline(never)]
fn finish_grow(
    new_layout: Result<Layout, LayoutError>,
    current_memory: Option<(NonNull<u8>, Layout)>,
) -> Result<NonNull<u8>, RawVecError> {
    // Check for the error here to minimize the size of `RawVec::grow_*`.
    let new_layout = new_layout.map_err(|_| RawVecError::CapacityOverflow)?;

    alloc_guard(new_layout.size())?;

    let memory = if let Some((ptr, old_layout)) = current_memory {
        debug_assert_eq!(old_layout.align(), new_layout.align());
        unsafe {
            // The allocator checks for alignment equality
            std::alloc::realloc(ptr.as_ptr(), old_layout, new_layout.size())
        }
    } else {
        unsafe {
            std::alloc::alloc(new_layout)
        }
    };

    unsafe {
        Ok(NonNull::new_unchecked(memory))
    }
}

impl<T> Drop for RawVec<T> {
    fn drop(&mut self) {
        let elem_size = mem::size_of::<T>();


        if self.cap.0 != 0 && elem_size != 0 {
            if let Some((ptr, layout)) = self.current_memory() {
                unsafe { std::alloc::dealloc(ptr.as_ptr(), layout) }
            }
        }
    }
}

// Central function for reserve error handling.
#[cfg(not(no_global_oom_handling))]
#[cold]
fn handle_error(e: RawVecError) -> ! {
    match e {
        RawVecError::CapacityOverflow => capacity_overflow(),
        RawVecError::LayoutError(layout) => handle_alloc_error(layout),
        RawVecError::TryReserveError(e) => handle_try_reserve_error(e),
        RawVecError::AllocError(l) => handle_alloc_error(l),
    }
}

// We need to guarantee the following:
// * We don't ever allocate `> isize::MAX` byte-size objects.
// * We don't overflow `usize::MAX` and actually allocate too little.
//
// On 64-bit we just need to check for overflow since trying to allocate
// `> isize::MAX` bytes will surely fail. On 32-bit and 16-bit we need to add
// an extra guard for this in case we're running on a platform which can use
// all 4GB in user-space, e.g., PAE or x32.
#[inline]
fn alloc_guard(alloc_size: usize) -> Result<(), RawVecError> {
    if usize::BITS < 64 && alloc_size > isize::MAX as usize {
        Err(RawVecError::CapacityOverflow)
    } else {
        Ok(())
    }
}