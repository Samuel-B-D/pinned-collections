//! A heap-allocated, growable array type analogous to the standard [`Vec<T>`],
//! but having pinned content which is not moved when resizing.
//!
//! Growing will by default allocate a new buffer on the stack that is twice as large
//! as the previously allocated buffer.
//!
//! This all means that a [`PinnedVec`] is *not* necessarily contiguous memory,
//! and therefore cannot be sliced (but can be iterated over).
//!
//! As opposed to the traditional vector, creating a new [`PinnedVec<T>`] *require*
//! specifying an initial capacity, making [`PinnedVec::new`] analogous to
//! [`Vec::with_capacity`] rather than [`Vec::new`].
//! An explicit size of 0 is allowed and will defer creation of the initial buffer
//! to the first insertion.
//!
//! This is because the initial capacity of a [`PinnedVec<T>`] is an important decision
//! due to the performance impacts of resizing.
//!
//! Growing a [`PinnedVec<T>`] imply adding a new buffer on each growth.
//! A [`PinnedVec<T>`] which was initially created with sufficient capacity have very
//! similar performances characteristics to [`Vec<T>`], but each additional buffers created
//! from resizing introduce an additional cost to *every* operations done on it.
//!
//! # Examples
//!
//! You can explicitly create a [`PinnedVec`] with [`PinnedVec::new`]:
//!
//! ```
//! # use pinned_vector::PinnedVec;
//! let v: PinnedVec<i32> = PinnedVec::new(2);
//! ```
//!
//! You can [`push`] values onto the end of a pinned vector (which will grow the
//! vector as needed):
//!
//! ```
//! # use pinned_vector::PinnedVec;
//! let mut v = PinnedVec::from(vec![1, 2]);
//!
//! v.push(3);
//! ```
//!
//! Popping values works in much the same way:
//!
//! ```
//! # use pinned_vector::PinnedVec;
//! let mut v: PinnedVec<_> = vec![1, 2].into();
//!
//! let two = v.pop();
//! ```

extern crate core;

use std::pin::Pin;
use crate::raw_vec::RawVec;

mod raw_vec;
mod inner;
mod tests;
mod iter;
mod iter_mut;

/// A heap-allocated, growable array type analogous to the standard `Vec<T>`,
/// but having pinned content which is not moved when resizing.
///
/// Growing will by default allocate a new buffer on the stack that is twice as large
/// as the previously allocated buffer.
///
/// As opposed to the traditional vector, creating a new `PinnedVec<T>` *require*
/// specifying an initial capacity, making `PinnedVec::new` analogous to
/// `Vec::with_capacity` rather than `Vec::new`.
/// An explicit size of 0 is allowed and will defer creation of the initial buffer
/// to the first insertion.
///
/// This is because the initial capacity of a `PinnedVec<T>` is an important decision
/// due to the performance impacts of resizing.
///
/// Growing a `PinnedVec<T>` imply adding a new buffer on each growth.
/// A `PinnedVec<T>` which was initially created with sufficient capacity have very
/// similar performances caracteristics to `Vec<T>`, but each additional buffers created
/// from resizing introduce an additional cost to *every* operations done on it.
///
/// # Examples
///
/// ```
/// # use pinned_vector::PinnedVec;
/// let mut vec = PinnedVec::new(2);
/// vec.push("1".to_string());
/// vec.push("2".to_string());
///
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec.get(0).as_str(), "1");
///
/// assert_eq!(vec.pop(), true);
/// assert_eq!(vec.len(), 1);
///
/// vec.set(0, "7".to_string());
/// assert_eq!(vec.get(0).as_str(), "7");
///
/// for x in &vec {
///     println!("{x}");
/// }
/// ```
pub struct PinnedVec<T> {
    buffers: Vec<RawVec<T>>,
    buffers_len: Vec<usize>,
    buffers_start: Vec<usize>,
    len: usize,
    cap: usize,
}

impl<T> PinnedVec<T> {
    /// Constructs a new `PinnedVec<T>` with the specified capacity.
    ///
    /// A capacity of 0 is allowed and will create a `PinnedVec` which will
    /// not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_mut)]
    /// # use pinned_vector::PinnedVec;
    /// let mut vec: PinnedVec<i32> = PinnedVec::new(2);
    /// ```
    #[inline]
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        PinnedVec {
            buffers: vec![RawVec::with_capacity(capacity)],
            buffers_len: vec![0],
            buffers_start: vec![0],
            len: 0,
            cap: capacity,
        }
    }

    /// Returns the total number of elements the vector can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pinned_vector::PinnedVec;
    /// let mut vec: PinnedVec<i32> = PinnedVec::new(10);
    /// vec.push(42);
    /// assert!(vec.capacity() >= 10);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.cap
    }

    /// Returns the number of elements in the vector, also referred to
    /// as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pinned_vector::PinnedVec;
    /// let a = PinnedVec::from(vec![1, 2, 3]);
    /// assert_eq!(a.len(), 3);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pinned_vector::PinnedVec;
    /// let mut v = PinnedVec::new(0);
    /// assert!(v.is_empty());
    ///
    /// v.push(1);
    /// assert!(!v.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// This uses [`std::alloc::realloc`] to reallocate.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pinned_vector::PinnedVec;
    /// let mut vec = PinnedVec::new(10);
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    /// assert!(vec.capacity() >= 10);
    /// vec.shrink_to_fit();
    /// assert_eq!(vec.capacity(), 3);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        let len = self.len;
        // The capacity is never less than the length, and there's nothing to do when
        // they are equal, so we can avoid the panic case in `RawVec::shrink_to_fit`
        // by only calling it with a greater capacity.
        if self.cap > len {
            let last_vec = self.get_last_buffer();
            let shrank_by = last_vec.shrink_to_fit(len);
            self.cap -= shrank_by;
        }
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pinned_vector::PinnedVec;
    /// let mut vec = PinnedVec::from(vec!["1".to_string(), "2".to_string()]);
    /// vec.push("3".to_string());
    /// assert_eq!(vec.len(), 3);
    /// assert_eq!(vec.get(2).as_str(), "3");
    /// ```
    #[inline]
    pub fn push(&mut self, value: T) {
        if self.len == self.cap {
            if self.cap == 0 {
                let grew_by = self.buffers[0].grow_one();
                self.cap += grew_by;
            } else {
                let new_buffer_capacity = (self.cap * 2).max(1);
                self.buffers.push(RawVec::with_capacity(new_buffer_capacity));
                self.buffers_len.push(0);
                let prev_buffer_idx = self.buffers_start.len() - 1;
                self.buffers_start.push(self.buffers_start[prev_buffer_idx] + self.buffers_len[prev_buffer_idx]);
                self.cap += new_buffer_capacity;
            }
        }

        let last_idx = self.buffers_len.len() - 1;
        let target_buffer = &mut self.buffers[last_idx];
        unsafe {
            let end = target_buffer.ptr().add(self.buffers_len[last_idx]);
            std::ptr::write(end, value);
        }
        self.len += 1;
        self.buffers_len[last_idx] += 1;
    }

    /// Removes the last element from a vector and returns it, or [`None`] if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pinned_vector::PinnedVec;
    /// let mut vec = PinnedVec::from(vec![1, 2, 3]);
    /// assert_eq!(vec.pop(), true);
    /// assert_eq!(vec.len(), 2);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> bool {
        if self.len == 0 {
            false
        } else {
            let mut last_idx = self.buffers_len.len() - 1;

            if self.buffers_len[last_idx] == 0 {
                self.buffers.pop();
                self.buffers_len.pop();
                self.buffers_start.pop();
                last_idx -= 1;
            }

            self.len -= 1;
            self.buffers_len[last_idx] -= 1;
            return true;
        }
    }

    #[inline]
    pub fn get(&self, index: usize) -> Pin<&T> {
        unsafe { Pin::new_unchecked(self.get_unchecked(index)) }
    }

    #[inline]
    pub fn get_unpin(&self, index: usize) -> &T where T: Unpin {
        unsafe { self.get_unchecked(index) }
    }

    #[inline]
    pub fn get_mut(&self, index: usize) -> Pin<&mut T> {
        let buffer_idx = self.get_buffer_index(index);
        let idx = index - self.buffers_start[buffer_idx];
        unsafe {
            let val: *mut T = self.buffers[buffer_idx].ptr().add(idx);
            Pin::new_unchecked(&mut *val)
        }
    }

    #[inline]
    pub fn set(&self, index: usize, value: T) {
        assert!(index < self.len, "index out of bounds: the len is {} but the index is {}", self.len, index);
        let buffer_idx = self.get_buffer_index(index);
        let idx = index - self.buffers_start[buffer_idx];
        unsafe {
            let ptr: *mut T = self.buffers[buffer_idx].ptr().add(idx);
            std::ptr::write(ptr, value);
        }
    }

    #[inline]
    pub fn is_contiguous(&self) -> bool {
        self.buffers.len() == 1
    }
}

/// Private utilities
impl<T> PinnedVec<T> {
    fn get_last_buffer(&mut self) -> &mut RawVec<T> {
        let last_idx = self.buffers.len() - 1;
        &mut self.buffers[last_idx]
    }

    fn get_buffer_index(&self, index: usize) -> usize {
        let buffers_len = self.buffers.len();
        if buffers_len == 1 {
            return 0
        }

        let mut buffer_idx = buffers_len / 2;
        loop {
            if index < self.buffers_start[buffer_idx] {
                buffer_idx = buffer_idx / 2;
            }
            if index >= self.buffers_start[buffer_idx] + self.buffers_len[buffer_idx] {
                buffer_idx += 1 + buffer_idx / 2;
            }
            break;
        }
        buffer_idx
    }

    #[inline]
    unsafe fn get_unchecked(&self, index: usize) -> &T {
        let buffer_idx = self.get_buffer_index(index);
        let idx = index - self.buffers_start[buffer_idx];
        unsafe {
            let val: *const T = self.buffers[buffer_idx].ptr().add(idx);
            &*val
        }
    }
}