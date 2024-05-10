//! A heap-allocated, growable array type analogous to the standard `Vec<T>`,
//! but having pinned content which is not moved when resizing.
//!
//! Growing will by default allocate a new buffer on the stack that is twice as large
//! as the previously allocated buffer, but the growing behavior is configurable.
//! TODO: Indicate which function to control allocation behavior here
//!
//! As opposed to the traditional vector, creating a new `PinnedVec<T>` *require*
//! specifying an initial capacity, making `PinnedVec::new` analogous to
//! `Vec::with_capacity` rather than `Vec::new`.
//! An explicit size of 0 is allowed and will defer creation of the initial buffer
//! to the first insertion.
//!
//! This is because the initial capacity of a `PinnedVec<T>` is an important decision
//! due to the performance impacts of resizing.
//!
//! Growing a `PinnedVec<T>` imply adding a new buffer on each growth.
//! A `PinnedVec<T>` which was initially created with sufficient capacity have very
//! similar performances caracteristics to `Vec<T>`, but each additional buffers created
//! from resizing introduce an additional cost to *every* operations done on it.
//!
//! # Examples
//!
//! You can explicitly create a [`PinnedVec`] with [`PinnedVec::new`]:
//!
//! ```
//! let v: PinnedVec<i32> = PinnedVec::new(2);
//! ```
//!
//! You can [`push`] values onto the end of a pinned vector (which will grow the
//! vector as needed):
//!
//! ```
//! let mut v = PinnedVec::from(vec![1, 2]);
//!
//! v.push(3);
//! ```
//!
//! Popping values works in much the same way:
//!
//! ```
//! let mut v: PinnedVec<_> = vec![1, 2].into();
//!
//! let two = v.pop();
//! ```
//!
//! Vectors also support indexing (through the [`Index`] and [`IndexMut`] traits):
//!
//! ```
//! let mut v = PinnedVec::from(vec![1, 2, 3]);
//! let three = v[2];
//! v[1] = v[1] + 5;
//! ```

use crate::raw_vec::RawVec;

mod raw_vec;

/// A heap-allocated, growable array type analogous to the standard `Vec<T>`,
/// but having pinned content which is not moved when resizing.
///
/// Growing will by default allocate a new buffer on the stack that is twice as large
/// as the previously allocated buffer, but the growing behavior is configurable.
/// TODO: Indicate which function to control allocation behavior here
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
/// let mut vec = PinnedVec::new(2);
/// vec.push(1);
/// vec.push(2);
///
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec[0], 1);
///
/// assert_eq!(vec.pop(), Some(2));
/// assert_eq!(vec.len(), 1);
///
/// vec[0] = 7;
/// assert_eq!(vec[0], 7);
///
/// vec.extend([1, 2, 3]);
///
/// for x in &vec {
///     println!("{x}");
/// }
/// assert_eq!(vec, [7, 1, 2, 3]);
/// ```
pub struct PinnedVec<T> {
    buf: RawVec<T>,
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
            buf: RawVec::with_capacity(capacity),
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

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `PinnedVec<T>`. The collection may reserve more space to
    /// speculatively avoid frequent reallocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// # use pinned_vector::PinnedVec;
    /// let mut vec = PinnedVec::from(vec![1]);
    /// vec.reserve(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        todo!()
        // self.buf.reserve(self.len, additional);
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
    /// vec.extend([1, 2, 3]);
    /// assert!(vec.capacity() >= 10);
    /// vec.shrink_to_fit();
    /// assert_eq!(vec.capacity(), 3);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        // The capacity is never less than the length, and there's nothing to do when
        // they are equal, so we can avoid the panic case in `RawVec::shrink_to_fit`
        // by only calling it with a greater capacity.
        if self.capacity() > self.len {
            self.buf.shrink_to_fit(self.len);
        }
    }
}

impl<T> From<Vec<T>> for PinnedVec<T> {
    fn from(mut vec: Vec<T>) -> Self {
        let cap = vec.capacity();
        PinnedVec {
            buf: unsafe { RawVec::from_raw_parts(vec.as_mut_ptr(), cap) },
            len: vec.len(),
            cap,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_create() {
        let vec: PinnedVec<i32> = PinnedVec::new(2);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.capacity(), 2);
    }

    #[test]
    fn can_create_empty() {
        let vec: PinnedVec<i32> = PinnedVec::new(0);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.capacity(), 0);
    }

    #[test]
    fn can_create_from_vec() {
        let vec = PinnedVec::from(vec![1, 2]);
        assert_eq!(vec.len(), 2);
        assert!(vec.capacity() >= 2);
    }
}
