use core::fmt;
use std::ops::Index;
use super::*;

unsafe impl<T: Send> Send for PinnedVec<T> {}
unsafe impl<T: Sync> Sync for PinnedVec<T> {}

impl<T> From<Vec<T>> for PinnedVec<T> {
    fn from(vec: Vec<T>) -> Self {
        let cap = vec.capacity();
        let len = vec.len();
        PinnedVec {
            buffers: vec![unsafe { RawVec::from_raw_parts(vec.leak().as_mut_ptr(), cap) }],
            buffers_len: vec![len],
            buffers_start: vec![0],
            len,
            cap,
        }
    }
}

impl<T> Index<usize> for PinnedVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.get_unchecked(index) }
    }
}

impl<T: fmt::Debug> fmt::Debug for PinnedVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        let mut first = true;
        for v in self {
            if first {
                first = false;
            } else {
                write!(f, ", ")?;
            }
            fmt::Debug::fmt(v, f)?;
        }
        write!(f, "]")
    }
}

impl<T> FromIterator<T> for PinnedVec<T> {
    fn from_iter<I: IntoIterator<Item=T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let (lower, _) = iter.size_hint();
        let mut pinned_vec = PinnedVec::new(lower.max(2));
        for v in iter {
            pinned_vec.push(v);
        }
        pinned_vec
    }
}

impl<T> Drop for PinnedVec<T> {
    fn drop(&mut self) {
        // TODO: iterate through all elements and drop them (can't pop because pop doesn't return the element because of pinning)

        // while self.pop() {}
        // deallocation is handled by RawVec
    }
}