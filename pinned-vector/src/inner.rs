use super::*;

unsafe impl<T: Send> Send for PinnedVec<T> {}
unsafe impl<T: Sync> Sync for PinnedVec<T> {}

impl<T> From<Vec<T>> for PinnedVec<T> {
    fn from(mut vec: Vec<T>) -> Self {
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

impl<T> Drop for PinnedVec<T> {
    fn drop(&mut self) {
        // TODO: iterate through all elements and drop them (can't pop because pop doesn't return the element because of pinning)

        // while self.pop() {}
        // deallocation is handled by RawVec
    }
}