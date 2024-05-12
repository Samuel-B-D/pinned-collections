use super::*;

impl<T> IntoIterator for PinnedVec<T> {
    type Item = Pin<Box<T>>;
    type IntoIter = PinnedVecIntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            cur: 0,
            cur_buf: 0,
            cur_buf_end: self.buffers_len[0] - 1,
            vec: self,
        }
    }
}

pub struct PinnedVecIntoIter<T> {
    cur: usize,
    cur_buf: usize,
    cur_buf_end: usize,
    vec: PinnedVec<T>,
}

impl<T> Iterator for PinnedVecIntoIter<T> {
    type Item = Pin<Box<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cur > self.cur_buf_end {
            if self.cur_buf >= self.vec.buffers.len() - 1 {
                return None;
            }
            self.cur_buf += 1;
            self.cur = 0;
            self.cur_buf_end = self.vec.buffers_len[self.cur_buf] - 1;
        }

        unsafe {
            let val: *mut T = self.vec.buffers[self.cur_buf].ptr().add(self.cur);
            self.cur += 1;
            Some(Pin::new_unchecked(Box::from_raw(val)))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.cur, Some(self.vec.len))
    }

    fn count(self) -> usize where Self: Sized {
        self.vec.len - self.cur
    }
}