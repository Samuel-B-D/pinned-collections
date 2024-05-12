use std::marker::PhantomData;
use super::*;

impl<T> PinnedVec<T> {
    pub fn iter_mut(&mut self) -> PinnedVecIterMut<T> {
       self.into_iter()
    }
}

impl<'v, T> IntoIterator for &'v mut PinnedVec<T> {
    type Item = Pin<&'v mut T>;
    type IntoIter = PinnedVecIterMut<'v, T>;

    fn into_iter(self) -> Self::IntoIter {
        PinnedVecIterMut {
            cur: 0,
            cur_buf: 0,
            cur_buf_end: self.buffers_len[0] - 1,
            vec: self,
            phantom_data: PhantomData::default(),
        }
    }
}

pub struct PinnedVecIterMut<'v, T> {
    cur: usize,
    cur_buf: usize,
    cur_buf_end: usize,
    vec: &'v mut PinnedVec<T>,
    phantom_data: PhantomData<&'v T>,
}

impl<'v, T> Iterator for PinnedVecIterMut<'v, T> {
    type Item = Pin<&'v mut T>;

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
            Some(Pin::new_unchecked(&mut *val))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.cur, Some(self.vec.len))
    }

    fn count(self) -> usize where Self: Sized {
        self.vec.len - self.cur
    }
}