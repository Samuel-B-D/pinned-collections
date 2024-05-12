use std::marker::PhantomData;
use super::*;

impl<T> PinnedVec<T> {
    pub fn iter(&self) -> PinnedVecIter<T> {
       self.into_iter()
    }
}

impl<'v, T> IntoIterator for &'v PinnedVec<T> {
    type Item = &'v T;
    type IntoIter = PinnedVecIter<'v, T>;

    fn into_iter(self) -> Self::IntoIter {
        PinnedVecIter {
            cur: 0,
            cur_buf: 0,
            cur_buf_end: self.buffers_len[0] - 1,
            vec: self,
            phantom_data: PhantomData::default(),
        }
    }
}

pub struct PinnedVecIter<'v, T> {
    cur: usize,
    cur_buf: usize,
    cur_buf_end: usize,
    vec: &'v PinnedVec<T>,
    phantom_data: PhantomData<&'v T>,
}

impl<'v, T> Iterator for PinnedVecIter<'v, T> {
    type Item = &'v T;

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
            let val: *const T = self.vec.buffers[self.cur_buf].ptr().add(self.cur);
            self.cur += 1;
            Some(&*val)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.cur, Some(self.vec.len))
    }

    fn count(self) -> usize where Self: Sized {
        self.vec.len - self.cur
    }
}