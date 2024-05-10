
pub mod prelude {
    #[cfg(feature = "pinned-vector")]
    #[cfg_attr(docsrs, doc(cfg(feature = "pinned-vector")))]
    pub use pinned_vector::*;
}

#[cfg(test)]
mod tests {
    use super::prelude::*;

    #[test]
    fn can_access_pinned_vector() {
        let vec: PinnedVec<i32> = PinnedVec::new(0);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.capacity(), 0);
    }
}
