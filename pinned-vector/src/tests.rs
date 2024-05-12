#[cfg(test)]
mod tests {
    use std::ops::AddAssign;
    use super::super::*;

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

    #[test]
    fn basic_push() {
        let mut vec = PinnedVec::from(vec!["1".to_string(), "2".to_string()]);
        assert_eq!(vec.len(), 2);
        assert_eq!(vec.get(0).as_str(), "1");
        assert_eq!(vec.get(1).as_str(), "2");
        vec.push("3".to_string());
        assert_eq!(vec.len(), 3);
        assert_eq!(vec.get(0).as_str(), "1");
        assert_eq!(vec.get(1).as_str(), "2");
        assert_eq!(vec.get(2).as_str(), "3");
    }

    #[test]
    fn shrink() {
        let mut vec = PinnedVec::new(10);
        vec.push(1);
        vec.push(2);
        vec.push(3);
        assert!(vec.capacity() >= 10);
        vec.shrink_to_fit();
        assert_eq!(vec.capacity(), 3);
    }

    #[test]
    fn iter() {
        let mut vec = PinnedVec::from(vec![1, 2]);
        vec.push(3);
        vec.push(4);
        vec.push(5);
        vec.push(6);
        vec.push(7);
        assert_eq!(vec.get_unpin(0), &1);
        assert_eq!(vec.get(1).get_ref(), &2);
        assert_eq!(*vec.get(2).get_ref(), 3);
        assert_eq!(*vec.get_unpin(3), 4);
        assert_eq!(vec[4], 5);
        assert_eq!(vec[5], 6);
        assert_eq!(vec.get_unpin(6), &7);
        vec.iter_mut().for_each(|mut v| v.as_mut().add_assign(1));
        for x in vec.iter() {
            println!("{x}");
        }
    }

    #[test]
    fn debug_print() {
        let vec = PinnedVec::from(vec![1, 2, 3]);
        let dbg = format!("{vec:?}");
        assert_eq!(dbg.as_str(), "[1, 2, 3]");
    }

    #[test]
    fn grow_from_zeroed_capacity() {
        let mut vec = PinnedVec::new(0);
        vec.push(1);
        vec.push(2);
        vec.push(3);
        vec.push(4);
        assert_eq!(format!("{vec:?}").as_str(), "[1, 2, 3, 4]");
    }

    #[test]
    fn from_iter() {
        let vec = vec![2, 4, 5, 6];
        let pinned_vec: PinnedVec<_> = vec.into_iter().collect();
        assert_eq!(format!("{pinned_vec:?}").as_str(), "[2, 4, 5, 6]");
    }

    #[test]
    fn is_contiguous_from_vec() {
        let vec: PinnedVec<usize> = PinnedVec::from(vec![]);
        assert!(vec.is_contiguous());

        let vec = PinnedVec::from(vec![1]);
        assert!(vec.is_contiguous());

        let vec = PinnedVec::from(vec!["a", "b", "c"]);
        assert!(vec.is_contiguous());
    }

    #[test]
    fn is_contiguous_from_iter() {
        let vec = vec![2, 4, 5, 6];
        let pinned_vec: PinnedVec<_> = vec.into_iter().collect();
        assert!(pinned_vec.is_contiguous());
    }
}
