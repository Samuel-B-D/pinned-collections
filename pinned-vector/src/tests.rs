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
        assert_eq!(vec.get_unpin(1), &2);
        assert_eq!(vec.get_unpin(2), &3);
        assert_eq!(vec.get_unpin(3), &4);
        assert_eq!(vec.get_unpin(4), &5);
        assert_eq!(vec.get_unpin(5), &6);
        assert_eq!(vec.get_unpin(6), &7);
        vec.iter_mut().for_each(|mut v| v.as_mut().add_assign(1));
        for x in vec.iter() {
            println!("{x}");
        }
    }
}
