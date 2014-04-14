#![cfg(test)]

use super::HashSet;
use std::container::Container;
use std::slice::ImmutableEqVector;

#[test]
fn test_disjoint() {
    let mut xs = HashSet::new();
    let mut ys = HashSet::new();
    assert!(xs.is_disjoint(&ys));
    assert!(ys.is_disjoint(&xs));
    assert!(xs.insert(5));
    assert!(ys.insert(11));
    assert!(xs.is_disjoint(&ys));
    assert!(ys.is_disjoint(&xs));
    assert!(xs.insert(7));
    assert!(xs.insert(19));
    assert!(xs.insert(4));
    assert!(ys.insert(2));
    assert!(ys.insert(-11));
    assert!(xs.is_disjoint(&ys));
    assert!(ys.is_disjoint(&xs));
    assert!(ys.insert(7));
    assert!(!xs.is_disjoint(&ys));
    assert!(!ys.is_disjoint(&xs));
}

#[test]
fn test_subset_and_superset() {
    let mut a = HashSet::new();
    assert!(a.insert(0));
    assert!(a.insert(5));
    assert!(a.insert(11));
    assert!(a.insert(7));

    let mut b = HashSet::new();
    assert!(b.insert(0));
    assert!(b.insert(7));
    assert!(b.insert(19));
    assert!(b.insert(250));
    assert!(b.insert(11));
    assert!(b.insert(200));

    assert!(!a.is_subset(&b));
    assert!(!a.is_superset(&b));
    assert!(!b.is_subset(&a));
    assert!(!b.is_superset(&a));

    assert!(b.insert(5));

    assert!(a.is_subset(&b));
    assert!(!a.is_superset(&b));
    assert!(!b.is_subset(&a));
    assert!(b.is_superset(&a));
}

#[test]
fn test_iterate() {
    let mut a = HashSet::new();
    for i in range(0u, 32) {
        assert!(a.insert(i));
    }
    let mut observed = 0;
    for k in a.iter() {
        observed |= 1 << *k;
    }
    assert_eq!(observed, 0xFFFF_FFFF);
}

#[test]
fn test_intersection() {
    let mut a = HashSet::new();
    let mut b = HashSet::new();

    assert!(a.insert(11));
    assert!(a.insert(1));
    assert!(a.insert(3));
    assert!(a.insert(77));
    assert!(a.insert(103));
    assert!(a.insert(5));
    assert!(a.insert(-5));

    assert!(b.insert(2));
    assert!(b.insert(11));
    assert!(b.insert(77));
    assert!(b.insert(-9));
    assert!(b.insert(-42));
    assert!(b.insert(5));
    assert!(b.insert(3));

    let mut i = 0;
    let expected = [3, 5, 11, 77];
    for x in a.intersection(&b) {
        assert!(expected.contains(x));
        i += 1
    }
    assert_eq!(i, expected.len());
}

#[test]
fn test_difference() {
    let mut a = HashSet::new();
    let mut b = HashSet::new();

    assert!(a.insert(1));
    assert!(a.insert(3));
    assert!(a.insert(5));
    assert!(a.insert(9));
    assert!(a.insert(11));

    assert!(b.insert(3));
    assert!(b.insert(9));

    let mut i = 0;
    let expected = [1, 5, 11];
    for x in a.difference(&b) {
        assert!(expected.contains(x));
        i += 1
    }
    assert_eq!(i, expected.len());
}

#[test]
fn test_symmetric_difference() {
    let mut a = HashSet::new();
    let mut b = HashSet::new();

    assert!(a.insert(1));
    assert!(a.insert(3));
    assert!(a.insert(5));
    assert!(a.insert(9));
    assert!(a.insert(11));

    assert!(b.insert(-2));
    assert!(b.insert(3));
    assert!(b.insert(9));
    assert!(b.insert(14));
    assert!(b.insert(22));

    let mut i = 0;
    let expected = [-2, 1, 5, 11, 14, 22];
    for x in a.symmetric_difference(&b) {
        assert!(expected.contains(x));
        i += 1
    }
    assert_eq!(i, expected.len());
}

#[test]
fn test_union() {
    let mut a = HashSet::new();
    let mut b = HashSet::new();

    assert!(a.insert(1));
    assert!(a.insert(3));
    assert!(a.insert(5));
    assert!(a.insert(9));
    assert!(a.insert(11));
    assert!(a.insert(16));
    assert!(a.insert(19));
    assert!(a.insert(24));

    assert!(b.insert(-2));
    assert!(b.insert(1));
    assert!(b.insert(5));
    assert!(b.insert(9));
    assert!(b.insert(13));
    assert!(b.insert(19));

    let mut i = 0;
    let expected = [-2, 1, 3, 5, 9, 11, 13, 16, 19, 24];
    for x in a.union(&b) {
        assert!(expected.contains(x));
        i += 1
    }
    assert_eq!(i, expected.len());
}

#[test]
fn test_from_iter() {
    let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];

    let set: HashSet<int> = xs.iter().map(|&x| x).collect();

    for x in xs.iter() {
        assert!(set.contains(x));
    }
}

#[test]
fn test_move_iter() {
    let hs = {
        let mut hs = HashSet::new();

        hs.insert('a');
        hs.insert('b');

        hs
    };

    let v = hs.move_iter().collect::<Vec<char>>();
    assert!(['a', 'b'] == v.as_slice() || ['b', 'a'] == v.as_slice());
}

#[test]
fn test_eq() {
    // These constants once happened to expose a bug in insert().
    // I'm keeping them around to prevent a regression.
    let mut s1 = HashSet::new();

    s1.insert(1);
    s1.insert(2);
    s1.insert(3);

    let mut s2 = HashSet::new();

    s2.insert(1);
    s2.insert(2);

    assert!(s1 != s2);

    s2.insert(3);

    assert_eq!(s1, s2);
}

#[test]
fn test_show() {
    let mut set: HashSet<int> = HashSet::new();
    let empty: HashSet<int> = HashSet::new();

    set.insert(1);
    set.insert(2);

    let set_str = format!("{}", set);

    assert!(set_str == ~"{1, 2}" || set_str == ~"{2, 1}");
    assert_eq!(format!("{}", empty), ~"{}");
}
