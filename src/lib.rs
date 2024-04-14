/// Given two ranges, return the range where they intersect or None.
fn intersect(ra: (i32, i32), rb: (i32, i32)) -> Option<(i32, i32)> {
    // Preconditions: (ra.0 <= ra.1) and (rb.0 <= rb.1)
    let sa = ra.0.max(rb.0);
    let sb = ra.1.min(rb.1);
    if sa < sb {
        Some((sa, sb))
    } else {
        None
    }
}

#[cfg(test)]
mod intersect_tests {
    use super::intersect;

    #[test]
    fn test_intersect() {
        assert_eq!(intersect((0, 10), (0, 6)), Some((0, 6)));
        assert_eq!(intersect((0, 10), (5, 15)), Some((5, 10)));
        assert_eq!(intersect((0, 10), (10, 15)), None);
        assert_eq!(intersect((0, 9), (10, 15)), None);
        assert_eq!(intersect((0, 9), (7, 15)), Some((7, 9)));
    }
}

/// Compare a[astart:aend] == b[bstart:bend], without slicing.
fn compare_range(
    a: &[i32],
    astart: usize,
    aend: usize,
    b: &[i32],
    bstart: usize,
    bend: usize,
) -> bool {
    if (aend - astart) != (bend - bstart) {
        return false;
    }
    for (ia, ib) in (astart..aend).zip(bstart..bend) {
        if a[ia] != b[ib] {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod compare_range_tests {
    use super::compare_range;

    #[test]
    fn test_compare_range() {
        let a = [1, 2, 3, 4, 5];
        let b = [1, 2, 3, 4, 5];
        assert!(compare_range(&a, 0, 5, &b, 0, 5));
        assert!(compare_range(&a, 0, 3, &b, 0, 3));
        assert!(!compare_range(&a, 0, 3, &b, 0, 4));
        assert!(!compare_range(&a, 0, 3, &b, 1, 4));
    }
}
