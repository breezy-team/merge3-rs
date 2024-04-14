use difflib::sequencematcher::{Match, SequenceMatcher};

/// Given two ranges, return the range where they intersect or None.
fn intersect(ra: (usize, usize), rb: (usize, usize)) -> Option<(usize, usize)> {
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

/// Compare a[astart..aend] == b[bstart..bend], without slicing.
fn compare_range<T: PartialEq>(
    a: &[T],
    astart: usize,
    aend: usize,
    b: &[T],
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

/// 3-way merge of texts
///
/// Given BASE, OTHER, THIS, tries to produce a combined text incorporating the changes from both
/// BASE->OTHER and BASE->THIS.  All three will typically be sequences of lines.

pub struct Merge3<T: Eq + std::hash::Hash> {
    // Lines in BASE
    base: Vec<T>,
    // lines in A
    a: Vec<T>,
    // lines in B
    b: Vec<T>,
    // flag indicating if this merge is a cherrypick.  When cherrypicking b => a, matches with b
    // and base do not conflict.
    is_cherrypick: bool,
    get_matching_blocks: fn(&[T], &[T]) -> Vec<Match>,
}

impl<T: Eq + std::hash::Hash + std::fmt::Debug> Merge3<T> {
    pub fn new(base: Vec<T>, a: Vec<T>, b: Vec<T>) -> Merge3<T> {
        Merge3 {
            base,
            a,
            b,
            is_cherrypick: false,
            get_matching_blocks: |a, b| SequenceMatcher::new(a, b).get_matching_blocks(),
        }
    }

    pub fn set_cherrypick(&mut self, is_cherrypick: bool) {
        self.is_cherrypick = is_cherrypick;
    }

    /// Return sequences of matching and conflicting regions.

    /// This returns tuples, where the first value says what kind we
    /// have:

    /// SelectedRegion::Unchanged { start, end }
    ///      Take a region of base[start..end]

    /// SelectedRegion::Same { astart, aend }
    ///      b and a are different from base but give the same result

    /// SelectedRegion::A { start, end }
    ///      Non-clashing insertion from a[start..end]

    /// Method is as follows:

    /// The two sequences align only on regions which match the base
    /// and both descendents.  These are found by doing a two-way diff
    /// of each one against the base, and then finding the
    /// intersections between those regions.  These "sync regions"
    /// are by definition unchanged in both and easily dealt with.

    /// The regions in between can be in any of three cases:
    /// conflicted, or changed on only one side.
    pub fn merge_regions(&self) -> Vec<SelectedRegion> {
        let mut iz = 0;
        let mut ia = 0;
        let mut ib = 0;

        let mut ret = vec![];
        for (zmatch, zend, amatch, aend, bmatch, bend) in self.find_sync_regions() {
            let matchlen = zend - zmatch;
            // invariants:
            assert!(matchlen >= 0);
            assert_eq!(matchlen, aend - amatch);
            assert_eq!(matchlen, bend - bmatch);
            let len_a = amatch - ia;
            let len_b = bmatch - ib;
            // invariants:
            assert!(len_a >= 0);
            assert!(len_b >= 0);

            // print 'unmatched a=%d, b=%d' % (len_a, len_b)

            if len_a > 0 || len_b > 0 {
                // try to avoid actually slicing the lists
                let same =
                    compare_range(self.a.as_slice(), ia, amatch, self.b.as_slice(), ib, bmatch);

                if same {
                    ret.push(SelectedRegion::Same {
                        astart: ia,
                        aend: amatch,
                    });
                } else {
                    let equal_a = compare_range(
                        self.a.as_slice(),
                        ia,
                        amatch,
                        self.base.as_slice(),
                        iz,
                        zmatch,
                    );
                    let equal_b = compare_range(
                        self.b.as_slice(),
                        ib,
                        bmatch,
                        self.base.as_slice(),
                        iz,
                        zmatch,
                    );
                    if equal_a && !equal_b {
                        ret.push(SelectedRegion::B {
                            start: ib,
                            end: bmatch,
                        });
                    } else if equal_b && !equal_a {
                        ret.push(SelectedRegion::A {
                            start: ia,
                            end: amatch,
                        });
                    } else if !equal_a && !equal_b {
                        if self.is_cherrypick {
                            ret.extend(
                                self.refine_cherrypick_conflict(iz, zmatch, ia, amatch, ib, bmatch),
                            );
                        } else {
                            ret.push(SelectedRegion::Conflict {
                                zstart: Some(iz),
                                zend: Some(zmatch),
                                astart: ia,
                                aend: amatch,
                                bstart: ib,
                                bend: bmatch,
                            });
                        }
                    } else {
                        panic!("can't handle a=b=base but unmatched");
                    }
                }

                ia = amatch;
                ib = bmatch;
            }
            iz = zmatch;

            // if the same part of the base was deleted on both sides
            // that's OK, we can just skip it.

            if matchlen > 0 {
                // invariants:
                assert_eq!(ia, amatch);
                assert_eq!(ib, bmatch);
                assert_eq!(iz, zmatch);

                ret.push(SelectedRegion::Unchanged {
                    start: zmatch,
                    end: zend,
                });
                iz = zend;
                ia = aend;
                ib = bend;
            }
        }

        ret
    }

    /// Return list of sync regions, where both descendents match the base.
    ///
    /// Generates a list of (base1, base2, a1, a2, b1, b2).  There is
    /// always a zero-length sync region at the end of all the files.
    pub fn find_sync_regions(&self) -> Vec<(usize, usize, usize, usize, usize, usize)> {
        let mut ia = 0;
        let mut ib = 0;
        let amatches = (self.get_matching_blocks)(&self.base, &self.a);
        let bmatches = (self.get_matching_blocks)(&self.base, &self.b);

        let mut sl = vec![];

        while ia < amatches.len() && ib < bmatches.len() {
            let am = amatches[ia];
            let abase = am.first_start;
            let amatch = am.second_start;
            let alen = am.size;
            let bm = bmatches[ib];
            let bbase = bm.first_start;
            let bmatch = bm.second_start;
            let blen = bm.size;

            // there is an unconflicted block at i; how long does it
            // extend?  until whichever one ends earlier.
            if let Some(i) = intersect((abase, abase + alen), (bbase, bbase + blen)) {
                let intbase = i.0;
                let intend = i.1;
                let intlen = intend - intbase;

                // found a match of base[i[0], i[1]]; this may be less than
                // the region that matches in either one
                assert!(intlen <= alen);
                assert!(intlen <= blen);
                assert!(abase <= intbase);
                assert!(bbase <= intbase);

                let asub = amatch + (intbase - abase);
                let bsub = bmatch + (intbase - bbase);
                let aend = asub + intlen;
                let bend = bsub + intlen;

                assert_eq!(self.base[intbase..intend], self.a[asub..aend]);
                assert_eq!(self.base[intbase..intend], self.b[bsub..bend]);

                sl.push((intbase, intend, asub, aend, bsub, bend));
            }
            // advance whichever one ends first in the base text
            if (abase + alen) < (bbase + blen) {
                ia += 1;
            } else {
                ib += 1;
            }
        }

        let intbase = self.base.len();
        let abase = self.a.len();
        let bbase = self.b.len();
        sl.push((intbase, intbase, abase, abase, bbase, bbase));

        sl
    }

    /// When cherrypicking b => a, ignore matches with b and base.
    fn refine_cherrypick_conflict(
        &self,
        zstart: usize,
        zend: usize,
        astart: usize,
        aend: usize,
        bstart: usize,
        bend: usize,
    ) -> Vec<SelectedRegion> {
        // Do not emit regions which match, only regions which do not match
        let matches = (self.get_matching_blocks)(&self.base[zstart..zend], &self.b[bstart..bend]);
        let mut last_base_idx = 0;
        let mut last_b_idx = 0;
        let mut yielded_a = false;
        let mut ret = vec![];
        for m in &matches {
            let base_idx = m.first_start;
            let b_idx = m.second_start;
            let match_len = m.size;
            let conflict_b_len = b_idx - last_b_idx;
            if conflict_b_len == 0 {
                // No conflict, just a match
                continue;
            } else if yielded_a {
                ret.push(SelectedRegion::Conflict {
                    zstart: Some(zstart + last_base_idx),
                    zend: Some(zstart + base_idx),
                    astart: aend,
                    aend: aend,
                    bstart: bstart + last_b_idx,
                    bend: bstart + b_idx,
                });
            } else {
                // The first conflict gets the a-range
                yielded_a = true;
                ret.push(SelectedRegion::Conflict {
                    zstart: Some(zstart + last_base_idx),
                    zend: Some(zstart + base_idx),
                    astart: astart,
                    aend: aend,
                    bstart: bstart + last_b_idx,
                    bend: bstart + b_idx,
                });
            }
            last_base_idx = base_idx + match_len;
            last_b_idx = b_idx + match_len;
        }
        if last_base_idx != zend - zstart || last_b_idx != bend - bstart {
            if yielded_a {
                ret.push(SelectedRegion::Conflict {
                    zstart: Some(zstart + last_base_idx),
                    zend: Some(zstart + matches.last().unwrap().first_start),
                    astart: aend,
                    aend: aend,
                    bstart: bstart + last_b_idx,
                    bend: bstart + matches.last().unwrap().second_start,
                });
            } else {
                // The first conflict gets the a-range
                yielded_a = true;
                ret.push(SelectedRegion::Conflict {
                    zstart: Some(zstart + last_base_idx),
                    zend: Some(zstart + matches.last().unwrap().first_start),
                    astart: astart,
                    aend: aend,
                    bstart: bstart + last_b_idx,
                    bend: bstart + matches.last().unwrap().second_start,
                });
            }
        }
        if !yielded_a {
            ret.push(SelectedRegion::Conflict {
                zstart: Some(zstart),
                zend: Some(zend),
                astart: astart,
                aend: aend,
                bstart: bstart,
                bend: bend,
            });
        }

        ret
    }
}

enum SelectedRegion {
    Unchanged {
        start: usize,
        end: usize,
    },
    Same {
        astart: usize,
        aend: usize,
    },
    A {
        start: usize,
        end: usize,
    },
    B {
        start: usize,
        end: usize,
    },
    Conflict {
        zstart: Option<usize>,
        zend: Option<usize>,
        astart: usize,
        aend: usize,
        bstart: usize,
        bend: usize,
    },
}

fn mismatch_region<T: PartialEq + std::fmt::Debug>(
    next_a: usize,
    region_ia: usize,
    next_b: usize,
    region_ib: usize,
) -> Option<SelectedRegion> {
    if next_a < region_ia || next_b < region_ib {
        Some(SelectedRegion::Conflict {
            zstart: None,
            zend: None,
            astart: next_a,
            aend: region_ia,
            bstart: next_b,
            bend: region_ib,
        })
    } else {
        None
    }
}
