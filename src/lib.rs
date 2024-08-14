use difflib::sequencematcher::{Match, SequenceMatcher};
use std::borrow::Cow;

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

/// 3-way merge of texts
///
/// Given BASE, OTHER, THIS, tries to produce a combined text incorporating the changes from both
/// BASE->OTHER and BASE->THIS.  All three will typically be sequences of lines.

pub struct Merge3<'b, T: Eq + std::hash::Hash + ?Sized> {
    // Lines in BASE
    base: &'b [&'b T],
    // lines in A
    a: &'b [&'b T],
    // lines in B
    b: &'b [&'b T],
    // flag indicating if this merge is a cherrypick.  When cherrypicking b => a, matches with b
    // and base do not conflict.
    is_cherrypick: bool,
    get_matching_blocks: fn(&[&T], &[&T]) -> Vec<Match>,
}

impl<'b, T: Eq + std::hash::Hash + std::fmt::Debug + ?Sized> Merge3<'b, T> {
    pub fn new(base: &'b [&'b T], a: &'b [&'b T], b: &'b [&'b T]) -> Merge3<'b, T> {
        Merge3 {
            base,
            a,
            b,
            is_cherrypick: false,
            get_matching_blocks: |a, b| SequenceMatcher::new(a, b).get_matching_blocks(),
        }
    }

    #[cfg(feature = "patiencediff")]
    pub fn with_patience_diff(base: &'b [&'b T], a: &'b [&'b T], b: &'b [&'b T]) -> Merge3<'b, T> {
        Merge3 {
            base,
            a,
            b,
            is_cherrypick: false,
            get_matching_blocks: |a, b| {
                patiencediff::SequenceMatcher::new(a, b)
                    .get_matching_blocks()
                    .iter()
                    .map(|(first_start, second_start, size)| Match {
                        first_start: *first_start,
                        second_start: *second_start,
                        size: *size,
                    })
                    .collect()
            },
        }
    }

    pub fn set_cherrypick(&mut self, is_cherrypick: bool) {
        self.is_cherrypick = is_cherrypick;
    }

    /// Return sequences of matching and conflicting regions.

    /// This returns tuples, where the first value says what kind we
    /// have:

    /// MergeRegion::Unchanged { start, end }
    ///      Take a region of base[start..end]

    /// MergeRegion::Same { astart, aend }
    ///      b and a are different from base but give the same result

    /// MergeRegion::A { start, end }
    ///      Non-clashing insertion from a[start..end]

    /// Method is as follows:

    /// The two sequences align only on regions which match the base
    /// and both descendents.  These are found by doing a two-way diff
    /// of each one against the base, and then finding the
    /// intersections between those regions.  These "sync regions"
    /// are by definition unchanged in both and easily dealt with.

    /// The regions in between can be in any of three cases:
    /// conflicted, or changed on only one side.
    pub fn merge_regions(&self) -> Vec<MergeRegion> {
        let mut iz = 0;
        let mut ia = 0;
        let mut ib = 0;

        let mut ret = vec![];
        for (zmatch, zend, amatch, aend, bmatch, bend) in self.find_sync_regions() {
            let matchlen = zend - zmatch;
            // invariants:
            assert_eq!(matchlen, aend - amatch);
            assert_eq!(matchlen, bend - bmatch);
            let len_a = amatch - ia;
            let len_b = bmatch - ib;

            // print 'unmatched a=%d, b=%d' % (len_a, len_b)

            if len_a > 0 || len_b > 0 {
                // try to avoid actually slicing the lists
                let same = compare_range(self.a, ia, amatch, self.b, ib, bmatch);

                if same {
                    ret.push(MergeRegion::Same {
                        astart: ia,
                        aend: amatch,
                    });
                } else {
                    let equal_a = compare_range(self.a, ia, amatch, self.base, iz, zmatch);
                    let equal_b = compare_range(self.b, ib, bmatch, self.base, iz, zmatch);
                    if equal_a && !equal_b {
                        ret.push(MergeRegion::B {
                            start: ib,
                            end: bmatch,
                        });
                    } else if equal_b && !equal_a {
                        ret.push(MergeRegion::A {
                            start: ia,
                            end: amatch,
                        });
                    } else if !equal_a && !equal_b {
                        if self.is_cherrypick {
                            ret.extend(
                                self.refine_cherrypick_conflict(iz, zmatch, ia, amatch, ib, bmatch),
                            );
                        } else {
                            ret.push(MergeRegion::Conflict {
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

                ret.push(MergeRegion::Unchanged {
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
        let amatches = (self.get_matching_blocks)(self.base, self.a);
        let bmatches = (self.get_matching_blocks)(self.base, self.b);

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
    ) -> Vec<MergeRegion> {
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
                ret.push(MergeRegion::Conflict {
                    zstart: Some(zstart + last_base_idx),
                    zend: Some(zstart + base_idx),
                    astart: aend,
                    aend,
                    bstart: bstart + last_b_idx,
                    bend: bstart + b_idx,
                });
            } else {
                // The first conflict gets the a-range
                yielded_a = true;
                ret.push(MergeRegion::Conflict {
                    zstart: Some(zstart + last_base_idx),
                    zend: Some(zstart + base_idx),
                    astart,
                    aend,
                    bstart: bstart + last_b_idx,
                    bend: bstart + b_idx,
                });
            }
            last_base_idx = base_idx + match_len;
            last_b_idx = b_idx + match_len;
        }
        if last_base_idx != zend - zstart || last_b_idx != bend - bstart {
            if yielded_a {
                ret.push(MergeRegion::Conflict {
                    zstart: Some(zstart + last_base_idx),
                    zend: Some(zstart + matches.last().unwrap().first_start),
                    astart: aend,
                    aend,
                    bstart: bstart + last_b_idx,
                    bend: bstart + matches.last().unwrap().second_start,
                });
            } else {
                // The first conflict gets the a-range
                yielded_a = true;
                ret.push(MergeRegion::Conflict {
                    zstart: Some(zstart + last_base_idx),
                    zend: Some(zstart + matches.last().unwrap().first_start),
                    astart,
                    aend,
                    bstart: bstart + last_b_idx,
                    bend: bstart + matches.last().unwrap().second_start,
                });
            }
        }
        if !yielded_a {
            ret.push(MergeRegion::Conflict {
                zstart: Some(zstart),
                zend: Some(zend),
                astart,
                aend,
                bstart,
                bend,
            });
        }

        ret
    }

    /// Return a list of ranges in base that are not conflicted.
    pub fn find_unconflicted(&self) -> Vec<(usize, usize)> {
        let mut am = (self.get_matching_blocks)(self.base, self.a);
        let mut bm = (self.get_matching_blocks)(self.base, self.b);

        let mut ret = vec![];

        while !am.is_empty() && !bm.is_empty() {
            // there is an unconflicted block at i; how long does it extend?  until whichever one
            // ends earlier.
            let a1 = am[0].first_start;
            let a2 = am[0].first_start + am[0].size;
            let b1 = bm[0].first_start;
            let b2 = bm[0].first_start + bm[0].size;

            let i = intersect((a1, a2), (b1, b2));

            if let Some(entry) = i {
                ret.push(entry);
            }

            if a2 < b2 {
                am.remove(0);
            } else {
                bm.remove(0);
            }
        }
        ret
    }

    /// Where there are conflict regions, remove the agreed lines.
    ///
    /// Lines where both A and B have made the same changes are
    /// eliminated.
    pub fn reprocess_merge_regions(&self, merge_regions: Vec<MergeRegion>) -> Vec<MergeRegion> {
        let mut ret = vec![];
        for region in merge_regions {
            if let MergeRegion::Conflict {
                zstart: _,
                zend: _,
                astart,
                aend,
                bstart,
                bend,
            } = region
            {
                let a_region = &self.a[astart..aend];
                let b_region = &self.b[bstart..bend];
                let mut matches = (self.get_matching_blocks)(a_region, b_region);
                let mut next_a = astart;
                let mut next_b = bstart;
                // Drop last item from matches
                matches.pop();
                for m in matches {
                    let region_ia = m.first_start + astart;
                    let region_ib = m.second_start + bstart;

                    if let Some(reg) = mismatch_region(next_a, region_ia, next_b, region_ib) {
                        ret.push(reg);
                    }

                    ret.push(MergeRegion::Unchanged {
                        start: region_ia,
                        end: region_ia + m.size,
                    });

                    next_a = region_ia + m.size;
                    next_b = region_ib + m.size;
                }

                if let Some(reg) = mismatch_region(next_a, aend, next_b, bend) {
                    ret.push(reg);
                }
            } else {
                ret.push(region);
            }
        }
        ret
    }

    /// Yield sequence of line groups.  Each one is a tuple:
    ///
    /// 'unchanged', lines
    ///      Lines unchanged from base
    ///
    /// 'a', lines
    ///      Lines taken from a
    ///
    /// 'same', lines
    ///      Lines taken from a (and equal to b)
    ///
    /// 'b', lines
    ///      Lines taken from b
    ///
    /// 'conflict', base_lines, a_lines, b_lines
    ///      Lines from base were changed to either a or b and conflict.
    pub fn merge_groups(&self) -> Vec<MergeGroup<'_, &T>> {
        let mut ret = vec![];
        for m in self.merge_regions() {
            match m {
                MergeRegion::Unchanged { start, end } => {
                    ret.push(MergeGroup::Unchanged(&self.base[start..end]));
                }
                MergeRegion::Same { astart, aend } => {
                    ret.push(MergeGroup::Same(&self.a[astart..aend]));
                }
                MergeRegion::A { start, end } => {
                    ret.push(MergeGroup::A(&self.a[start..end]));
                }
                MergeRegion::B { start, end } => {
                    ret.push(MergeGroup::B(&self.b[start..end]));
                }
                MergeRegion::Conflict {
                    zstart,
                    zend,
                    astart,
                    aend,
                    bstart,
                    bend,
                } => {
                    let base_lines = zstart.map(|zstart| &self.base[zstart..zend.unwrap()]);
                    let a_lines = &self.a[astart..aend];
                    let b_lines = &self.b[bstart..bend];
                    ret.push(MergeGroup::Conflict(base_lines, a_lines, b_lines));
                }
            }
        }
        ret
    }

    /// Return merge in CVS-style format.
    ///
    /// # Arguments
    /// * `reprocess` - If true, remove lines where a and b are the same.
    /// * `markers` - LineMarkers implementation to provide markers for the merge.
    pub fn merge_lines<'a>(
        &'b self,
        reprocess: bool,
        markers: &impl LineMarkers<'a, T>,
    ) -> Vec<std::borrow::Cow<'a, T>>
    where
        T: ToOwned,
        'b: 'a,
    {
        let mut merge_regions = self.merge_regions();
        if reprocess {
            merge_regions = self.reprocess_merge_regions(merge_regions);
            assert!(
                markers.base_marker().is_none(),
                "base marker in reprocessed merge"
            );
        }
        let mut ret: Vec<std::borrow::Cow<T>> = vec![];
        for m in merge_regions {
            match m {
                MergeRegion::Unchanged { start, end } => {
                    for i in start..end {
                        ret.push(std::borrow::Cow::Borrowed(self.base[i]));
                    }
                }
                MergeRegion::Same { astart, aend } => {
                    for i in astart..aend {
                        ret.push(std::borrow::Cow::Borrowed(self.a[i]));
                    }
                }
                MergeRegion::A { start, end } => {
                    for i in start..end {
                        ret.push(std::borrow::Cow::Borrowed(self.a[i]));
                    }
                }
                MergeRegion::B { start, end } => {
                    for i in start..end {
                        ret.push(std::borrow::Cow::Borrowed(self.b[i]));
                    }
                }
                MergeRegion::Conflict {
                    zstart,
                    zend,
                    astart,
                    aend,
                    bstart,
                    bend,
                } => {
                    if let Some(start_marker) = markers.start_marker() {
                        ret.push(start_marker);
                    }
                    for i in astart..aend {
                        ret.push(std::borrow::Cow::Borrowed(self.a[i]));
                    }
                    if let Some(zstart) = zstart {
                        if let Some(base_marker) = markers.base_marker() {
                            ret.push(base_marker);
                        }
                        for i in zstart..zend.unwrap() {
                            ret.push(std::borrow::Cow::Borrowed(self.base[i]));
                        }
                    }
                    if let Some(mid_marker) = markers.mid_marker() {
                        ret.push(mid_marker);
                    }
                    for i in bstart..bend {
                        ret.push(std::borrow::Cow::Borrowed(self.b[i]));
                    }
                    if let Some(end_marker) = markers.end_marker() {
                        ret.push(end_marker);
                    }
                }
            }
        }
        ret
    }

    /// Return merge with conflicts, showing origin of lines.
    ///
    /// Most useful for debugging merge.
    pub fn merge_annotated<'a>(&self, markers: &impl AnnotationMarkers<'a, T>) -> Vec<T>
    where
        T: Clone,
    {
        let mut ret = vec![];
        for m in self.merge_regions() {
            match m {
                MergeRegion::Unchanged { start, end } => {
                    for i in start..end {
                        ret.push(markers.unchanged_line(self.base[i]));
                    }
                }
                MergeRegion::Same { astart, aend } => {
                    for i in astart..aend {
                        ret.push(markers.a_line(self.a[i]));
                    }
                }
                MergeRegion::A { start, end } => {
                    for i in start..end {
                        ret.push(markers.a_line(self.a[i]));
                    }
                }
                MergeRegion::B { start, end } => {
                    for i in start..end {
                        ret.push(markers.b_line(self.b[i]));
                    }
                }
                MergeRegion::Conflict {
                    zstart,
                    zend,
                    astart,
                    aend,
                    bstart,
                    bend,
                } => {
                    ret.push(markers.start_marker());
                    for i in astart..aend {
                        ret.push(markers.a_line(self.a[i]));
                    }
                    if let Some(zstart) = zstart {
                        ret.push(markers.base_marker());
                        for i in zstart..zend.unwrap() {
                            ret.push(markers.base_line(self.base[i]));
                        }
                    }
                    ret.push(markers.mid_marker());
                    for i in bstart..bend {
                        ret.push(markers.b_line(self.b[i]));
                    }
                    ret.push(markers.end_marker());
                }
            }
        }
        ret
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum MergeRegion {
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

#[derive(Debug, PartialEq, Eq)]
pub enum MergeGroup<'a, T: Eq> {
    /// Unchanged region
    Unchanged(&'a [T]),

    /// Region where a and b are the same
    Same(&'a [T]),

    /// Region where a is different from base
    A(&'a [T]),

    /// Region where b is different from base
    B(&'a [T]),

    /// Conflict region
    Conflict(Option<&'a [T]>, &'a [T], &'a [T]),
}

fn mismatch_region(
    next_a: usize,
    region_ia: usize,
    next_b: usize,
    region_ib: usize,
) -> Option<MergeRegion> {
    if next_a < region_ia || next_b < region_ib {
        Some(MergeRegion::Conflict {
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

pub trait LineMarkers<'a, T: ToOwned + ?Sized> {
    fn start_marker(&self) -> Option<Cow<'a, T>>;
    fn base_marker(&self) -> Option<Cow<'a, T>>;
    fn mid_marker(&self) -> Option<Cow<'a, T>>;
    fn end_marker(&self) -> Option<Cow<'a, T>>;
}

#[derive(Default)]
pub struct FixedMarkers<'a> {
    other_name: Option<&'a str>,
    this_name: Option<&'a str>,
    base_name: Option<&'a str>,
}

impl<'a> FixedMarkers<'a> {
    pub fn new(
        other_name: Option<&'a str>,
        this_name: Option<&'a str>,
        base_name: Option<&'a str>,
    ) -> Self {
        FixedMarkers {
            other_name,
            this_name,
            base_name,
        }
    }
}

impl<'a> LineMarkers<'a, str> for FixedMarkers<'a> {
    fn start_marker(&self) -> Option<Cow<'a, str>> {
        if let Some(name) = self.other_name {
            Some(Cow::Owned(format!("<<<<<<< {}\n", name)))
        } else {
            Some(Cow::Borrowed("<<<<<<<\n"))
        }
    }

    fn base_marker(&self) -> Option<Cow<'a, str>> {
        if let Some(name) = self.base_name {
            Some(Cow::Owned(format!("======= {}\n", name)))
        } else {
            Some(Cow::Borrowed("=======\n"))
        }
    }

    fn mid_marker(&self) -> Option<Cow<'a, str>> {
        None
    }

    fn end_marker(&self) -> Option<Cow<'a, str>> {
        if let Some(name) = self.this_name {
            Some(Cow::Owned(format!(">>>>>>> {}\n", name)))
        } else {
            Some(Cow::Borrowed(">>>>>>>\n"))
        }
    }
}

impl<'a> LineMarkers<'a, [u8]> for FixedMarkers<'a> {
    fn start_marker(&self) -> Option<Cow<'a, [u8]>> {
        if let Some(name) = self.other_name {
            Some(Cow::Owned(format!("<<<<<<< {}\n", name).into_bytes()))
        } else {
            Some(Cow::Borrowed("<<<<<<<\n".as_bytes()))
        }
    }

    fn base_marker(&self) -> Option<Cow<'a, [u8]>> {
        if let Some(name) = self.base_name {
            Some(Cow::Owned(format!("======= {}\n", name).into_bytes()))
        } else {
            Some(Cow::Borrowed("=======\n".as_bytes()))
        }
    }

    fn mid_marker(&self) -> Option<Cow<'a, [u8]>> {
        None
    }

    fn end_marker(&self) -> Option<Cow<'a, [u8]>> {
        if let Some(name) = self.this_name {
            Some(Cow::Owned(format!(">>>>>>> {}\n", name).into_bytes()))
        } else {
            Some(Cow::Borrowed(">>>>>>>\n".as_bytes()))
        }
    }
}

#[derive(Default)]
pub struct CustomMarkers<'a> {
    pub start_marker: Option<&'a str>,
    pub base_marker: Option<&'a str>,
    pub mid_marker: Option<&'a str>,
    pub end_marker: Option<&'a str>,
}

impl<'a> CustomMarkers<'a> {
    pub fn new(
        start_marker: Option<&'a str>,
        base_marker: Option<&'a str>,
        mid_marker: Option<&'a str>,
        end_marker: Option<&'a str>,
    ) -> Self {
        CustomMarkers {
            start_marker,
            base_marker,
            mid_marker,
            end_marker,
        }
    }
}

impl<'a> LineMarkers<'a, str> for CustomMarkers<'a> {
    fn start_marker(&self) -> Option<Cow<'a, str>> {
        self.start_marker.map(Cow::Borrowed)
    }

    fn base_marker(&self) -> Option<Cow<'a, str>> {
        self.base_marker.map(Cow::Borrowed)
    }

    fn mid_marker(&self) -> Option<Cow<'a, str>> {
        self.mid_marker.map(Cow::Borrowed)
    }

    fn end_marker(&self) -> Option<Cow<'a, str>> {
        self.end_marker.map(Cow::Borrowed)
    }
}

impl<'a> LineMarkers<'a, [u8]> for CustomMarkers<'a> {
    fn start_marker(&self) -> Option<Cow<'a, [u8]>> {
        self.start_marker.map(|s| Cow::Borrowed(s.as_bytes()))
    }

    fn base_marker(&self) -> Option<Cow<'a, [u8]>> {
        self.base_marker.map(|s| Cow::Borrowed(s.as_bytes()))
    }

    fn mid_marker(&self) -> Option<Cow<'a, [u8]>> {
        self.mid_marker.map(|s| Cow::Borrowed(s.as_bytes()))
    }

    fn end_marker(&self) -> Option<Cow<'a, [u8]>> {
        self.end_marker.map(|s| Cow::Borrowed(s.as_bytes()))
    }
}

pub trait AnnotationMarkers<'a, T> {
    fn unchanged_line(&self, line: &T) -> T;
    fn a_line(&self, line: &T) -> T;
    fn b_line(&self, line: &T) -> T;
    fn base_line(&self, line: &T) -> T;
    fn start_marker(&self) -> T;
    fn base_marker(&self) -> T;
    fn mid_marker(&self) -> T;
    fn end_marker(&self) -> T;
}

#[cfg(test)]
mod merge3_tests {
    use super::*;
    use pretty_assertions::assert_eq;

    const TZU: &str = r###"     The Nameless is the origin of Heaven and Earth;
     The named is the mother of all things.

     Therefore let there always be non-being,
       so we may see their subtlety,
     And let there always be being,
       so we may see their outcome.
     The two are the same,
     But after they are produced,
       they have different names.
     They both may be called deep and profound.
     Deeper and more profound,
     The door of all subtleties!
"###;

    const LAO: &str = r###"     The Way that can be told of is not the eternal Way;
     The name that can be named is not the eternal name.
     The Nameless is the origin of Heaven and Earth;
     The Named is the mother of all things.
     Therefore let there always be non-being,
       so we may see their subtlety,
     And let there always be being,
       so we may see their outcome.
     The two are the same,
     But after they are produced,
       they have different names.
"###;

    const TAO: &str = r###"     The Way that can be told of is not the eternal Way;
     The name that can be named is not the eternal name.
     The Nameless is the origin of Heaven and Earth;
     The named is the mother of all things.

     Therefore let there always be non-being,
       so we may see their subtlety,
     And let there always be being,
       so we may see their result.
     The two are the same,
     But after they are produced,
       they have different names.

       -- The Way of Lao-Tzu, tr. Wing-tsit Chan

"###;

    const MERGED_RESULT: &str = r###"     The Way that can be told of is not the eternal Way;
     The name that can be named is not the eternal name.
     The Nameless is the origin of Heaven and Earth;
     The Named is the mother of all things.
     Therefore let there always be non-being,
       so we may see their subtlety,
     And let there always be being,
       so we may see their result.
     The two are the same,
     But after they are produced,
       they have different names.
<<<<<<< LAO
=======

       -- The Way of Lao-Tzu, tr. Wing-tsit Chan

>>>>>>> TAO
"###;

    fn splitlines(s: &str) -> Vec<&str> {
        // Initialize an empty vector to store the result
        let mut result = Vec::new();

        // Initialize variables to track the start and end indices of each line
        let mut start = 0;
        let mut end = 0;

        // Iterate over the characters in the string
        while end < s.len() {
            // Check if the current character is a newline character
            if s[end..].starts_with('\n') {
                // Check if the previous character is a carriage return
                // Include the carriage return in the line
                result.push(&s[start..end + 1]);

                // Move the start index to the next character after the newline
                start = end + 1;
            }
            // Move to the next character
            end += 1;
        }

        // Add the last line if it's not empty
        if start < s.len() {
            result.push(&s[start..]);
        }

        // Return the vector of lines
        result
    }

    #[test]
    fn test_splitlines_unix_style() {
        let input = "hello\nworld\nhow are you\n";
        let expected = vec!["hello\n", "world\n", "how are you\n"];
        assert_eq!(splitlines(input), expected);
    }

    #[test]
    fn test_splitlines_windows_style() {
        let input = "hello\r\nworld\r\nhow are you\r\n";
        let expected = vec!["hello\r\n", "world\r\n", "how are you\r\n"];
        assert_eq!(splitlines(input), expected);
    }

    #[test]
    fn test_splitlines_mixed_style() {
        let input = "hello\nworld\r\nhow are you\r";
        let expected = vec!["hello\n", "world\r\n", "how are you\r"];
        assert_eq!(splitlines(input), expected);
    }

    #[test]
    fn test_splitlines_empty_input() {
        let input = "";
        let expected: Vec<&str> = vec![];
        assert_eq!(splitlines(input), expected);
    }

    #[test]
    fn test_splitlines_single_line_input() {
        let input = "hello world";
        let expected = vec!["hello world"];
        assert_eq!(splitlines(input), expected);
    }

    #[test]
    fn test_splitlines_whitespace_input() {
        let input = "\nhello world\n";
        let expected = vec!["\n", "hello world\n"];
        assert_eq!(splitlines(input), expected);
    }

    #[test]
    fn test_splitlines_multiple_empty_lines() {
        let input = "\n\n\n";
        let expected = vec!["\n", "\n", "\n"];
        assert_eq!(splitlines(input), expected);
    }

    /// No conflicts because nothing changed.
    #[test]
    fn test_no_changes() {
        let m3 = Merge3::new(&["aaa", "bbb"], &["aaa", "bbb"], &["aaa", "bbb"]);

        assert_eq!(m3.find_unconflicted(), vec![(0, 2)]);

        assert_eq!(
            m3.find_sync_regions(),
            vec![(0, 2, 0, 2, 0, 2), (2, 2, 2, 2, 2, 2)]
        );

        assert_eq!(
            m3.merge_regions(),
            vec![MergeRegion::Unchanged { start: 0, end: 2 }]
        );

        assert_eq!(
            m3.merge_groups(),
            vec![MergeGroup::Unchanged(&["aaa", "bbb"])]
        );
    }

    #[test]
    fn test_front_insert() {
        let m3 = Merge3::new(&["zz"], &["aaa", "bbb", "zz"], &["zz"]);

        // todo: should use a sentinal at end as from get_matching_blocks to match without zz
        assert_eq!(
            m3.find_sync_regions(),
            vec![(0, 1, 2, 3, 0, 1), (1, 1, 3, 3, 1, 1),]
        );

        assert_eq!(
            m3.merge_regions(),
            vec![
                MergeRegion::A { start: 0, end: 2 },
                MergeRegion::Unchanged { start: 0, end: 1 }
            ]
        );

        assert_eq!(
            m3.merge_groups(),
            vec![
                MergeGroup::A(&["aaa", "bbb"]),
                MergeGroup::Unchanged(&["zz"])
            ]
        );
    }

    #[test]
    fn test_null_insert() {
        let m3 = Merge3::new(&[], &["aaa", "bbb"], &[]);

        // todo: should use a sentinal at end as from get_matching_blocks to match without zz
        assert_eq!(m3.find_sync_regions(), vec![(0, 0, 2, 2, 0, 0)]);

        assert_eq!(
            m3.merge_regions(),
            vec![MergeRegion::A { start: 0, end: 2 }]
        );

        assert_eq!(
            m3.merge_lines(false, &FixedMarkers::default()),
            vec!["aaa", "bbb"]
        );
    }

    /// No conflicts because only one side changed.
    #[test]
    fn test_no_conflicts() {
        let m3 = Merge3::new(&["aaa", "bbb"], &["aaa", "111", "bbb"], &["aaa", "bbb"]);

        assert_eq!(m3.find_unconflicted(), vec![(0, 1), (1, 2)]);

        assert_eq!(
            m3.find_sync_regions(),
            vec![(0, 1, 0, 1, 0, 1), (1, 2, 2, 3, 1, 2), (2, 2, 3, 3, 2, 2),]
        );

        assert_eq!(
            m3.merge_regions(),
            vec![
                MergeRegion::Unchanged { start: 0, end: 1 },
                MergeRegion::A { start: 1, end: 2 },
                MergeRegion::Unchanged { start: 1, end: 2 },
            ]
        );
    }

    #[test]
    fn test_append_a() {
        let m3 = Merge3::new(
            &["aaa\n", "bbb\n"],
            &["aaa\n", "bbb\n", "222\n"],
            &["aaa\n", "bbb\n"],
        );

        assert_eq!(
            m3.merge_lines(false, &FixedMarkers::default()).join(""),
            "aaa\nbbb\n222\n"
        );
    }

    #[test]
    fn test_append_b() {
        let m3 = Merge3::new(
            &["aaa\n", "bbb\n"],
            &["aaa\n", "bbb\n"],
            &["aaa\n", "bbb\n", "222\n"],
        );

        assert_eq!(
            m3.merge_lines(false, &FixedMarkers::default()).join(""),
            "aaa\nbbb\n222\n"
        );
    }

    #[test]
    fn test_append_agreement() {
        let m3 = Merge3::new(
            &["aaa\n", "bbb\n"],
            &["aaa\n", "bbb\n", "222\n"],
            &["aaa\n", "bbb\n", "222\n"],
        );

        assert_eq!(
            m3.merge_lines(false, &FixedMarkers::default()).join(""),
            "aaa\nbbb\n222\n"
        );
    }

    #[test]
    fn test_append_clash() {
        let m3 = Merge3::new(
            &["aaa\n", "bbb\n"],
            &["aaa\n", "bbb\n", "222\n"],
            &["aaa\n", "bbb\n", "333\n"],
        );

        let ml = m3.merge_lines(
            false,
            &CustomMarkers {
                start_marker: Some("<< a\n"),
                mid_marker: Some("--\n"),
                end_marker: Some(">> b\n"),
                ..Default::default()
            },
        );
        assert_eq!(
            ml.join(""),
            r###"aaa
bbb
<< a
222
--
333
>> b
"###
        );
    }

    #[test]
    fn test_insert_agreement() {
        let m3 = Merge3::new(
            &["aaa\n", "bbb\n"],
            &["aaa\n", "222\n", "bbb\n"],
            &["aaa\n", "222\n", "bbb\n"],
        );

        let ml = m3.merge_lines(
            false,
            &CustomMarkers {
                start_marker: Some("<< a\n"),
                mid_marker: Some("--\n"),
                end_marker: Some(">> b\n"),
                ..Default::default()
            },
        );
        assert_eq!(ml.join(""), "aaa\n222\nbbb\n");
    }

    /// Both try to insert lines in the same place.
    #[test]
    fn test_insert_clash() {
        let m3 = Merge3::new(
            &["aaa\n", "bbb\n"],
            &["aaa\n", "111\n", "bbb\n"],
            &["aaa\n", "222\n", "bbb\n"],
        );

        assert_eq!(m3.find_unconflicted(), vec![(0, 1), (1, 2)]);

        assert_eq!(
            m3.find_sync_regions(),
            vec![(0, 1, 0, 1, 0, 1), (1, 2, 2, 3, 2, 3), (2, 2, 3, 3, 3, 3),]
        );

        assert_eq!(
            m3.merge_regions(),
            vec![
                MergeRegion::Unchanged { start: 0, end: 1 },
                MergeRegion::Conflict {
                    zstart: Some(1),
                    zend: Some(1),
                    astart: 1,
                    aend: 2,
                    bstart: 1,
                    bend: 2
                },
                MergeRegion::Unchanged { start: 1, end: 2 }
            ]
        );

        assert_eq!(
            m3.merge_groups(),
            vec![
                MergeGroup::Unchanged(&["aaa\n"]),
                MergeGroup::Conflict(Some(&[]), &["111\n"], &["222\n"]),
                MergeGroup::Unchanged(&["bbb\n"]),
            ]
        );

        let ml = m3.merge_lines(
            false,
            &CustomMarkers {
                start_marker: Some("<< a\n"),
                mid_marker: Some("--\n"),
                end_marker: Some(">> b\n"),
                ..Default::default()
            },
        );
        assert_eq!(
            ml.join(""),
            r###"aaa
<< a
111
--
222
>> b
bbb
"###
        );
    }

    /// Both try to insert lines in the same place.
    #[test]
    fn test_replace_clash() {
        let m3 = Merge3::new(
            &["aaa", "000", "bbb"],
            &["aaa", "111", "bbb"],
            &["aaa", "222", "bbb"],
        );

        assert_eq!(m3.find_unconflicted(), vec![(0, 1), (2, 3)]);

        assert_eq!(
            m3.find_sync_regions(),
            vec![(0, 1, 0, 1, 0, 1), (2, 3, 2, 3, 2, 3), (3, 3, 3, 3, 3, 3),]
        );
    }

    /// Replacement with regions of different size.
    #[test]
    fn test_replace_multi() {
        let m3 = Merge3::new(
            &["aaa", "000", "000", "bbb"],
            &["aaa", "111", "111", "111", "bbb"],
            &["aaa", "222", "222", "222", "222", "bbb"],
        );

        assert_eq!(m3.find_unconflicted(), vec![(0, 1), (3, 4)]);

        assert_eq!(
            m3.find_sync_regions(),
            vec![(0, 1, 0, 1, 0, 1), (3, 4, 4, 5, 5, 6), (4, 4, 5, 5, 6, 6),]
        );
    }

    /// Test case from diff3 manual.
    #[test]
    fn test_merge_poem() {
        let base = splitlines(TZU);
        let a = splitlines(LAO);
        let b = splitlines(TAO);
        let m3 = Merge3::new(base.as_slice(), a.as_slice(), b.as_slice());

        let ml = m3.merge_lines(false, &FixedMarkers::new(Some("LAO"), Some("TAO"), None));
        assert_eq!(ml.join(""), MERGED_RESULT);
    }

    /// Test case from diff3 manual.
    #[test]
    fn test_merge_poem_bytes() {
        let base = splitlines(TZU)
            .into_iter()
            .map(|s| s.as_bytes())
            .collect::<Vec<&[u8]>>();
        let a = splitlines(LAO)
            .into_iter()
            .map(|s| s.as_bytes())
            .collect::<Vec<&[u8]>>();
        let b = splitlines(TAO)
            .into_iter()
            .map(|s| s.as_bytes())
            .collect::<Vec<&[u8]>>();
        let m3 = Merge3::new(base.as_slice(), a.as_slice(), b.as_slice());

        let ml = m3.merge_lines(false, &FixedMarkers::new(Some("LAO"), Some("TAO"), None));

        let result = splitlines(MERGED_RESULT).into_iter().map(|s| s.as_bytes());

        let ml_s: Vec<String> = ml
            .iter()
            .map(|s| String::from_utf8_lossy(s).to_string())
            .collect();
        let result_s: Vec<String> = result
            .map(|s| String::from_utf8_lossy(s).to_string())
            .collect();

        assert_eq!(ml_s, result_s);
    }

    /// Reprocessing.
    #[test]
    fn test_minimal_conflicts_common() {
        let base_text = "a\n".repeat(20);
        let base_lines = splitlines(&base_text);
        let this_text = format!("{}{}", "a\n".repeat(10), "b\n".repeat(10));
        let this_lines = splitlines(&this_text);
        let other_text = format!("{}c\n{}c\n", "a\n".repeat(10), "b\n".repeat(8));
        let other_lines = splitlines(&other_text);
        let m3 = Merge3::new(
            base_lines.as_slice(),
            other_lines.as_slice(),
            this_lines.as_slice(),
        );

        let m_lines = m3.merge_lines(true, &FixedMarkers::new(Some("OTHER"), Some("THIS"), None));
        let merged_text = m_lines.join("");
        let optimal_text = [
            "a\n".repeat(10),
            "<<<<<<< OTHER\nc\n".to_string(),
            "=======\n".to_string(),
            ">>>>>>> THIS\n".to_string(),
            "b\n".repeat(8),
            "<<<<<<< OTHER\nc\n".to_string(),
            "=======\n".to_string(),
            "b\n".repeat(2),
            ">>>>>>> THIS\n".to_string(),
        ]
        .concat();
        assert_eq!(optimal_text, merged_text);
    }

    #[test]
    fn test_cherrypick() {
        let base_text = splitlines("ba\nb\n");
        let this_text = splitlines("ba\n");
        let other_text = splitlines("a\nb\nc\n");

        let m3 = Merge3::new(
            base_text.as_slice(),
            other_text.as_slice(),
            this_text.as_slice(),
        );

        assert_eq!(m3.find_unconflicted(), vec![]);

        assert_eq!(m3.find_sync_regions(), vec![(2, 2, 3, 3, 1, 1)]);
    }

    /// Reprocessing.
    #[cfg(feature = "patiencediff")]
    #[test]
    fn test_minimal_conflicts_common_with_patiencediff() {
        let base_text = "a\n".repeat(20);
        let base_lines = splitlines(&base_text);
        let this_text = ["a\n".repeat(10), "b\n".repeat(10)].concat();
        let this_lines = splitlines(&this_text);
        let other_text = [
            "a\n".repeat(10),
            "c\n".to_string(),
            "b\n".repeat(8),
            "c\n".to_string(),
        ]
        .concat();
        let other_lines = splitlines(&other_text);
        let m3 = Merge3::with_patience_diff(&base_lines, &other_lines, &this_lines);
        let m_lines = m3.merge_lines(true, &FixedMarkers::new(Some("OTHER"), Some("THIS"), None));
        let merged_text = m_lines.join("");
        let optimal_text = [
            "a\n".repeat(10),
            "<<<<<<< OTHER\nc\n".to_string(),
            "b\n".repeat(8),
            "c\n=======\n".to_string(),
            "b\n".repeat(10),
            ">>>>>>> THIS\n".to_string(),
        ]
        .concat();
        assert_eq!(optimal_text, merged_text)
    }

    #[test]
    fn test_minimal_conflicts_unique() {
        /// Add a newline to each entry in the string.
        fn add_newline(s: &str) -> String {
            let mut r = String::new();
            for c in s.chars() {
                r.push(c);
                r.push('\n');
            }
            r
        }

        let base_text = add_newline("abcdefghijklm");
        let base_lines = splitlines(&base_text);
        let this_text = add_newline("abcdefghijklmNOPQRSTUVWXYZ");
        let this_lines = splitlines(&this_text);
        let other_text = add_newline("abcdefghijklm1OPQRSTUVWXY2");
        let other_lines = splitlines(&other_text);
        let m3 = Merge3::new(&base_lines, &other_lines, &this_lines);
        let m_lines = m3.merge_lines(true, &FixedMarkers::new(Some("OTHER"), Some("THIS"), None));
        let merged_text = m_lines.join("");
        let optimal_text = [
            add_newline("abcdefghijklm"),
            "<<<<<<< OTHER\n1\n=======\nN\n>>>>>>> THIS\n".to_string(),
            add_newline("OPQRSTUVWXY"),
            "<<<<<<< OTHER\n2\n=======\nZ\n>>>>>>> THIS\n".to_string(),
        ]
        .concat();
        assert_eq!(optimal_text, merged_text);
    }

    #[test]
    fn test_minimal_conflicts_nonunique() {
        fn add_newline(s: &str) -> String {
            let mut r = String::new();
            for c in s.chars() {
                r.push(c);
                r.push('\n');
            }
            r
        }

        let base_text = add_newline("abacddefgghij");
        let base_lines = splitlines(&base_text);
        let this_text = add_newline("abacddefgghijkalmontfprz");
        let this_lines = splitlines(&this_text);
        let other_text = add_newline("abacddefgghijknlmontfprd");
        let other_lines = splitlines(&other_text);
        let m3 = Merge3::new(&base_lines, &other_lines, &this_lines);
        let m_lines = m3.merge_lines(true, &FixedMarkers::new(Some("OTHER"), Some("THIS"), None));
        let merged_text = m_lines.join("");
        let optimal_text = [
            add_newline("abacddefgghijk"),
            "<<<<<<< OTHER\nn\n=======\na\n>>>>>>> THIS\n".to_string(),
            add_newline("lmontfpr"),
            "<<<<<<< OTHER\nd\n=======\nz\n>>>>>>> THIS\n".to_string(),
        ]
        .concat();
        assert_eq!(optimal_text, merged_text);
    }

    /// Reprocessing and showing base breaks correctly.
    #[test]
    #[should_panic(expected = "base marker in reprocessed merge")]
    fn test_reprocess_and_base() {
        let base_text = "a\n".repeat(20);
        let base_lines = base_text.split_inclusive('\n').collect::<Vec<&str>>();
        let this_text = ["a\n".repeat(10), "b\n".repeat(10)].concat();
        let this_lines = this_text.split_inclusive('\n').collect::<Vec<&str>>();
        let other_text = [
            "a\n".repeat(10),
            "c\n".to_string(),
            "b\n".repeat(8),
            "c\n".to_string(),
        ]
        .concat();
        let other_lines = other_text.split_inclusive('\n').collect::<Vec<&str>>();
        let m3 = Merge3::new(
            base_lines.as_slice(),
            other_lines.as_slice(),
            this_lines.as_slice(),
        );
        m3.merge_lines(
            true,
            &CustomMarkers {
                start_marker: Some("<<<<< OTHER\n"),
                mid_marker: Some("=======\n"),
                end_marker: Some(">>>>>> THIS\n"),
                base_marker: Some("|||||||\n"),
            },
        );
    }

    #[test]
    fn test_dos_text() {
        let base_text = splitlines("a\r\n");
        let this_text = splitlines("b\r\n");
        let other_text = splitlines("c\r\n");
        let m3 = Merge3::new(
            base_text.as_slice(),
            other_text.as_slice(),
            this_text.as_slice(),
        );

        let m_lines = m3.merge_lines(false, &FixedMarkers::new(Some("OTHER"), Some("THIS"), None));
        assert_eq!(
            "<<<<<<< OTHER\r\nc\r\n=======\r\nb\r\n>>>>>>> THIS\r\n",
            m_lines.join("")
        );
    }

    #[test]
    fn test_mac_text() {
        let base_text = splitlines("a\r");
        let this_text = splitlines("b\r");
        let other_text = splitlines("c\r");
        let m3 = Merge3::new(
            base_text.as_slice(),
            other_text.as_slice(),
            this_text.as_slice(),
        );

        let m_lines = m3.merge_lines(false, &FixedMarkers::new(Some("OTHER"), Some("THIS"), None));
        assert_eq!(
            "<<<<<<< OTHER\rc\r=======\rb\r>>>>>>> THIS\r",
            m_lines.join("")
        );
    }

    #[test]
    fn test_merge3_cherrypick() {
        let base_text = splitlines("a\nb\n");
        let this_text = splitlines("a\n");
        let other_text = splitlines("a\nb\nc\n");
        // When cherrypicking, lines in base are not part of the conflict
        let mut m3 = Merge3::new(
            base_text.as_slice(),
            this_text.as_slice(),
            other_text.as_slice(),
        );
        m3.set_cherrypick(true);
        let m_lines = m3.merge_lines(false, &FixedMarkers::default());
        assert_eq!("a\n<<<<<<<\n=======\nc\n>>>>>>>\n", m_lines.join(""));

        // This is not symmetric
        let mut m3 = Merge3::new(
            base_text.as_slice(),
            other_text.as_slice(),
            this_text.as_slice(),
        );
        m3.set_cherrypick(true);

        let m_lines = m3.merge_lines(false, &FixedMarkers::default());
        assert_eq!("a\n<<<<<<<\nb\nc\n=======\n>>>>>>>\n", m_lines.join(""));
    }

    #[test]
    fn test_merge3_cherrypick_w_mixed() {
        let base_text = splitlines("a\nb\nc\nd\ne\n");
        let this_text = splitlines("a\nb\nq\n");
        let other_text = splitlines("a\nb\nc\nd\nf\ne\ng\n");
        // When cherrypicking, lines in base are not part of the conflict
        let mut m3 = Merge3::new(
            base_text.as_slice(),
            this_text.as_slice(),
            other_text.as_slice(),
        );
        m3.set_cherrypick(true);
        let m_lines = m3.merge_lines(false, &FixedMarkers::default());
        assert_eq!(
            [
                "a\n",
                "b\n",
                "<<<<<<<\n",
                "q\n",
                "=======\n",
                "f\n",
                ">>>>>>>\n",
                "<<<<<<<\n",
                "=======\n",
                "g\n",
                ">>>>>>>\n"
            ]
            .concat(),
            m_lines.join("")
        );
    }

    /// Objects other than strs may be used with Merge3.
    ///
    /// merge_groups and merge_regions work with non-str input.  Methods that
    /// return lines like merge_lines fail.
    #[test]
    fn test_allow_objects() {
        let base = b"abcde".iter().map(|x| (*x, *x)).collect::<Vec<(u8, u8)>>();
        let baser = base.iter().collect::<Vec<&(u8, u8)>>();
        let a = b"abcdef"
            .iter()
            .map(|x| (*x, *x))
            .collect::<Vec<(u8, u8)>>();
        let ar = a.iter().collect::<Vec<&(u8, u8)>>();
        let b = b"Zabcde"
            .iter()
            .map(|x| (*x, *x))
            .collect::<Vec<(u8, u8)>>();
        let br = b.iter().collect::<Vec<&(u8, u8)>>();
        let m3 = Merge3::new(baser.as_slice(), ar.as_slice(), br.as_slice());
        assert_eq!(
            vec![
                MergeRegion::B { start: 0, end: 1 },
                MergeRegion::Unchanged { start: 0, end: 5 },
                MergeRegion::A { start: 5, end: 6 }
            ],
            m3.merge_regions()
        );
        assert_eq!(
            vec![
                MergeGroup::B(&[&(b"Z"[0], b"Z"[0])]),
                MergeGroup::Unchanged(&[
                    &(b"a"[0], b"a"[0]),
                    &(b"b"[0], b"b"[0]),
                    &(b"c"[0], b"c"[0]),
                    &(b"d"[0], b"d"[0]),
                    &(b"e"[0], b"e"[0])
                ]),
                MergeGroup::A(&[&(b"f"[0], b"f"[0])]),
            ],
            m3.merge_groups()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intersect() {
        assert_eq!(intersect((0, 10), (0, 6)), Some((0, 6)));
        assert_eq!(intersect((0, 10), (5, 15)), Some((5, 10)));
        assert_eq!(intersect((0, 10), (10, 15)), None);
        assert_eq!(intersect((0, 9), (10, 15)), None);
        assert_eq!(intersect((0, 9), (7, 15)), Some((7, 9)));
    }

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
