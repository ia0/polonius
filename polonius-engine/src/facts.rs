use std::collections::{BTreeMap, BTreeSet};
use std::hash::Hash;

/// The "facts" which are the basis of the NLL borrow analysis.
#[derive(Clone)]
pub struct AllFacts<R: Atom, L: Atom, P: Atom> {
    /// `borrow_region(R, B, P)` -- the region R may refer to data
    /// from borrow B starting at the point P (this is usually the
    /// point *after* a borrow rvalue)
    pub borrow_region: Vec<(R, L, P)>,

    /// `universal_region(R)` -- this is a "free region" within fn body
    pub universal_region: Vec<R>,

    /// `cfg_edge(P,Q)` for each edge P -> Q in the control flow
    pub cfg_edge: Vec<(P, P)>,

    /// `killed(B,P)` when some prefix of the path borrowed at B is assigned at point P
    pub killed: Vec<(L, P)>,

    /// `outlives(R1, R2, P)` when we require `R1@P: R2@P`
    pub outlives: Vec<(R, R, P)>,

    /// `region_live_at(R, P)` when the region R appears in a live variable at P
    pub region_live_at: Vec<(R, P)>,

    ///  `invalidates(P, L)` when the loan L is invalidated at point P
    pub invalidates: Vec<(P, L)>,
}

impl<R: Atom, L: Atom, P: Atom> Default for AllFacts<R, L, P> {
    fn default() -> Self {
        AllFacts {
            borrow_region: Vec::default(),
            universal_region: Vec::default(),
            cfg_edge: Vec::default(),
            killed: Vec::default(),
            outlives: Vec::default(),
            region_live_at: Vec::default(),
            invalidates: Vec::default(),
        }
    }
}

fn extract_singleton<Point: Atom>(m: &BTreeSet<Point>) -> Option<Point> {
    if m.len() != 1 {
        return None;
    }
    for &p in m {
        return Some(p);
    }
    unreachable!();
}

impl<Region: Atom, Loan: Atom, Point: Atom> AllFacts<Region, Loan, Point> {
    pub fn condense_cfg(&mut self) {
        let mut pred = BTreeMap::new();
        let mut succ = BTreeMap::new();
        let mut all_points = BTreeSet::new();
        for &(p, q) in self.cfg_edge.iter() {
            assert!(succ.entry(p).or_insert_with(|| BTreeSet::new()).insert(q));
            assert!(pred.entry(q).or_insert_with(|| BTreeSet::new()).insert(p));
            all_points.insert(p);
            all_points.insert(q);
        }
        let mut region_live_at = BTreeMap::new();
        for &(r, p) in self.region_live_at.iter() {
            assert!(
                region_live_at
                    .entry(p)
                    .or_insert_with(|| BTreeSet::new())
                    .insert(r)
            );
        }
        let mut outlives_at = BTreeSet::new();
        for &(_, _, p) in self.outlives.iter() {
            // We may have several outlives relations at a given point.
            outlives_at.insert(p);
        }

        let mut merge_into = BTreeMap::new();
        for (p, qs) in succ.iter() {
            let q = match extract_singleton(qs) {
                Some(q) => q,
                None => continue,
            };
            if let Some(should_be_p) = pred.get(&q).and_then(extract_singleton) {
                assert!(should_be_p == *p);
            } else {
                continue;
            }
            if region_live_at.get(p) != region_live_at.get(&q) {
                continue;
            }
            if outlives_at.contains(p) || outlives_at.contains(&q) {
                continue;
            }
            assert!(merge_into.insert(q, *p) == None);
        }
        println!(
            "There are {}/{} nodes to be merged.",
            merge_into.len(),
            all_points.len()
        );
        let first_merge_into = |q: Point| -> Option<Point> {
            match merge_into.get(&q) {
                None => None,
                Some(q) => {
                    let mut r = *q;
                    while let Some(p) = merge_into.get(&r) {
                        r = *p;
                    }
                    Some(r)
                }
            }
        };
        let last_merge_into = |mut p: Point| -> Point {
            loop {
                let qs = match succ.get(&p) {
                    None => return p,
                    Some(qs) => qs,
                };
                p = match extract_singleton(qs) {
                    None => return p,
                    Some(p) if merge_into.get(&p).is_some() => p,
                    Some(_) => return p,
                };
            }
        };

        let mut borrow_region: BTreeMap<(Region, Loan), BTreeSet<Point>> = BTreeMap::new();
        for &(r, l, q) in self.borrow_region.iter() {
            let s = borrow_region
                .entry((r, l))
                .or_insert_with(|| BTreeSet::new());
            match first_merge_into(q) {
                None => {
                    assert!(s.insert(q));
                }
                Some(p) => {
                    s.insert(p);
                }
            };
        }
        self.borrow_region.clear();
        for ((r, l), ps) in borrow_region {
            for p in ps {
                self.borrow_region.push((r, l, p));
            }
        }
        let mut cfg_edge = Vec::new();
        for &(p, q) in self.cfg_edge.iter() {
            if first_merge_into(p).is_some() {
                continue;
            }
            cfg_edge.push((p, last_merge_into(q)));
        }
        self.cfg_edge = cfg_edge;
        let mut killed: BTreeMap<Loan, BTreeSet<Point>> = BTreeMap::new();
        for &(l, q) in self.killed.iter() {
            let s = killed.entry(l).or_insert_with(|| BTreeSet::new());
            match first_merge_into(q) {
                None => {
                    assert!(s.insert(q));
                }
                Some(p) => {
                    s.insert(p);
                }
            };
        }
        self.killed.clear();
        for (l, ps) in killed {
            for p in ps {
                self.killed.push((l, p));
            }
        }
        let mut region_live_at = Vec::new();
        for &(r, p) in self.region_live_at.iter() {
            if merge_into.get(&p).is_some() {
                continue;
            }
            region_live_at.push((r, p));
        }
        self.region_live_at = region_live_at;
        let mut invalidates: BTreeMap<Loan, BTreeSet<Point>> = BTreeMap::new();
        for &(q, l) in self.invalidates.iter() {
            let s = invalidates.entry(l).or_insert_with(|| BTreeSet::new());
            match first_merge_into(q) {
                None => {
                    assert!(s.insert(q));
                }
                Some(p) => {
                    s.insert(p);
                }
            };
        }
        self.invalidates.clear();
        for (l, ps) in invalidates {
            for p in ps {
                self.invalidates.push((p, l));
            }
        }
    }
}

pub trait Atom: From<usize> + Into<usize> + Copy + Clone + Eq + Ord + Hash + 'static {
    fn index(self) -> usize;
}
