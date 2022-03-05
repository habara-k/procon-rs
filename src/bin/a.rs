#![allow(unused_imports)]
use fixedbitset::FixedBitSet;
use itertools::Itertools;
use num::complex::Complex;
use num::integer::gcd;
use ordered_float::OrderedFloat;
use proconio::{
    fastout, input,
    marker::{Chars, Usize1},
};
use std::cmp::{max, min};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};
use std::f64::consts::PI;
use std::mem::swap;
use superslice::Ext;
use text_io::read;

use my_library_rs::*;

struct RangeSum;
impl Monoid for RangeSum {
    type S = (i64, usize);
    fn identity() -> Self::S {
        (0, 0)
    }
    fn binary_operation(&(a, n): &Self::S, &(b, m): &Self::S) -> Self::S {
        (a + b, n + m)
    }
}
struct RangeAddRangeSum;
impl MapMonoid for RangeAddRangeSum {
    type M = RangeSum;
    type F = i64;
    fn identity_map() -> Self::F {
        0
    }
    fn mapping(&a: &Self::F, &(x, n): &<Self::M as Monoid>::S) -> <Self::M as Monoid>::S {
        (a * n as i64 + x, n)
    }
    fn composition(&a: &Self::F, &b: &Self::F) -> Self::F {
        a + b
    }
}

#[fastout]
fn main() {
    input! {
        n: usize, q: usize,
        x: [i64; n],
    }

    let mut seg: RedBlackTree<RangeAddRangeSum> =
        x.iter().map(|&v| (v, 1usize)).collect_vec().into();

    let mut ans = vec![];
    for _ in 0..q {
        input! { t: usize }
        match t {
            1 => {
                input! { a: Usize1, b: Usize1, v: i64 }
                seg.apply_range(a, b + 1, v);
            }
            2 => {
                input! { a: Usize1, b: Usize1, c: Usize1, d: Usize1 }
                let x = seg.clone();
                let (_, mut x, _) = x.split3(c, d + 1);
                // x = [c,d+1)

                let y = seg.clone();
                let (mut y, _, mut z) = y.split3(a, b + 1);
                // y = [0,a)
                // z = [b+1,n)

                y.merge(&mut x);
                y.merge(&mut z);
                swap(&mut y, &mut seg);
                // seg = [0,a) + [c,d+1) + [b+1,n)
            }
            3 => {
                input! { a: Usize1, b: Usize1 }
                ans.push(seg.prod(a, b + 1).0);
            }
            _ => panic!(),
        }
    }

    for e in ans {
        println!("{}", e);
    }
}
