#![allow(unused_imports)]
use itertools::Itertools;
use num::complex::Complex;
use num::integer::gcd;
use ordered_float::OrderedFloat;
use proconio::{
    fastout, input,
    marker::{Chars, Usize1},
};
use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};
use std::f64::consts::PI;
use std::mem::swap;
use superslice::Ext;

use ac_library_rs::*;
use my_library_rs::*;

//#[fastout]
fn main() {
    input! {
        h: usize, w: usize,
        c: [Chars; h],
    }

    let disjoint = (0..1<<w).filter(|&s| {
        (s & (s << 1)) == 0
    }).collect_vec();

    type Mint = ModInt1000000007;
    let mut dp = vec![Mint::new(1); 1 << w];

    for k in 0..h {

        let mut wall = 0;
        for i in 0..w {
            if c[k][i] == '#' {
                wall |= 1<<i;
            }
        }

        let mut nxt_dp = vec![Mint::new(0); 1<<w];

        for &s in disjoint.iter().filter(|&s| {
            *s & wall == 0
        }) {
            nxt_dp[s] = dp[(1<<w)-1 & !(s | s>>1 | s<<1)];
        }

        // zeta
        subset_zeta_transform(&mut nxt_dp);

        swap(&mut dp, &mut nxt_dp);
    }

    println!("{}", dp[(1<<w)-1].val());
}
