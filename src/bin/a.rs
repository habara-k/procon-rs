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
type Fps = Fps998244353;

#[fastout]
fn main() {
    input! {
        n: u64, k: usize,
    }

    let mut mp = BTreeMap::new();
    for i in 1..=k {
        *mp.entry(k / i).or_insert(0) += 1;
    }

    let mut fps: Fps = vec![1].into();
    const MOD: u32 = 998244353;
    for (sz, cnt) in mp {
        let cnt = cnt % MOD;
        fps *= if cnt == 0 { 0 } else { MOD - cnt };
        fps.insert(0, 1);

        fps = fps.inv(sz+2);
        fps.remove(0);
        fps /= cnt;
    }

    fps *= MOD - 1;
    fps.insert(0, 1);
    let ans = Fps::bostan_mori(&vec![1], &fps, n+1);
    println!("{}", ans);
}
