use itertools::Itertools;
use num::complex::Complex;
use num::{Num, Zero};

pub fn cross<T>(a: Complex<T>, b: Complex<T>) -> T
where
    T: Num,
{
    a.re * b.im - a.im * b.re
}

pub fn convex_hull<T>(ps: &mut Vec<Complex<T>>) -> Vec<Complex<T>>
where
    T: Copy + Num + Ord,
{
    ps.sort_by_key(|p| (p.re, p.im));

    let mut ch = vec![];
    for &p in ps.iter() {
        while ch.len() >= 2
            && cross(p - ch[ch.len() - 1], ch[ch.len() - 1] - ch[ch.len() - 2]) >= Zero::zero()
        {
            ch.pop();
        }
        ch.push(p);
    }
    let n = ch.len();
    for &p in ps.iter().rev().skip(1) {
        while ch.len() > n
            && cross(p - ch[ch.len() - 1], ch[ch.len() - 1] - ch[ch.len() - 2]) >= Zero::zero()
        {
            ch.pop();
        }
        ch.push(p);
    }

    ch.pop();
    ch
}
pub fn area_x2<T>(ps: &Vec<Complex<T>>) -> T
where
    T: Copy + Num,
{
    ps.iter()
        .skip(1)
        .tuple_windows()
        .map(|(a, b)| cross(a - ps[0], b - ps[0]))
        .fold(Zero::zero(), |sum, x| sum + x)
}
