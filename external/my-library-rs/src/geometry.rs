use num::complex::Complex;
use num::{Num, Zero};
use std::iter::Sum;

/// 外積を返す.
/// # Example
///
/// ```
/// use num::Complex;
/// use my_library_rs::*;
/// assert_eq!(cross(Complex::new(4, 1), Complex::new(3, 2)), 4*2 - 1*3);
/// ```
pub fn cross<T>(a: Complex<T>, b: Complex<T>) -> T
where
    T: Num,
{
    a.re * b.im - a.im * b.re
}

/// 反時計回りの凸包を返す.
/// NOTE: (x座標,y座標)のtupleが一番小さい点を始点とする.
/// # Example
///
/// ```
/// use num::Complex;
/// use my_library_rs::*;
/// let ps = vec![Complex::new(0, 0), Complex::new(10, 0), Complex::new(0, 10), Complex::new(1, 1)];
/// assert_eq!(convex_hull(&ps), vec![Complex::new(0, 0), Complex::new(10, 0), Complex::new(0, 10)]);
/// ```
pub fn convex_hull<T>(ps: &[Complex<T>]) -> Vec<Complex<T>>
where
    T: Copy + Num + Ord,
{
    if ps.len() <= 1 {
        return ps.to_vec();
    }

    let mut order: Vec<usize> = (0..ps.len()).collect();
    order.sort_by_key(|&i| (ps[i].re, ps[i].im));

    let mut ch = vec![];
    for &i in order.iter() {
        while ch.len() >= 2
            && cross(
                ps[i] - ch[ch.len() - 1],
                ch[ch.len() - 1] - ch[ch.len() - 2],
            ) >= Zero::zero()
        {
            ch.pop();
        }
        ch.push(ps[i]);
    }
    let n = ch.len();
    for &i in order.iter().rev().skip(1) {
        while ch.len() > n
            && cross(
                ps[i] - ch[ch.len() - 1],
                ch[ch.len() - 1] - ch[ch.len() - 2],
            ) >= Zero::zero()
        {
            ch.pop();
        }
        ch.push(ps[i]);
    }

    ch.pop();
    ch
}

/// 多角形の符号付き面積の2倍を返す.
/// # Example
/// ```
/// use num::Complex;
/// use my_library_rs::*;
/// let ps = vec![Complex::new(0, 0), Complex::new(1, 0), Complex::new(0, 1)];
/// assert_eq!(area_x2(&ps), 1);
///
/// let ps = vec![Complex::new(0, 0), Complex::new(0, 1), Complex::new(1, 0)];
/// assert_eq!(area_x2(&ps), -1);
/// ```
pub fn area_x2<T>(ps: &[Complex<T>]) -> T
where
    T: Copy + Num + Sum,
{
    let n = ps.len();
    (0..n).map(|i| cross(ps[i], ps[(i + 1) % n])).sum::<T>()
}
