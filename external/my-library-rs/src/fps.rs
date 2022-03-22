//use std::arch::x86_64::*;
use std::cmp::min;
use std::marker::PhantomData;
use std::ops::{Add, Deref, DerefMut, Div, DivAssign, Mul, MulAssign, Neg, Sub};

use crate::convolution::{butterfly, butterfly_doubling, butterfly_inv};
use crate::modulo::{Mod998244353, Modulus};

pub struct Fps<M: Modulus, T>(Vec<T>, PhantomData<M>);
pub type Fps998244353<T> = Fps<Mod998244353, T>;

impl<M: Modulus, T> From<Vec<T>> for Fps<M, T> {
    fn from(v: Vec<T>) -> Self {
        Self(v, PhantomData::<M>)
    }
}

impl<M: Modulus, T> Deref for Fps<M, T> {
    type Target = Vec<T>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<M: Modulus, T> DerefMut for Fps<M, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
impl<M: Modulus, T: Clone> Clone for Fps<M, T> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData::<M>)
    }
}

impl<M: Modulus, T: Clone + Copy + MulAssign> MulAssign<T> for Fps<M, T> {
    fn mul_assign(&mut self, rhs: T) {
        self.iter_mut().for_each(|e| *e *= rhs);
    }
}
impl<M: Modulus, T: Clone + Copy + MulAssign + From<i32> + Div<Output = T>> DivAssign<T>
    for Fps<M, T>
{
    fn div_assign(&mut self, mut rhs: T) {
        rhs = T::from(1) / rhs;
        self.iter_mut().for_each(|e| *e *= rhs);
    }
}

fn ceil_log2(n: usize) -> usize {
    debug_assert!(n > 0);
    32 - (n as u32 - 1).leading_zeros() as usize
}

impl<M: Modulus, T> Fps<M, T>
where
    T: Clone
        + Copy
        + From<u32>
        + Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + Div<Output = T>
        + MulAssign<T>
        + MulAssign<u32>
        + Neg<Output = T>,
{
    //pub fn convolution(a: &[T], b: &[T]) -> Self {
    //    if a.is_empty() || b.is_empty() {
    //        return vec![].into();
    //    }
    //    let (n, m) = (a.len(), b.len());

    //    let (mut a, mut b): (Self, Self) = (a.to_owned().into(), b.to_owned().into());
    //    let z = 1 << ceil_log2(n + m - 1);
    //    a.resize(z, T::from(0));
    //    Self::butterfly(&mut a);
    //    b.resize(z, T::from(0));
    //    Self::butterfly(&mut b);
    //    for (a, &b) in a.iter_mut().zip(&b) {
    //        *a *= b;
    //    }
    //    Self::butterfly_inv(&mut a);
    //    a.resize(n + m - 1, T::from(0));
    //    a /= z;
    //    a
    //}

    pub fn inv(&self, d: usize) -> Self {
        debug_assert!(d > 0);
        debug_assert!(self.len() > 0);
        let mut inv = vec![T::from(1) / self[0]];
        for m in (0..).map(|i| 1 << i).take_while(|&m| m < d) {
            let mut f = self[0..min(2 * m, self.len())].to_owned();
            let mut g = inv.clone();
            f.resize(2 * m, T::from(0));
            g.resize(2 * m, T::from(0));
            butterfly::<M, T>(&mut f);
            butterfly::<M, T>(&mut g);
            for (a, &b) in f.iter_mut().zip(&g) {
                *a *= b;
            }
            butterfly_inv::<M, T>(&mut f);

            f.drain(0..m);
            f.resize(2 * m, T::from(0));

            butterfly::<M, T>(&mut f);
            for (a, &b) in f.iter_mut().zip(&g) {
                *a *= b;
            }
            butterfly_inv::<M, T>(&mut f);

            let iz = T::from(1) / T::from(2 * m as u32);
            let iz = -iz * iz;

            for &a in &f[0..min(d - inv.len(), m)] {
                inv.push(a * iz);
            }
        }
        debug_assert_eq!(inv.len(), d);
        inv.into()
    }

    pub fn bostan_mori(p: &[T], q: &[T], mut k: u64) -> T {
        let (mut p, mut q): (Self, Self) = (p.to_owned().into(), q.to_owned().into());

        let n = 1 << ceil_log2(p.len() + q.len() - 1);
        p.resize(n, T::from(0));
        q.resize(n, T::from(0));
        butterfly::<M, T>(&mut p);
        butterfly::<M, T>(&mut q);

        while k >= n as u64 {
            butterfly_doubling::<M, T>(&mut p);
            butterfly_doubling::<M, T>(&mut q);

            let mut inv2 = T::from(M::INV2);
            if (k & 1) == 0 {
                for s in 0..n {
                    p[s] = (p[2 * s] * q[2 * s + 1] + p[2 * s + 1] * q[2 * s]) * inv2;
                }
            } else {
                for s in 0..n {
                    p[s] = (p[2 * s] * q[2 * s + 1] - p[2 * s + 1] * q[2 * s]) * inv2;
                    inv2 *= M::INV_ROT[(!s).trailing_zeros() as usize];
                }
            }
            p.truncate(n);
            for i in 0..n {
                q[i] = q[2 * i] * q[2 * i + 1];
            }
            q.truncate(n);

            k >>= 1;
        }

        butterfly_doubling::<M, T>(&mut p);

        butterfly_inv::<M, T>(&mut q);
        q = Self::inv(&q, n);
        q.resize(2 * n, T::from(0));
        butterfly::<M, T>(&mut q);

        for (e, &x) in q.iter_mut().zip(p.iter()) {
            *e *= x;
            *e *= M::INV2;
        }
        butterfly_inv::<M, T>(&mut q);

        q[k as usize]
    }
}
