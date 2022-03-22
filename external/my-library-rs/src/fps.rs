//use std::arch::x86_64::*;
use std::cmp::min;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, DivAssign, MulAssign};

use crate::convolution::{butterfly, butterfly_doubling, butterfly_inv};
use crate::modulo::{Mod998244353, Modulus};

pub struct Fps<M: Modulus>(Vec<u32>, PhantomData<M>);
pub type Fps998244353 = Fps<Mod998244353>;

impl<M: Modulus> From<Vec<u32>> for Fps<M> {
    fn from(v: Vec<u32>) -> Self {
        Self(v, PhantomData::<M>)
    }
}

impl<M: Modulus> Deref for Fps<M> {
    type Target = Vec<u32>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<M: Modulus> DerefMut for Fps<M> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
impl<M: Modulus> Clone for Fps<M> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData::<M>)
    }
}

impl<M: Modulus> MulAssign<u32> for Fps<M> {
    fn mul_assign(&mut self, rhs: u32) {
        self.iter_mut().for_each(|e| *e = M::mul(*e, rhs));
    }
}
impl<M: Modulus> DivAssign<u32> for Fps<M> {
    fn div_assign(&mut self, mut rhs: u32) {
        rhs = M::inv(rhs);
        self.iter_mut().for_each(|e| *e = M::mul(*e, rhs));
    }
}

fn ceil_log2(n: usize) -> usize {
    debug_assert!(n > 0);
    32 - (n as u32 - 1).leading_zeros() as usize
}

impl<M: Modulus> Fps<M> {
    pub fn inv(&self, d: usize) -> Self {
        debug_assert!(d > 0);
        debug_assert!(self.len() > 0);
        let mut inv = vec![M::inv(self[0])];
        for m in (0..).map(|i| 1 << i).take_while(|&m| m < d) {
            let mut f = self[0..min(2 * m, self.len())].to_owned();
            let mut g = inv.clone();
            f.resize(2 * m, 0);
            g.resize(2 * m, 0);
            butterfly::<M>(&mut f);
            butterfly::<M>(&mut g);
            for (a, &b) in f.iter_mut().zip(&g) {
                *a = M::mul(*a, b);
            }
            butterfly_inv::<M>(&mut f);

            f.drain(0..m);
            f.resize(2 * m, 0);

            butterfly::<M>(&mut f);
            for (a, &b) in f.iter_mut().zip(&g) {
                *a = M::mul(*a, b);
            }
            butterfly_inv::<M>(&mut f);

            let iz = M::inv(2 * m as u32);
            let iz = M::neg(M::mul(iz, iz));

            for &a in &f[0..min(d - inv.len(), m)] {
                inv.push(M::mul(a, iz));
            }
        }
        debug_assert_eq!(inv.len(), d);
        inv.into()
    }

    pub fn bostan_mori(p: &[u32], q: &[u32], mut k: u64) -> u32 {
        let (mut p, mut q): (Self, Self) = (p.to_owned().into(), q.to_owned().into());

        let n = 1 << ceil_log2(p.len() + q.len() - 1);
        p.resize(n, 0);
        q.resize(n, 0);
        butterfly::<M>(&mut p);
        butterfly::<M>(&mut q);

        while k >= n as u64 {
            butterfly_doubling::<M>(&mut p);
            butterfly_doubling::<M>(&mut q);

            if (k & 1) == 0 {
                for s in 0..n {
                    p[s] = M::div2(M::add(
                        M::mul(p[2 * s], q[2 * s + 1]),
                        M::mul(p[2 * s + 1], q[2 * s]),
                    ));
                }
            } else {
                let mut rot = M::inv(2);
                for s in 0..n {
                    p[s] = M::mul(
                        M::sub(
                            M::mul(p[2 * s], q[2 * s + 1]),
                            M::mul(p[2 * s + 1], q[2 * s]),
                        ),
                        rot,
                    );
                    rot = M::mul(rot, M::INV_ROT[(!s).trailing_zeros() as usize]);
                }
            }
            p.truncate(n);
            for i in 0..n {
                q[i] = M::mul(q[2 * i], q[2 * i + 1]);
            }
            q.truncate(n);

            k >>= 1;
        }

        butterfly_doubling::<M>(&mut p);

        butterfly_inv::<M>(&mut q);
        q = Self::inv(&q, n);
        q.resize(2 * n, 0);
        butterfly::<M>(&mut q);

        for (e, &x) in q.iter_mut().zip(p.iter()) {
            *e = M::div2(M::mul(*e, x));
        }
        butterfly_inv::<M>(&mut q);

        q[k as usize]
    }
}
