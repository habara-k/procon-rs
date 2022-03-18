use std::cmp::min;
use std::iter::successors;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, DivAssign, MulAssign};

pub trait Modulus {
    const VALUE: u32;
    const PRIMITIVE_ROOT: u32;
    fn mul(a: u32, b: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        debug_assert!(b < Self::VALUE);
        ((a as u64 * b as u64) % Self::VALUE as u64) as u32
    }
    fn add(mut a: u32, b: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        debug_assert!(b < Self::VALUE);
        a += b;
        if a >= Self::VALUE {
            a - Self::VALUE
        } else {
            a
        }
    }
    fn neg(a: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        if a == 0 {
            0
        } else {
            Self::VALUE - a
        }
    }
    fn sub(a: u32, b: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        debug_assert!(b < Self::VALUE);
        Self::add(a, Self::neg(b))
    }
    fn pow(mut a: u32, mut n: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        let mut r = 1;
        while n > 0 {
            if n & 1 == 1 {
                r = Self::mul(r, a);
            }
            a = Self::mul(a, a);
            n >>= 1;
        }
        r
    }
    fn inv(a: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        Self::pow(a, Self::VALUE - 2)
    }
}

pub struct Fps<M: Modulus>(Vec<u32>, PhantomData<M>);
pub struct Mod998244353 {}
impl Modulus for Mod998244353 {
    const VALUE: u32 = 998244353;
    const PRIMITIVE_ROOT: u32 = 3;
}
pub type Fps998244353 = Fps<Mod998244353>;

impl<M: Modulus> From<Vec<u32>> for Fps<M> {
    fn from(v: Vec<u32>) -> Self {
        Self(
            v.iter().map(|&e| e % M::VALUE).collect::<Vec<_>>(),
            PhantomData::<M>,
        )
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

fn ceil_log2(n: u32) -> u32 {
    debug_assert!(n > 0);
    32 - (n - 1).leading_zeros()
}

impl<M: Modulus> Fps<M> {
    pub fn butterfly(a: &mut [u32]) {
        let n = a.len();
        debug_assert!(n.is_power_of_two());
        let h = ceil_log2(n as u32) as usize;

        let root = M::pow(M::PRIMITIVE_ROOT, (M::VALUE - 1) >> h);
        let mut e = successors(Some(root), |&x| Some(M::neg(M::mul(x, x))))
            .take(h - 1)
            .collect::<Vec<_>>();
        e.reverse();

        for len in 0..h {
            let p = 1 << h - 1 - len;

            for j in 0..p {
                let x = a[j];
                let y = a[j + p];
                a[j] = M::add(x, y);
                a[j + p] = M::sub(x, y);
            }

            if len == 0 {
                continue;
            }

            let mut rot = e[0];
            for s in 1..1 << len {
                let offset = s << h - len;
                for j in offset..offset + p {
                    let x = a[j];
                    let y = M::mul(a[j + p], rot);
                    a[j] = M::add(x, y);
                    a[j + p] = M::sub(x, y);
                }
                if s + 1 != 1 << len {
                    rot = M::mul(rot, e[(!s).trailing_zeros() as usize]);
                }
            }
        }
    }
    pub fn butterfly_inv(a: &mut [u32]) {
        let n = a.len();
        debug_assert!(n.is_power_of_two());
        let h = ceil_log2(n as u32) as usize;

        let root = M::pow(M::PRIMITIVE_ROOT, (M::VALUE - 1) >> h);

        let mut ie = successors(Some(M::inv(root)), |&x| Some(M::neg(M::mul(x, x))))
            .take(h - 1)
            .collect::<Vec<_>>();
        ie.reverse();

        for len in (0..h).rev() {
            let p = 1 << h - 1 - len;

            for j in 0..p {
                let x = a[j];
                let y = a[j + p];
                a[j] = M::add(x, y);
                a[j + p] = M::sub(x, y);
            }

            if len == 0 {
                continue;
            }

            let mut rot = ie[0];
            for s in 1..1 << len {
                let offset = s << h - len;
                for j in offset..offset + p {
                    let x = a[j];
                    let y = a[j + p];
                    a[j] = M::add(x, y);
                    a[j + p] = M::mul(M::sub(x, y), rot);
                }
                if s + 1 != 1 << len {
                    rot = M::mul(rot, ie[(!s).trailing_zeros() as usize]);
                }
            }
        }
    }

    pub fn convolution(a: &[u32], b: &[u32]) -> Self {
        if a.is_empty() || b.is_empty() {
            return vec![].into();
        }
        let (n, m) = (a.len(), b.len());

        let (mut a, mut b) = (a.to_owned(), b.to_owned());
        let z = 1 << ceil_log2((n + m - 1) as _);
        a.resize(z, 0);
        Self::butterfly(&mut a);
        b.resize(z, 0);
        Self::butterfly(&mut b);
        for (a, &b) in a.iter_mut().zip(&b) {
            *a = M::mul(*a, b);
        }
        Self::butterfly_inv(&mut a);
        a.resize(n + m - 1, 0);
        let iz = M::inv(z as u32);
        for a in &mut a {
            *a = M::mul(*a, iz);
        }
        a.into()
    }

    pub fn inv(&self, d: usize) -> Self {
        debug_assert!(d > 0);
        debug_assert!(self.len() > 0);
        let mut inv = vec![M::inv(self[0])];
        for m in (0..).map(|i| 1 << i).take_while(|&m| m < d) {
            let mut f = self[0..min(2 * m, self.len())].to_owned();
            let mut g = inv.clone();
            f.resize(2 * m, 0);
            g.resize(2 * m, 0);
            Self::butterfly(&mut f);
            Self::butterfly(&mut g);
            for (a, &b) in f.iter_mut().zip(&g) {
                *a = M::mul(*a, b);
            }
            Self::butterfly_inv(&mut f);

            f.drain(0..m);
            f.resize(2 * m, 0);
            Self::butterfly(&mut f);
            for (a, &b) in f.iter_mut().zip(&g) {
                *a = M::mul(*a, b);
            }
            Self::butterfly_inv(&mut f);

            let iz = M::inv(2*m as u32);
            let iz = M::neg(M::mul(iz, iz));

            for &a in &f[0..min(d - inv.len(), m)] {
                inv.push(M::mul(a, iz));
            }
        }
        debug_assert_eq!(inv.len(), d);
        inv.into()
    }

    pub fn bostan_mori(p: &[u32], q: &[u32], mut n: u64) -> u32 {
        let (mut p, mut q) = (p.to_owned(), q.to_owned());
        while n > 0 {
            let r = (0..q.len())
                .map(|i| if i & 1 == 1 { M::neg(q[i]) } else { q[i] })
                .collect::<Vec<_>>();
            p = Self::convolution(&p, &r)
                .iter()
                .skip((n & 1) as usize)
                .step_by(2)
                .cloned()
                .collect::<Vec<_>>();
            q = Self::convolution(&q, &r)
                .iter()
                .step_by(2)
                .cloned()
                .collect::<Vec<_>>();
            n >>= 1;
        }
        M::mul(p[0], M::inv(q[0]))
    }
}
