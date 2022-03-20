use std::cmp::min;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, DivAssign, MulAssign, SubAssign};

pub trait Modulus {
    const VALUE: u32;
    const PRIMITIVE_ROOT: u32;
    const BASE: [u32; 30];
    const ROT: [u32; 30];
    const INV_ROT: [u32; 30];
    fn mul(a: u32, b: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        debug_assert!(b < Self::VALUE);
        ((a as u64 * b as u64) % Self::VALUE as u64) as u32
    }
    fn add_assign(a: &mut u32, b: u32) {
        debug_assert!(*a < Self::VALUE);
        debug_assert!(b < Self::VALUE);
        *a += b;
        if *a >= Self::VALUE {
            *a -= Self::VALUE;
        }
    }
    fn add(mut a: u32, b: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        debug_assert!(b < Self::VALUE);
        Self::add_assign(&mut a, b);
        a
    }
    fn neg(a: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        if a == 0 {
            0
        } else {
            Self::VALUE - a
        }
    }
    fn sub_assign(a: &mut u32, b: u32) {
        debug_assert!(*a < Self::VALUE);
        debug_assert!(b < Self::VALUE);
        *a += Self::VALUE - b;
        if *a >= Self::VALUE {
            *a -= Self::VALUE;
        }
    }
    fn sub(mut a: u32, b: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        debug_assert!(b < Self::VALUE);
        Self::sub_assign(&mut a, b);
        a
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
    fn div2(a: u32) -> u32 {
        debug_assert!(a < Self::VALUE);
        (a + if (a & 1) == 0 { 0 } else { Self::VALUE }) >> 1
    }
}

pub struct Fps<M: Modulus>(Vec<u32>, PhantomData<M>);
pub struct Mod998244353 {}
impl Modulus for Mod998244353 {
    const VALUE: u32 = 998244353;
    const PRIMITIVE_ROOT: u32 = 3;
    const BASE: [u32; 30] = [
        1, 998244352, 911660635, 372528824, 929031873, 452798380, 922799308, 781712469, 476477967,
        166035806, 258648936, 584193783, 63912897, 350007156, 666702199, 968855178, 629671588,
        24514907, 996173970, 363395222, 565042129, 733596141, 267099868, 15311432, 0, 0, 0, 0, 0,
        0,
    ];
    // root := pow(3, (998244353-1) >> 23)
    // BASE[0] = pow(root, 1<<23);
    // BASE[1] = pow(root, 1<<22);
    // ...
    // BASE[23] = pow(root, 1<<0);
    const ROT: [u32; 30] = [
        911660635, 509520358, 369330050, 332049552, 983190778, 123842337, 238493703, 975955924,
        603855026, 856644456, 131300601, 842657263, 730768835, 942482514, 806263778, 151565301,
        510815449, 503497456, 743006876, 741047443, 56250497, 867605899, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    // ROT[0] := pow(root, 1<<21)
    // ROT[1] := pow(root, (1<<20) - (1<<21))
    // ...
    // ROT[21] :- pow(root, (1<<0) - (1<<1) - ... - (1<<21))
    const INV_ROT: [u32; 30] = [
        86583718, 372528824, 373294451, 645684063, 112220581, 692852209, 155456985, 797128860,
        90816748, 860285882, 927414960, 354738543, 109331171, 293255632, 535113200, 308540755,
        121186627, 608385704, 438932459, 359477183, 824071951, 103369235, 0, 0, 0, 0, 0, 0, 0, 0,
    ];
    // INV_ROT[i] * ROT[i] = 1, 0 <= i <= 21
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
impl<M: Modulus> SubAssign<Self> for Fps<M> {
    fn sub_assign(&mut self, rhs: Self) {
        let n = std::cmp::max(self.len(), rhs.len());
        self.resize(n, 0);
        for (e, &x) in self.iter_mut().zip(rhs.iter()) {
            *e = M::sub(*e, x);
        }
    }
}

fn ceil_log2(n: usize) -> usize {
    debug_assert!(n > 0);
    32 - (n as u32 - 1).leading_zeros() as usize
}

impl<M: Modulus> Fps<M> {
    pub fn butterfly(a: &mut [u32]) {
        let n = a.len();
        debug_assert!(n.is_power_of_two());
        let h = ceil_log2(n);

        for len in 0..h {
            let p = 1 << h - 1 - len;

            for j in 0..p {
                let x = a[j];
                let y = a[j + p];
                a[j] = M::add(x, y);
                a[j + p] = M::sub(x, y);
            }

            let mut rot = M::ROT[0];
            for s in 1..1 << len {
                let offset = s << h - len;
                for j in offset..offset + p {
                    let x = a[j];
                    let y = M::mul(a[j + p], rot);
                    a[j] = M::add(x, y);
                    a[j + p] = M::sub(x, y);
                }
                rot = M::mul(rot, M::ROT[(!s).trailing_zeros() as usize]);
            }
        }
    }
    pub fn butterfly_inv(a: &mut [u32]) {
        let n = a.len();
        debug_assert!(n.is_power_of_two());
        let h = ceil_log2(n);

        for len in (0..h).rev() {
            let p = 1 << h - 1 - len;

            for j in 0..p {
                let x = a[j];
                let y = a[j + p];
                a[j] = M::add(x, y);
                a[j + p] = M::sub(x, y);
            }

            let mut rot = M::INV_ROT[0];
            for s in 1..1 << len {
                let offset = s << h - len;
                for j in offset..offset + p {
                    let x = a[j];
                    let y = a[j + p];
                    a[j] = M::add(x, y);
                    a[j + p] = M::mul(M::sub(x, y), rot);
                }
                rot = M::mul(rot, M::INV_ROT[(!s).trailing_zeros() as usize]);
            }
        }
    }

    pub fn butterfly_doubling(a: &mut Vec<u32>) {
        let n = a.len();
        let h = ceil_log2(n);
        let mut b = a.clone();
        Self::butterfly_inv(&mut b);
        let mut rot = M::inv(n as u32);
        for e in b.iter_mut() {
            *e = M::mul(*e, rot);
            rot = M::mul(rot, M::BASE[h + 1]);
        }
        Self::butterfly(&mut b);
        a.extend(b);
    }

    pub fn convolution(a: &[u32], b: &[u32]) -> Self {
        if a.is_empty() || b.is_empty() {
            return vec![].into();
        }
        let (n, m) = (a.len(), b.len());

        let (mut a, mut b) = (a.to_owned(), b.to_owned());
        let z = 1 << ceil_log2(n + m - 1);
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
        let (mut p, mut q) = (Self::from(p.to_owned()), Self::from(q.to_owned()));

        let n = 1 << ceil_log2(p.len() + q.len() - 1);
        p.resize(2 * n, 0);
        q.resize(2 * n, 0);
        Self::butterfly(&mut p);
        Self::butterfly(&mut q);

        loop {
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
            if k < n as u64 {
                break;
            }

            Self::butterfly_doubling(&mut p);
            Self::butterfly_doubling(&mut q);
        }

        Self::butterfly_doubling(&mut p);

        Self::butterfly_inv(&mut q);
        q = Self::inv(&q, n);
        q.resize(2 * n, 0);
        Self::butterfly(&mut q);

        for (e, &x) in q.iter_mut().zip(p.iter()) {
            *e = M::div2(M::mul(*e, x));
        }
        Self::butterfly_inv(&mut q);

        q[k as usize]
    }
}
