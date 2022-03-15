use std::cmp::min;
use std::fmt::Debug;
use std::ops::{Deref,DerefMut,DivAssign,MulAssign,Add,Sub,Mul,Div,Neg};
use std::iter::successors;
use std::marker::PhantomData;

fn pow<T: Copy + Clone + MulAssign + From<u32>>(mut a: T, mut n: u32) -> T {
    let mut r = T::from(1);
    while n > 0 {
        if (n & 1) == 1 {
            r *= a;
        }
        a *= a;
        n >>= 1;
    }
    r
}
fn primitive_root(m: u32) -> u32 {
    match m {
        998244353 => return 3,
        _ => panic!("Not implemented"),
    }
}

pub trait Modulus {
    const VALUE: u32;
}

pub struct Fps<M: Modulus, T>(Vec<T>, PhantomData<M>);
pub struct Mod998244353 {}
impl Modulus for Mod998244353 {
    const VALUE: u32 = 998244353;
}
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

impl<M: Modulus, T: Copy + Clone + MulAssign> MulAssign<T> for Fps<M, T> {
    fn mul_assign(&mut self, rhs: T) {
        self.iter_mut().for_each(|e| *e *= rhs );
    }
}
impl<M: Modulus, T: Copy + Clone + DivAssign> DivAssign<T> for Fps<M, T> {
    fn div_assign(&mut self, rhs: T) {
        self.iter_mut().for_each(|e| *e /= rhs);
    }
}

fn ceil_log2(n: u32) -> u32 {
    debug_assert!(n > 0);
    32 - (n-1).leading_zeros()
}

impl<M: Modulus, T> Fps<M, T>
where T: Copy + Clone + From<u32> + Add<Output=T> + Sub<Output=T> + Mul<Output=T> + Div<Output=T> + MulAssign + Neg<Output=T> + Debug
{
    pub fn butterfly(a: &mut [T]) {
        let n = a.len();
        debug_assert!(n.is_power_of_two());
        let h = ceil_log2(n as u32) as usize;

        let root = pow(T::from(primitive_root(M::VALUE)), (M::VALUE - 1) >> h);
        let mut es = successors(Some(root), |&x| Some(-x * x)).take(h-1).collect::<Vec<_>>();
        es.reverse();

        for c in 0..h {
            let w = 1<<h-1-c;
            let mut p = T::from(1);
            for i in 0..1<<c {
                let s = i * 2 * w;
                for j in s..s+w {
                    let x = a[j];
                    let y = a[j + w] * p;
                    a[j] = x + y;
                    a[j + w] = x - y;
                }
                if i+1 != 1<<c {
                    p *= es[(!i).trailing_zeros() as usize];
                }
            }
        }
    }
    pub fn butterfly_inv(a: &mut [T]) {
        let n = a.len();
        debug_assert!(n.is_power_of_two());
        let h = ceil_log2(n as u32) as usize;

        let root = pow(T::from(primitive_root(M::VALUE)), (M::VALUE - 1) >> h);
        let root = pow(root, M::VALUE-2);
        let mut es = successors(Some(root), |&x| Some(-x * x)).take(h-1).collect::<Vec<_>>();
        es.reverse();

        for c in (0..h).rev() {
            let w = 1<<h-1-c;
            let mut p = T::from(1);
            for i in 0..1<<c {
                let s = i * 2 * w;
                for j in s..s+w {
                    let x = a[j];
                    let y = a[j + w];
                    a[j] = x + y;
                    a[j + w] = (x - y) * p;
                }
                if i+1 != 1<<c {
                    p *= es[(!i).trailing_zeros() as usize];
                }
            }
        }
    }

    pub fn convolution(a: &[T], b: &[T]) -> Self {
        if a.is_empty() || b.is_empty() {
            return vec![].into();
        }
        let (n, m) = (a.len(), b.len());

        let (mut a, mut b) = (a.to_owned(), b.to_owned());
        let z = 1 << ceil_log2((n + m - 1) as _);
        a.resize(z, T::from(0));
        Self::butterfly(&mut a);
        b.resize(z, T::from(0));
        Self::butterfly(&mut b);
        for (a, &b) in a.iter_mut().zip(&b) {
            *a *= b;
        }
        Self::butterfly_inv(&mut a);
        a.resize(n + m - 1, T::from(0));
        let iz = T::from(1) / T::from(z as u32);
        for a in &mut a {
            *a *= iz;
        }
        a.into()
    }


    pub fn inv(&self, d: usize) -> Self {
        debug_assert!(d > 0);
        debug_assert!(self.len() > 0);
        let mut inv = vec![T::from(1) / self[0]];
        for m in (0..).map(|i| 1<<i).take_while(|&m| m < d) {
            let mut f = self[0..min(2*m, self.len())].to_owned();
            let mut g = inv.clone();
            f.resize(2*m, T::from(0));
            g.resize(2*m, T::from(0));
            Self::butterfly(&mut f);
            Self::butterfly(&mut g);
            for (a, &b) in f.iter_mut().zip(&g) {
                *a *= b;
            }
            Self::butterfly_inv(&mut f);

            f.drain(0..m);
            f.resize(2*m, T::from(0));
            Self::butterfly(&mut f);
            for (a, &b) in f.iter_mut().zip(&g) {
                *a *= b;
            }
            Self::butterfly_inv(&mut f);

            let iz = T::from(1) / T::from(2*m as u32);
            let iz = -iz * iz;

            for &a in &f[0..min(d - inv.len(), m)] {
                inv.push(a * iz);
            }
        }
        debug_assert_eq!(inv.len(), d);
        inv.into()
    }

    pub fn bostan_mori(p: &[T], q: &[T], mut n: u64) -> T {
        let (mut p, mut q) = (p.to_owned(), q.to_owned());
        while n > 0 {
            let r = (0..q.len()).map(|i| if (i&1) == 1 { -q[i] } else { q[i] }).collect::<Vec<_>>();
            p = Self::convolution(&p, &r).iter().skip((n&1) as usize).step_by(2).cloned().collect::<Vec<_>>();
            q = Self::convolution(&q, &r).iter().step_by(2).cloned().collect::<Vec<_>>();
            n >>= 1;
        }
        return p[0] / q[0];
    }
}
