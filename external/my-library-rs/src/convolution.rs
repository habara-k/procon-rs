use crate::modulo::*;
use std::ops::{Add, Div, Mul, MulAssign, Sub};

fn ceil_log2(n: usize) -> usize {
    debug_assert!(n > 0);
    32 - (n as u32 - 1).leading_zeros() as usize
}

pub fn butterfly<M, T>(a: &mut [T])
where
    M: Modulus,
    T: Clone
        + Copy
        + From<u32>
        + Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + MulAssign<u32>,
{
    let n = a.len();
    debug_assert!(n.is_power_of_two());
    let h = ceil_log2(n);

    for len in 0..h {
        let p = 1 << h - 1 - len;

        for j in 0..p {
            let (x, y) = (a[j], a[j + p]);
            a[j] = x + y;
            a[j + p] = x - y;
        }

        let mut rot = T::from(M::ROT[0]);
        for s in 1..1 << len {
            let offset = s << h - len;
            for j in offset..offset + p {
                let (x, y) = (a[j], a[j + p] * rot);
                a[j] = x + y;
                a[j + p] = x - y;
            }
            rot *= M::ROT[(!s).trailing_zeros() as usize];
        }
    }
}

pub fn butterfly_inv<M, T>(a: &mut [T])
where
    M: Modulus,
    T: Clone
        + Copy
        + From<u32>
        + Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + MulAssign<u32>,
{
    let n = a.len();
    debug_assert!(n.is_power_of_two());
    let h = ceil_log2(n);

    for len in (0..h).rev() {
        let p = 1 << h - 1 - len;

        for j in 0..p {
            let (x, y) = (a[j], a[j + p]);
            a[j] = x + y;
            a[j + p] = x - y;
        }

        let mut rot = T::from(M::INV_ROT[0]);
        for s in 1..1 << len {
            let offset = s << h - len;
            for j in offset..offset + p {
                let (x, y) = (a[j], a[j + p]);
                a[j] = x + y;
                a[j + p] = (x - y) * rot;
            }
            rot *= M::INV_ROT[(!s).trailing_zeros() as usize];
        }
    }
}

pub fn butterfly_doubling<M, T>(a: &mut Vec<T>)
where
    M: Modulus,
    T: Clone
        + Copy
        + From<u32>
        + Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>
        + MulAssign<T>
        + MulAssign<u32>
        + Div<Output = T>,
{
    let n = a.len();
    let h = ceil_log2(n) + 1;
    let mut b = a.clone();
    butterfly_inv::<M, T>(&mut b);
    let mut rot = T::from(1) / T::from(n as u32);
    for e in b.iter_mut() {
        *e *= rot;
        rot *= M::BASE[h];
    }
    butterfly::<M, T>(&mut b);
    a.extend(b);
}
