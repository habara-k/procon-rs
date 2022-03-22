use crate::modulo::*;

fn ceil_log2(n: usize) -> usize {
    debug_assert!(n > 0);
    32 - (n as u32 - 1).leading_zeros() as usize
}

pub fn butterfly<M: Modulus>(a: &mut [u32]) {
    let n = a.len();
    debug_assert!(n.is_power_of_two());
    let h = ceil_log2(n);

    for len in 0..h {
        let p = 1 << h - 1 - len;

        for j in 0..p {
            let (x, y) = (a[j], a[j + p]);
            a[j] = M::add(x, y);
            a[j + p] = M::sub(x, y);
        }

        let mut rot = M::ROT[0];
        for s in 1..1 << len {
            let offset = s << h - len;
            for j in offset..offset + p {
                let (x, y) = (a[j], M::mul(a[j + p], rot));
                a[j] = M::add(x, y);
                a[j + p] = M::sub(x, y);
            }
            rot = M::mul(rot, M::ROT[(!s).trailing_zeros() as usize]);
        }
    }
}

pub fn butterfly_inv<M: Modulus>(a: &mut [u32]) {
    let n = a.len();
    debug_assert!(n.is_power_of_two());
    let h = ceil_log2(n);

    for len in (0..h).rev() {
        let p = 1 << h - 1 - len;

        for j in 0..p {
            let (x, y) = (a[j], a[j + p]);
            a[j] = M::add(x, y);
            a[j + p] = M::sub(x, y);
        }

        let mut rot = M::INV_ROT[0];
        for s in 1..1 << len {
            let offset = s << h - len;
            for j in offset..offset + p {
                let (x, y) = (a[j], a[j + p]);
                a[j] = M::add(x, y);
                a[j + p] = M::mul(M::sub(x, y), rot);
            }
            rot = M::mul(rot, M::INV_ROT[(!s).trailing_zeros() as usize]);
        }
    }
}

pub fn butterfly_doubling<M: Modulus>(a: &mut Vec<u32>) {
    let n = a.len();
    let h = ceil_log2(n) + 1;
    let mut b = a.clone();
    butterfly_inv::<M>(&mut b);
    let mut rot = M::inv(n as u32);
    for e in b.iter_mut() {
        *e = M::mul(*e, rot);
        rot = M::mul(rot, M::BASE[h]);
    }
    butterfly::<M>(&mut b);
    a.extend(b);
}
