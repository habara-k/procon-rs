use std::convert::From;
use std::ops::{AddAssign, Div, Mul};

/// 二項係数を計算する.
/// NOTE: ACLibrary のModInt が渡されることを想定している.
pub struct Combination<T> {
    fac: Vec<T>,
    inv: Vec<T>,
}

impl<T> Combination<T>
where
    T: Copy + From<usize> + Mul<Output = T> + Div<Output = T>,
{
    pub fn new(n: usize) -> Self {
        let (mut fac, mut inv) = (Vec::with_capacity(n + 1), Vec::with_capacity(n + 1));

        fac.push(T::from(1));
        for i in 0..n {
            fac.push(fac[i] * T::from(i + 1));
        }

        inv.push(T::from(1) / fac[n]);
        for i in 0..n {
            inv.push(inv[i] * T::from(n - i));
        }
        inv.reverse();

        Self { fac, inv }
    }

    pub fn c(&self, n: usize, r: usize) -> T {
        if n < r {
            return T::from(0);
        }
        self.fac[n] * self.inv[r] * self.inv[n - r]
    }
}

fn bitwise_transform<T>(a: &mut [T], f: fn(*mut T, *mut T)) {
    let n = a.len();
    assert_eq!(n & (n - 1), 0);

    let ptr = a.as_mut_ptr();
    for block in (0..).map(|k| 1 << k).take_while(|&b| b < n) {
        for l in (0..n).step_by(block << 1) {
            for i in l..l + block {
                unsafe {
                    f(ptr.add(i), ptr.add(i + block));
                }
            }
        }
    }
}

/// 下位集合に対する高速ゼータ変換を行う.
/// # Example
/// ```
/// use my_library_rs::*;
/// let mut a = vec![0; 8];
/// a[0b001] = 1;
/// a[0b010] = 10;
/// a[0b100] = 100;
/// subset_zeta_transform(&mut a);
/// assert_eq!(a[0b000], 0);
/// assert_eq!(a[0b001], 1);
/// assert_eq!(a[0b010], 10);
/// assert_eq!(a[0b011], 11);
/// assert_eq!(a[0b100], 100);
/// assert_eq!(a[0b101], 101);
/// assert_eq!(a[0b110], 110);
/// assert_eq!(a[0b111], 111);
/// ```
pub fn subset_zeta_transform<T>(a: &mut [T])
where
    T: Copy + AddAssign,
{
    bitwise_transform(a, |x: *mut T, y: *mut T| unsafe {
        *y += *x;
    });
}
