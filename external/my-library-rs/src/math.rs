use std::convert::From;
use std::ops::{AddAssign, Div, Mul};

pub struct Combination<T> {
    fact: Vec<T>,
    ifact: Vec<T>,
}

impl<T> Combination<T>
where
    T: Copy + From<usize> + Mul<Output = T> + Div<Output = T>,
{
    pub fn new(n: usize) -> Self {
        let (mut fact, mut ifact) = (vec![], vec![]);
        fact.reserve(n + 1);
        ifact.reserve(n + 1);

        fact.push(1.into());
        for i in 0..n {
            fact.push(fact[i] * (i + 1).into());
        }

        ifact.push(T::from(1) / fact[n]);
        for i in 0..n {
            ifact.push(ifact[i] * (n - i).into());
        }
        ifact.reverse();

        Self { fact, ifact }
    }

    pub fn c(&self, n: usize, r: usize) -> T {
        if n < r {
            return 0.into();
        }
        self.fact[n] * self.ifact[r] * self.ifact[n - r]
    }
}

fn bitwise_transform<T>(a: &mut Vec<T>, f: fn(*mut T, *mut T)) {
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
pub fn subset_zeta_transform<T>(a: &mut Vec<T>)
where
    T: Copy + AddAssign,
{
    bitwise_transform(a, |x: *mut T, y: *mut T| unsafe {
        *y += *x;
    });
}
