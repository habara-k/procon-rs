use std::convert::From;
use std::ops::{Div, Mul};

pub struct Combination<T> {
    fact: Vec<T>,
    ifact: Vec<T>,
}

impl<T> Combination<T>
where T: Copy + From<usize> + Mul<Output = T> + Div<Output = T>
{
    pub fn new(n: usize) -> Self {
        let (mut fact, mut ifact) = (vec![], vec![]);
        fact.reserve(n + 1);
        ifact.reserve(n + 1);

        fact.push(T::from(1));
        for i in 0..n {
            fact.push(fact[i] * T::from(i + 1));
        }

        ifact.push(T::from(1) / fact[n]);
        for i in 0..n {
            ifact.push(ifact[i] * T::from(n - i));
        }
        ifact.reverse();

        Self { fact, ifact }
    }

    pub fn c(&self, n: usize, r: usize) -> T {
        if n < r {
            return T::from(0);
        }
        self.fact[n] * self.ifact[r] * self.ifact[n - r]
    }
}



fn bitwise_transform<T>(a: &mut Vec<T>, f: fn(*mut T, *mut T))
{
    let n = a.len();
    assert_eq!(n & (n-1), 0);

    let ptr = a.as_mut_ptr();
    for block in (0..).map(|k| 1<<k).take_while(|&b| b < n) {
        for l in (0..n).step_by(block << 1) {
            for i in l..l+block {
                unsafe {
                    f(ptr.add(i), ptr.add(i + block));
                }
            }
        }
    }
}

use std::ops::AddAssign;
pub fn subset_zeta_transform<T>(a: &mut Vec<T>)
    where T: Copy + AddAssign
{
    bitwise_transform(a, |x: *mut T, y: *mut T| {
        unsafe {
            *y += *x;
        }
    });
}

