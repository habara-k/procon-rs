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

