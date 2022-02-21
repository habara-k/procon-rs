pub struct RollingHash {
    hash: Vec<u64>,
    pow: Vec<u64>,
}
impl RollingHash {
    pub fn new(s: &Vec<u64>) -> Self {
        let n = s.len();
        let (mut hash, mut pow) = (Vec::with_capacity(n + 1), Vec::with_capacity(n + 1));
        hash.push(0);
        pow.push(1);
        for i in 0..n {
            hash.push(modulo(mul(hash[i], *ROLLINGHASH_BASE) + s[i]));
            pow.push(mul(pow[i], *ROLLINGHASH_BASE));
        }
        Self { hash, pow }
    }
    pub fn get(&self, l: usize, r: usize) -> u64 {
        modulo(self.hash[r] + MOD - mul(self.hash[l], self.pow[r - l]))
    }
}

use lazy_static::lazy_static;
use rand::distributions::{Distribution, Uniform};

const MOD: u64 = (1 << 61) - 1;
fn mul(x: u64, y: u64) -> u64 {
    let t = x as u128 * y as u128;
    let t = (t >> 61) + (t & MOD as u128);
    modulo(t as u64)
}
fn modulo(x: u64) -> u64 {
    assert!(x < 2 * MOD);
    if x >= MOD {
        x - MOD
    } else {
        x
    }
}

lazy_static! {
    static ref ROLLINGHASH_BASE: u64 = {
        let mut rng = rand::thread_rng();
        Uniform::from(0..MOD).sample(&mut rng)
    };
}
