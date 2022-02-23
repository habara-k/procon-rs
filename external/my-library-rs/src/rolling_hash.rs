use lazy_static::lazy_static;
use num::ToPrimitive;
use rand::distributions::{Distribution, Uniform};
use std::marker::PhantomData;

/// Rolling Hash
/// - 法: 2^61 - 1
/// - 基数: 実行時ランダム
/// # Example
/// ```
/// use my_library_rs::*;
///
/// // 文字列
/// let s = "abrakadabra";
/// let hash = RollingHash::new(&s.as_bytes());
/// assert_eq!(hash.get(0, 4), hash.get(7, 11));  // abra == abra
/// assert_ne!(hash.get(0, 4), hash.get(6, 10));  // abra != dabr
///
/// // 数列
/// let a = vec![3,1,4,2,8,5,7,1,4,2,8];
/// let hash = RollingHash::new(&a);
/// assert_eq!(hash.get(1, 5), hash.get(7, 11));  // [1,4,2,8] == [1,4,2,8]
/// assert_ne!(hash.get(0, 5), hash.get(7, 11));  // [3,1,4,2] != [1,4,2,8]
/// ```
pub struct RollingHash<T> {
    hash: Vec<u64>,
    pow: Vec<u64>,
    _marker: PhantomData<fn() -> T>,
}
impl<T: Copy + ToPrimitive> RollingHash<T> {
    pub fn new(s: &[T]) -> Self {
        let n = s.len();
        let (mut hash, mut pow) = (Vec::with_capacity(n + 1), Vec::with_capacity(n + 1));
        hash.push(0);
        pow.push(1);
        for i in 0..n {
            hash.push(modulo(
                mul(hash[i], *ROLLINGHASH_BASE) + s[i].to_u64().unwrap(),
            ));
            pow.push(mul(pow[i], *ROLLINGHASH_BASE));
        }
        Self {
            hash,
            pow,
            _marker: PhantomData,
        }
    }
    pub fn get(&self, l: usize, r: usize) -> u64 {
        modulo(self.hash[r] + MOD - mul(self.hash[l], self.pow[r - l]))
    }
}

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
