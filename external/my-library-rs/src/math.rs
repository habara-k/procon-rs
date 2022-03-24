use std::convert::From;
use std::ops::{AddAssign, Div, Mul, SubAssign};

/// 二項係数を計算する.
/// NOTE: ACLibrary のModInt のような有限体が渡されることを想定している.
/// # Example
/// ```
/// use my_library_rs::*;
/// use std::ops::{Mul, Div};
///
/// const MOD: u64 = 1_000_000_007;
/// fn pow(mut a: u64, mut n: u64) -> u64 {
///     let mut r = 1;
///     while n > 0 {
///         if n & 1 == 1 {
///             r *= a;
///             r %= MOD;
///         }
///         a *= a;
///         a %= MOD;
///         n >>= 1;
///     }
///     r
/// }
/// #[derive(Copy, Clone)]
/// struct ModInt {
///     val: u64,
/// }
/// impl From<u32> for ModInt {
///     fn from(val: u32) -> Self {
///         Self { val: val as u64 }
///     }
/// }
/// impl Mul for ModInt {
///     type Output = Self;
///     fn mul(self, rhs: Self) -> Self::Output {
///         Self { val: ((self.val * rhs.val) % MOD) as u64 }
///     }
/// }
/// impl Div for ModInt {
///     type Output = Self;
///     fn div(self, rhs: Self) -> Self::Output {
///         self * Self { val: pow(rhs.val, MOD-2) }
///     }
/// }
/// let comb = Combination::<ModInt>::new(10);
/// assert_eq!(comb.C(10, 3).val, (10 * 9 * 8) / (3 * 2 * 1) as u64);
/// ```
pub struct Combination<T> {
    pub fact: Vec<T>,
    pub finv: Vec<T>,
}

impl<T> Combination<T>
where
    T: Copy + From<u32> + Mul<Output = T> + Div<Output = T>,
{
    pub fn new(n: usize) -> Self {
        let (mut fact, mut finv) = (Vec::with_capacity(n + 1), Vec::with_capacity(n + 1));

        fact.push(T::from(1));
        for i in 0..n {
            fact.push(fact[i] * T::from((i + 1) as u32));
        }

        finv.push(T::from(1) / fact[n]);
        for i in 0..n {
            finv.push(finv[i] * T::from((n - i) as u32));
        }
        finv.reverse();

        Self { fact, finv }
    }

    #[allow(non_snake_case)]
    pub fn C(&self, n: usize, r: usize) -> T {
        if n < r {
            return T::from(0);
        }
        self.fact[n] * self.finv[r] * self.finv[n - r]
    }

    #[allow(non_snake_case)]
    pub fn P(&self, n: usize, r: usize) -> T {
        if n < r {
            return T::from(0);
        }
        self.fact[n] * self.finv[n - r]
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

/// ラグランジュ補間
/// n次多項式 f(x) に対して f(0), ..., f(n), t を入力すると, f(t) を返す.
pub fn lagrange_polynomial<
    T: Clone
        + Copy
        + From<i64>
        + From<u32>
        + Mul<Output = T>
        + Div<Output = T>
        + SubAssign
        + AddAssign,
>(
    f: &[T],
    t: i64,
) -> T {
    let n = f.len() - 1;
    if t <= n as i64 {
        return f[t as usize];
    }
    let fact = Combination::new(n);
    let mut lp = vec![T::from(1u32); n + 1];
    let mut rp = vec![T::from(1u32); n + 1];
    for i in 0..n {
        lp[i + 1] = lp[i] * T::from(t - i as i64);
    }
    for i in (1..=n).rev() {
        rp[i - 1] = rp[i] * T::from(t - i as i64);
    }
    let mut ans = T::from(0u32);
    for i in 0..=n {
        let x = f[i] * fact.finv[i] * fact.finv[n - i] * lp[i] * rp[i];
        if ((n - i) & 1) == 1 {
            ans -= x;
        } else {
            ans += x;
        }
    }
    ans
}
