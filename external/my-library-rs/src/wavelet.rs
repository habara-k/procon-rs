use std::mem::swap;

#[derive(Clone)]
struct BitVector {
    n: usize,
    bit: Vec<u64>,
    sum: Vec<usize>,
}
impl BitVector {
    pub fn new(n: usize) -> Self {
        Self {
            n,
            bit: vec![0; (n >> 6) + 1],
            sum: vec![0],
        }
    }
    pub fn set(&mut self, k: usize) {
        assert!(k < self.n);
        self.bit[k >> 6] |= 1u64 << (k & 63);
    }
    pub fn build(&mut self) {
        for i in 0..self.bit.len() {
            self.sum.push(self.sum[i] + self.bit[i].count_ones() as usize);
        }
    }
    /// k 番目の要素を取得. O(1)
    pub fn get(&self, k: usize) -> bool {
        assert!(k < self.n);
        (self.bit[k >> 6] >> (k & 63) & 1) == 1
    }
    fn rank1(&self, k: usize) -> usize {
        assert!(k <= self.n);
        self.sum[k >> 6] + (self.bit[k >> 6] & ((1u64 << (k & 63)) - 1)).count_ones() as usize
    }
    /// 区間 [0, k) に現れる f の総数. O(1)
    pub fn rank(&self, k: usize, f: bool) -> usize {
        assert!(k <= self.n);
        if f {
            self.rank1(k)
        } else {
            k - self.rank1(k)
        }
    }
    /// (k+1)個目の f が現れる index. O(log n)
    pub fn select(&self, mut k: usize, f: bool) -> Option<usize> {
        if self.rank(self.n, f) <= k {
            return None;
        }
        let mut l = 0;
        let mut r = self.n;
        while r - l > 1 {
            let m = (l + r) / 2;
            if self.rank(m, f) >= k+1 {
                r = m;
            } else {
                l = m;
            }
        }
        Some(l)
    }
    /// 区間[l,n) において (k+1)個目の f が現れる index. O(log n)
    pub fn select_after(&self, mut k: usize, f: bool, l: usize) -> Option<usize> {
        self.select(k + self.rank(l, f), f)
    }
}

/// ```
/// use my_library_rs::*;
///
/// let wm = WaveletMatrix::new(&[0,7,2,1,4,3,6,7,2,5,0,4,7,2,6,3]);
/// assert_eq!(wm.rank(12, 2), 2);
/// assert_eq!(wm.select(1, 2), Some(8));
/// assert_eq!(wm.kth_largest(4, 12, 2), 5);
/// assert_eq!(wm.range_freq(5, 14, 2, 5), 4);
/// ```
pub struct WaveletMatrix {
    n: usize,
    bits: Vec<BitVector>,
    mid: [usize; 64],
}
impl WaveletMatrix {
    pub fn new(a: &[u64]) -> Self {
        let n = a.len();
        let mut a = a.to_owned();
        let mut bits = vec![BitVector::new(n); 64];
        let mut mid = [0; 64];
        for level in (0..64).rev() {
            let mut l = vec![];
            let mut r = vec![];
            for i in 0..a.len() {
                if (a[i] >> level) & 1 == 1 {
                    bits[level].set(i);
                    r.push(a[i]);
                } else {
                    l.push(a[i]);
                }
            }
            mid[level] = l.len();
            bits[level].build();
            l.extend(r);
            swap(&mut a, &mut l);
        }
        Self { n, bits, mid }
    }

    fn succ(&self, f: bool, k: usize, level: usize) -> usize {
        self.bits[level].rank(k, f) + self.mid[level] * f as usize
    }

    /// k 番目の要素を取得. O(log σ)
    pub fn access(&self, mut k: usize) -> u64 {
        let mut x = 0u64;
        for level in (0..64).rev() {
            let f = self.bits[level].get(k);
            if f {
                x |= 1u64 << level;
            }
            k = self.succ(f, k, level);
        }
        x
    }
    /// 区間 [0, r) に現れる x の総数. O(log σ)
    pub fn rank(&self, mut r: usize, x: u64) -> usize {
        let mut l = 0;
        for level in (0..64).rev() {
            let f = (x >> level & 1) == 1;
            l = self.succ(f, l, level);
            r = self.succ(f, r, level);
        }
        r - l
    }
    /// (k+1)個目の x が現れる index. O(log σ log n)
    pub fn select(&self, mut k: usize, x: u64) -> Option<usize> {
        let mut l = [0; 64];
        let mut r = [self.n; 64];
        for level in (1..64).rev() {
            let f = (x >> level & 1) == 1;
            l[level-1] = self.succ(f, l[level], level);
            r[level-1] = self.succ(f, r[level], level);
        }

        for level in 0..64 {
            let f = (x >> level & 1) == 1;
            let s = self.bits[level].select_after(k, f, l[level]);
            if s.is_none() {
                return None;
            }
            k = s.unwrap();
            if k >= r[level] {
                return None;
            }
            k -= l[level];
        }
        Some(k)
    }
    /// 区間[l,n) において (k+1)個目の x が現れる index. O(log σ log n)
    pub fn select_after(&self, mut k: usize, x: u64, l: usize) -> Option<usize> {
        self.select(k + self.rank(l, x), x)
    }


    /// 区間 [l, r) において k 番目に小さい要素. O(log σ)
    pub fn kth_smallest(&self, mut l: usize, mut r: usize, mut k: usize) -> u64 {
        assert!(l <= r);
        assert!(k < r - l);
        let mut x = 0u64;
        for level in (0..64).rev() {
            let cnt = self.bits[level].rank(r, false) - self.bits[level].rank(l, false);
            let f = cnt <= k;
            if f {
                x |= 1u64 << level;
                k -= cnt;
            }
            l = self.succ(f, l, level);
            r = self.succ(f, r, level);
        }
        x
    }
    /// 区間 [l, r) において k 番目に大きい要素. O(log σ)
    pub fn kth_largest(&self, l: usize, r: usize, k: usize) -> u64 {
        self.kth_smallest(l, r, r - l - k - 1)
    }

    pub fn _range_freq(&self, mut l: usize, mut r: usize, upper: u64) -> usize {
        let mut s = 0;
        for level in (0..64).rev() {
            let f = (upper >> level & 1) == 1;
            if f {
                s += self.bits[level].rank(r, false) - self.bits[level].rank(l, false);
            }
            l = self.succ(f, l, level);
            r = self.succ(f, r, level);
        }
        s
    }
    /// [l, r) における lower 以上 upper 未満の要素数. O(log σ)
    pub fn range_freq(&self, l: usize, r: usize, lower: u64, upper: u64) -> usize {
        self._range_freq(l, r, upper) - self._range_freq(l, r, lower)
    }

    /// 区間[l, r) における upper 未満の最大値. O(log σ)
    pub fn prev_value(&self, l: usize, r: usize, upper: u64) -> Option<u64> {
        let cnt = self._range_freq(l, r, upper);
        if cnt == 0 {
            None
        } else {
            Some(self.kth_smallest(l, r, cnt-1))
        }
    }
    /// 区間[l, r) における lower 以上の最小値. O(log σ)
    pub fn next_value(&self, l: usize, r: usize, lower: u64) -> Option<u64> {
        let cnt = self._range_freq(l, r, lower);
        if cnt == r - l {
            None
        } else {
            Some(self.kth_smallest(l, r, cnt))
        }
    }
}
