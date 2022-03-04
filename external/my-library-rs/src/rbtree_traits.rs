use crate::algebra::{MapMonoid, Monoid};
use std::mem;
use std::ops::Deref;

const RED: bool = false;
const BLACK: bool = true;

pub trait Node: Sized {
    type Value: Clone;
    type Link: Deref<Target = Self>;

    /// ノード`l, r` を `black` で繋げたノードを返す.
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link;

    /// 値 `val` を持たせた葉ノードを返す.
    fn new_leaf(val: Self::Value) -> Self::Link;

    /// 葉でないノード `p` の左右の子 `l, r` を返す.
    fn detach(p: Self::Link) -> (Self::Link, Self::Link);

    /// 黒で塗ったノードを返す.
    fn make_root(p: Self::Link) -> Self::Link;

    /// ノードが持つ値を返す.
    fn val(&self) -> Self::Value;

    /// 色を返す.
    fn black(&self) -> bool;

    /// 黒高さを返す.
    fn height(&self) -> usize;

    /// 葉の数を返す.
    fn size(&self) -> usize;

    fn is_leaf(&self) -> bool {
        self.black() && self.height() == 1
    }

    fn len(p: &Option<Self::Link>) -> usize {
        p.as_ref().map_or(0, |p| p.size())
    }
    fn is_root(p: &Option<Self::Link>) -> bool {
        p.as_ref().map_or(true, |p| p.black())
    }

    fn merge(a: Option<Self::Link>, b: Option<Self::Link>) -> Option<Self::Link> {
        debug_assert!(Self::is_root(&a) && Self::is_root(&b));
        if a.is_none() {
            return b;
        }
        if b.is_none() {
            return a;
        }
        Some(Self::make_root(Self::merge_sub(a.unwrap(), b.unwrap())))
    }

    /// 木 `a, b` を併合する
    /// # Required
    /// `a, b` はそれぞれ空でなく, 根が黒である.
    ///
    /// # Ensured
    /// 併合後の木を `c` とすると,
    /// `c.height == max(a.height, b.height)` が成立する.
    /// ただし `c` の根が黒であるとは限らない.
    ///
    /// # 計算量
    /// O(|`a.height - b.height`|)
    ///
    fn merge_sub(a: Self::Link, b: Self::Link) -> Self::Link {
        debug_assert!(a.black());
        debug_assert!(b.black());

        if a.height() < b.height() {
            let (l, r) = Self::detach(b);
            //      b(BLACK,h+1)
            //       /     \
            //   l(*,h)    r(*,h)

            if l.black() {
                // Connect directly:
                //               (BLACK,h+1)
                //                /        \
                //   merge_sub(a,l)(*,h)   r(*,h)
                return Self::new(Self::merge_sub(a, l), r, BLACK);
            }

            let (ll, lr) = Self::detach(l);
            //           b(BLACK,h+1)
            //           /      \
            //       l(RED,h)   r(*,h)
            //       /       \
            //   ll(BLACK,h)  lr(BLACK,h)

            let c = Self::merge_sub(a, ll);
            if c.black() {
                // Connect directly:
                //             (BLACK,h+1)
                //             /    \
                //         (RED,h)   r(BLACK,h)
                //         /    \
                //   c(BLACK,h)  lr(BLACK,h)
                return Self::new(Self::new(c, lr, RED), r, BLACK);
            }

            return if r.black() {
                // Rotate tree:
                //             (BLACK,h+1)                (BLACK,h+1)
                //             /    \                     /     \
                //         (RED,h)  r(BLACK,h)   =>   c(RED,h)  (RED,h)
                //        /    \                                /    \
                //   c(RED,h)   lr(BLACK,h)              lr(BLACK,h)  r(BLACK,h)
                Self::new(c, Self::new(lr, r, RED), BLACK)
            } else {
                // Change color:
                //             (BLACK,h+1)                   (RED,h+1)
                //             /    \                        /       \
                //         (RED,h)  r(RED,h)     =>      (BLACK,h+1)  r(BLACK,h+1)
                //        /    \                          /     \
                //   c(RED,h)   lr(BLACK,h)           c(RED,h)   lr(BLACK,h)
                Self::new(Self::new(c, lr, BLACK), Self::make_root(r), RED)
            };
        }
        if a.height() > b.height() {
            // Do the reverse of the above procedure.
            let (l, r) = Self::detach(a);
            if r.black() {
                return Self::new(l, Self::merge_sub(r, b), BLACK);
            }

            let (rl, rr) = Self::detach(r);
            let c = Self::merge_sub(rr, b);
            if c.black() {
                return Self::new(l, Self::new(rl, c, RED), BLACK);
            }

            return if l.black() {
                Self::new(Self::new(l, rl, RED), c, BLACK)
            } else {
                Self::new(Self::make_root(l), Self::new(rl, c, BLACK), RED)
            };
        }

        // Connect directly:
        //         (RED,h)
        //         /     \
        //   a(BLACK,h)  b(BLACK,h)
        Self::new(a, b, RED)
    }

    fn split(p: Option<Self::Link>, k: usize) -> (Option<Self::Link>, Option<Self::Link>) {
        debug_assert!(k <= Self::len(&p));
        debug_assert!(Self::is_root(&p));
        if k == 0 {
            return (None, p);
        }
        if k == Self::len(&p) {
            return (p, None);
        }
        let (l, r) = Self::split_sub(p.unwrap(), k);
        (Some(Self::make_root(l)), Some(Self::make_root(r)))
    }
    fn split_range(
        p: Option<Self::Link>,
        l: usize,
        r: usize,
    ) -> (Option<Self::Link>, Option<Self::Link>, Option<Self::Link>) {
        debug_assert!(l <= r && r <= Self::len(&p));
        debug_assert!(Self::is_root(&p));
        let (p, c) = Self::split(p, r);
        let (a, b) = Self::split(p, l);
        (a, b, c)
    }

    /// 木 `p` を `[0, k), [k, n)` で分割する.
    ///
    /// # Required
    /// * `0 < k < n`
    ///
    /// # Ensured
    /// 返却される2つの木 `c = a, b` に対して以下が成立する.
    /// * `c.height ≦ p.height + 1`
    /// * `c.height == p.height + 1` となるのは, `p` が赤 かつ `c` が黒のときだけ
    ///
    /// # 計算量
    /// O(log n)
    /// ## 証明
    /// 再帰を降りながら木を O(log n) 個に分割する.
    /// 再帰の末端で 2つの木を持ち, 再帰を昇りながら先ほど分割してできた木をどちらかに merge していく.
    /// ここで # Ensured より `x` に `y` をマージする際, `x.height ≦ y.height + 1` が保証されている.
    /// `y.height` が昇順となるように処理は進み, その最大値は O(log n) である.
    /// merge(x, y) の計算量は O(|`x.height - y.height`|) であったことを踏まえると,
    /// split は全体で O(log n) になっている.
    fn split_sub(p: Self::Link, k: usize) -> (Self::Link, Self::Link) {
        debug_assert!(!p.is_leaf());
        debug_assert!(0 < k && k < p.size());
        let (l, r) = Self::detach(p);

        if k < l.size() {
            let (a, b) = Self::split_sub(l, k);
            return (a, Self::merge_sub(Self::make_root(b), Self::make_root(r)));

            // 左側の返り値の検証
            // (1) pが黒のとき
            // split_sub の性質より a.height ≦ l.height + 1 == p.height. OK
            // (2) pが赤のとき
            // l が黒なので, split_sub の性質より a.height ≦ l.height == p.height. OK

            // 右側の返り値の検証
            // (1) pが黒のとき
            // split_sub の性質より make_root(b.height) ≦ l.height + 1 == p.height
            // これと make_root(r).height ≦ p.height より,
            //     merge_sub(make_root(b), make_root(r)).height ≦ p.height. OK
            //
            // (2) pが赤のとき
            // l が黒なので, split_subの性質より b.height ≦ l.height == p.height
            //
            // (2.1) b が黒のとき
            // make_root(b).height == b.height ≦ p.height, make_root(r).height == p.height より
            //     merge_sub(make_root(b), make_root(r)).height ≦ p.height
            // (2.2) b が赤のとき
            // make_root(b).height == b.height + 1 ≦ p.height + 1
            // また, b の左右の子が黒となるので, merge_sub の実装を読むと
            // merge_sub(make_root(b), make_root(r)) は黒となることがわかる.
            //     merge_sub(make_root(b), make_root(r)).height ≦ p.height + 1 かつ
            //     merge_sub(make_root(b), make_root(r)) は黒. OK
        }
        if k > l.size() {
            let (a, b) = Self::split_sub(r, k - l.size());
            return (Self::merge_sub(Self::make_root(l), Self::make_root(a)), b);
        }

        // l.height ≦ p.height && r.height ≦ p.height より条件を満たす.
        (l, r)
    }

    fn insert(p: Option<Self::Link>, k: usize, val: Self::Value) -> Option<Self::Link> {
        debug_assert!(k <= Self::len(&p));
        debug_assert!(Self::is_root(&p));
        let (a, b) = Self::split(p, k);
        Self::merge(Self::merge(a, Some(Self::new_leaf(val))), b)
    }
    fn remove(p: Option<Self::Link>, k: usize) -> (Option<Self::Link>, Self::Value) {
        debug_assert!(k < Self::len(&p));
        debug_assert!(Self::is_root(&p));
        let (a, b, c) = Self::split_range(p, k, k + 1);
        (Self::merge(a, c), b.unwrap().val())
    }

    /// 配列 `v` を元に木を線形時間で構築する.
    fn build(v: &[Self::Value], l: usize, r: usize) -> Option<Self::Link> {
        debug_assert!(l <= r && r <= v.len());
        if l == r {
            return None;
        }
        if l + 1 == r {
            return Some(Self::new_leaf(v[l].clone()));
        }
        Self::merge(
            Self::build(v, l, (l + r) / 2),
            Self::build(v, (l + r) / 2, r),
        )
    }
    fn collect_vec(mut p: Self::Link, v: &mut Vec<Self::Value>) -> Self::Link {
        if !p.is_leaf() {
            let black = p.black();
            let (mut l, mut r) = Self::detach(p);
            l = Self::collect_vec(l, v);
            r = Self::collect_vec(r, v);
            p = Self::new(l, r, black);
        } else {
            v.push(p.val());
        }
        p
    }
}

pub struct Tree<T: Node> {
    root: Option<T::Link>,
}
impl<T: Node> Tree<T> {
    fn new(root: Option<T::Link>) -> Self {
        debug_assert!(T::is_root(&root));
        Self { root }
    }
    pub fn len(&mut self) -> usize {
        T::len(&self.root)
    }
    pub fn insert(&mut self, k: usize, val: T::Value) {
        debug_assert!(k <= self.len());
        self.root = T::insert(mem::replace(&mut self.root, None), k, val);
    }
    pub fn remove(&mut self, k: usize) -> T::Value {
        debug_assert!(k < self.len());
        let (root, val) = T::remove(mem::replace(&mut self.root, None), k);
        self.root = root;
        val
    }
    pub fn split(mut self, k: usize) -> (Self, Self) {
        debug_assert!(k <= self.len());
        let (l, r) = T::split(mem::replace(&mut self.root, None), k);
        (Self::new(l), Self::new(r))
    }
    pub fn split_range(mut self, l: usize, r: usize) -> (Self, Self, Self) {
        debug_assert!(l <= r && r <= self.len());
        let (a, b, c) = T::split_range(mem::replace(&mut self.root, None), l, r);
        (Self::new(a), Self::new(b), Self::new(c))
    }
    pub fn merge(&mut self, other: &mut Self) {
        self.root = T::merge(
            mem::replace(&mut self.root, None),
            mem::replace(&mut other.root, None),
        );
    }
    pub fn get(&mut self, k: usize) -> T::Value {
        debug_assert!(k < self.len());
        let val = self.remove(k);
        self.insert(k, val.clone());
        val
    }
    pub fn collect_vec(&mut self) -> Vec<T::Value> {
        if self.len() == 0 {
            return vec![];
        }
        let mut v = vec![];
        self.root = Some(T::collect_vec(
            mem::replace(&mut self.root, None).unwrap(),
            &mut v,
        ));
        v
    }
}

pub trait MonoidNode: Node<Value = <<Self as MonoidNode>::M as Monoid>::S> {
    type M: Monoid;
    fn min_left<G: Fn(<Self::M as Monoid>::S) -> bool>(
        p: <Self as Node>::Link,
        g: G,
        k: &mut usize,
        sm: <Self::M as Monoid>::S,
    ) -> <Self as Node>::Link {
        if p.is_leaf() {
            if g(<Self::M as Monoid>::binary_operation(&p.val(), &sm)) {
                *k -= 1;
            }
            return p;
        }

        let black = p.black();
        let (mut l, mut r) = <Self as Node>::detach(p);

        let nxt = <Self::M as Monoid>::binary_operation(&r.val(), &sm);
        if g(nxt.clone()) {
            *k -= r.size();
            l = Self::min_left(l, g, k, nxt);
        } else {
            r = Self::min_left(r, g, k, sm);
        }

        <Self as Node>::new(l, r, black)
    }

    fn max_right<G: Fn(<Self::M as Monoid>::S) -> bool>(
        p: <Self as Node>::Link,
        g: G,
        k: &mut usize,
        sm: <Self::M as Monoid>::S,
    ) -> <Self as Node>::Link {
        if p.is_leaf() {
            if g(<Self::M as Monoid>::binary_operation(&sm, &p.val())) {
                *k += 1;
            }
            return p;
        }

        let black = p.black();
        let (mut l, mut r) = <Self as Node>::detach(p);

        let nxt = <Self::M as Monoid>::binary_operation(&sm, &l.val());
        if g(nxt.clone()) {
            *k += l.size();
            r = Self::max_right(r, g, k, nxt);
        } else {
            l = Self::max_right(l, g, k, sm);
        }

        <Self as Node>::new(l, r, black)
    }
}

impl<T: MonoidNode> Tree<T> {
    /// 次を両方満たす l を返す.
    /// * g(prod(l, r)) = true
    /// * g(prod(l-1, r)) = false or l == 0
    ///
    /// # Required
    /// * g(identity()) = true
    /// * r <= n
    ///
    /// # 計算量
    /// O(log n)
    pub fn min_left<G: Fn(<T::M as Monoid>::S) -> bool>(&mut self, r: usize, g: G) -> usize {
        debug_assert!(g(<T::M as Monoid>::identity()));
        debug_assert!(r <= self.len());
        if r == 0 {
            return r;
        }
        let (mut a, b) = T::split(mem::replace(&mut self.root, None), r);

        let mut k = r;
        a = Some(T::min_left(
            a.unwrap(),
            g,
            &mut k,
            <T::M as Monoid>::identity(),
        ));
        self.root = T::merge(a, b);
        k
    }

    /// 次を両方満たす r を返す.
    /// * g(prod(l, r)) = true
    /// * g(prod(l, r+1)) = false or r == n
    ///
    /// # Required
    /// * g(identity()) = true
    /// * l <= n
    ///
    /// # 計算量
    /// O(log n)
    pub fn max_right<G: Fn(<T::M as Monoid>::S) -> bool>(&mut self, l: usize, g: G) -> usize {
        debug_assert!(g(<T::M as Monoid>::identity()));
        debug_assert!(l <= self.len());
        if l == self.len() {
            return l;
        }
        let (a, mut b) = T::split(mem::replace(&mut self.root, None), l);

        let mut k = l;
        b = Some(T::max_right(
            b.unwrap(),
            g,
            &mut k,
            <T::M as Monoid>::identity(),
        ));
        self.root = T::merge(a, b);
        k
    }

    pub fn prod(&mut self, l: usize, r: usize) -> <T::M as Monoid>::S {
        debug_assert!(l <= r && r <= self.len());
        if l == r {
            return <T::M as Monoid>::identity();
        }

        let (a, b, c) = T::split_range(mem::replace(&mut self.root, None), l, r);

        let val = b.as_ref().unwrap().val();

        self.root = T::merge(T::merge(a, b), c);
        val
    }
}

pub trait MapMonoidNode:
    Node<Value = <<<Self as MapMonoidNode>::F as MapMonoid>::M as Monoid>::S>
{
    type F: MapMonoid;
    fn apply(p: <Self as Node>::Link, f: <Self::F as MapMonoid>::F) -> <Self as Node>::Link;
}

impl<T: MapMonoidNode> Tree<T> {
    pub fn apply_range(&mut self, l: usize, r: usize, f: <T::F as MapMonoid>::F) {
        debug_assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }
        let (a, mut b, c) = T::split_range(mem::replace(&mut self.root, None), l, r);

        b = Some(T::apply(b.unwrap(), f));

        self.root = T::merge(T::merge(a, b), c);
    }
}

pub trait ReversibleNode: Node {
    fn reverse(p: <Self as Node>::Link) -> <Self as Node>::Link;
}

impl<T: ReversibleNode> Tree<T> {
    pub fn reverse_range(&mut self, l: usize, r: usize) {
        debug_assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }
        let (a, mut b, c) = T::split_range(mem::replace(&mut self.root, None), l, r);

        b = Some(T::reverse(b.unwrap()));

        self.root = T::merge(T::merge(a, b), c);
    }
}

impl<T: Node, L> Clone for Tree<T>
where
    T: Node<Link = L>,
    L: Deref<Target = T> + Clone,
{
    fn clone(&self) -> Self {
        Self::new(self.root.clone())
    }
}

impl<T, U> From<Vec<U>> for Tree<T>
where
    T: Node<Value = U>,
    U: Clone,
{
    fn from(v: Vec<U>) -> Self {
        Self::new(T::build(&v, 0, v.len()))
    }
}

impl<T: Node> Default for Tree<T> {
    fn default() -> Self {
        Self::new(None)
    }
}
