use std::rc::Rc;
use std::mem::replace;

use crate::algebra::{MapMonoid, Monoid};

const RED: bool = false;
const BLACK: bool = true;

pub struct RedBlackNode<F: MapMonoid> {
    l: Option<Rc<Self>>,
    r: Option<Rc<Self>>,
    black: bool,
    height: usize,
    size: usize,
    val: <F::M as Monoid>::S,
    lazy: F::F,
    rev: bool,
}
impl<F: MapMonoid> RedBlackNode<F> {
    fn new(l: Rc<Self>, r: Rc<Self>, black: bool) -> Rc<Self> {
        Rc::new(Self {
            black,
            height: l.height + black as usize,
            size: l.size + r.size,
            val: F::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            rev: false,
            l: Some(l),
            r: Some(r),
        })
    }
    fn new_leaf(val: <F::M as Monoid>::S) -> Rc<Self> {
        Rc::new(Self {
            black: true,
            height: 1,
            size: 1,
            val,
            lazy: F::identity_map(),
            rev: false,
            l: None,
            r: None,
        })
    }
    fn detach(p: Rc<Self>) -> (Rc<Self>, Rc<Self>) {
        let (mut l, mut r) = (p.l.clone().unwrap(), p.r.clone().unwrap());
        Rc::make_mut(&mut l).val = F::mapping(&p.lazy, &l.val);
        Rc::make_mut(&mut r).val = F::mapping(&p.lazy, &r.val);
        Rc::make_mut(&mut l).lazy = F::composition(&p.lazy, &l.lazy);
        Rc::make_mut(&mut r).lazy = F::composition(&p.lazy, &r.lazy);
        if p.rev {
            Rc::make_mut(&mut l).rev ^= true;
            Rc::make_mut(&mut r).rev ^= true;
            return (r, l);
        }
        (l, r)
    }
    fn make_root(mut p: Rc<Self>) -> Rc<Self> {
        if !p.black {
            Rc::make_mut(&mut p).black = true;
            Rc::make_mut(&mut p).height += 1;
        }
        p
    }
    fn val(&self) -> <F::M as Monoid>::S {
        self.val.clone()
    }

    /// 木 a, b を併合する
    ///
    /// # Required
    /// a, b はそれぞれ空でなく, 根が黒である.
    ///
    /// # Ensured
    /// 併合後の木を c とすると,
    ///     c.height == max(a.height, b.height)
    /// が成立する. ただし c の根が黒であるとは限らない.
    ///
    /// # 計算量
    /// O(|a.height - b.height|)
    pub fn merge_sub(a: Rc<Self>, b: Rc<Self>) -> Rc<Self> {
        debug_assert!(a.black);
        debug_assert!(b.black);
        if a.height < b.height {
            let (l, r) = Self::detach(b);
            //      b(BLACK,h+1)
            //       /     \
            //   l(*,h)    r(*,h)

            if l.black {
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
            if c.black {
                // Connect directly:
                //             (BLACK,h+1)
                //             /    \
                //         (RED,h)   r(BLACK,h)
                //         /    \
                //   c(BLACK,h)  lr(BLACK,h)
                return Self::new(Self::new(c, lr, RED), r, BLACK);
            }

            return if r.black {
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
        if a.height > b.height {
            // Do the reverse of the above procedure.
            let (l, r) = Self::detach(a);
            if r.black {
                return Self::new(l, Self::merge_sub(r, b), BLACK);
            }

            let (rl, rr) = Self::detach(r);
            let c = Self::merge_sub(rr, b);
            if c.black {
                return Self::new(l, Self::new(rl, c, RED), BLACK);
            }

            return if l.black {
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

    /// 葉を n 個持つ木 p を [0, k), [k, n) で分割する.
    ///
    /// # Required
    /// * 0 < k < n
    ///
    /// # Ensured
    /// 返却される2つの木 c = a, b に対して以下が成立する.
    ///   c.height ≦ p.height + 1
    ///   c.height == p.height + 1 となるのは, p の根が赤 かつ c の根が黒のときだけ
    ///
    /// # 計算量
    /// O(log n)
    ///
    /// ## 証明
    /// 再帰を降りながら木を O(log n) 個に分割する.
    /// 再帰の末端で 2つの木を持ち, 再帰を昇りながら先ほど分割してできた木をどちらかに merge_sub していく.
    /// ここで # Ensured より x に y をマージする際, x.height ≦ y.height + 1 が保証されている.
    /// y.height が昇順となるように処理は進み, その最大値は O(log n) である.
    /// merge_sub(x, y) の計算量は O(|x.height - y.height|) であったことを踏まえると,
    /// split_sub は全体で O(log n) になっている.
    pub fn split_sub(p: Rc<Self>, k: usize) -> (Rc<Self>, Rc<Self>) {
        debug_assert!(0 < k && k < p.size);
        let (l, r) = Self::detach(p);

        if k < l.size {
            let (a, b) = Self::split_sub(l, k);
            return (a, Self::merge_sub(Self::make_root(b), Self::make_root(r)));

            // 左側の返り値の検証
            // (1) p の根が黒のとき
            // split_sub の性質より
            //     a.height ≦ l.height + 1 == p.height. OK
            // (2) p の根が赤のとき
            // l の根が黒なので, split_sub の性質より
            //     a.height ≦ l.height == p.height. OK
            //
            // 右側の返り値の検証
            // (1) p の根が黒のとき
            // split_sub の性質より make_root(b.height) ≦ l.height + 1 == p.height
            // これと make_root(r).height ≦ p.height より,
            //     merge_sub(make_root(b), make_root(r)).height ≦ p.height. OK
            //
            // (2) p の根が赤のとき
            // l の根が黒なので, split_subの性質より b.height ≦ l.height == p.height
            //
            // (2.1) make_root(b).height ≦ p.height のとき
            // make_root(r).height == p.height と合わせて
            //     merge_sub(make_root(b), make_root(r)).height ≦ p.height. OK
            //
            // (2.2) make_root(b).height == p.height + 1 のとき
            // make_root(r).height == p.height < make_root(b).height
            // これと b の左右の子が黒となることから, merge_sub の実装を読むと
            // merge_sub(make_root(b), make_root(r)) の根は黒となることがわかる.
            //     merge_sub(make_root(b), make_root(r)).height == p.height + 1 かつ
            //     merge_sub(make_root(b), make_root(r)) の根は黒. OK
        }
        if k > l.size {
            let (a, b) = Self::split_sub(r, k - l.size);
            return (Self::merge_sub(Self::make_root(l), Self::make_root(a)), b);
        }

        // l.height ≦ p.height && r.height ≦ p.height. OK
        (l, r)
    }

    fn len(p: &Option<Rc<Self>>) -> usize {
        p.as_ref().map_or(0, |p| p.size)
    }

    fn merge(a: Option<Rc<Self>>, b: Option<Rc<Self>>) -> Option<Rc<Self>> {
        if a.is_none() {
            return b;
        }
        if b.is_none() {
            return a;
        }
        Some(Self::make_root(Self::merge_sub(a.unwrap(), b.unwrap())))
    }
    fn merge3(
        a: Option<Rc<Self>>,
        b: Option<Rc<Self>>,
        c: Option<Rc<Self>>,
    ) -> Option<Rc<Self>> {
        Self::merge(Self::merge(a, b), c)
    }
    fn split(p: Option<Rc<Self>>, k: usize) -> (Option<Rc<Self>>, Option<Rc<Self>>) {
        debug_assert!(k <= Self::len(&p));
        if k == 0 {
            return (None, p);
        }
        if k == Self::len(&p) {
            return (p, None);
        }
        let (l, r) = Self::split_sub(p.unwrap(), k);
        (Some(Self::make_root(l)), Some(Self::make_root(r)))
    }
    fn split3(
        p: Option<Rc<Self>>,
        l: usize,
        r: usize,
    ) -> (Option<Rc<Self>>, Option<Rc<Self>>, Option<Rc<Self>>) {
        debug_assert!(l <= r && r <= Self::len(&p));
        let (p, c) = Self::split(p, r);
        let (a, b) = Self::split(p, l);
        (a, b, c)
    }

    fn insert(p: Option<Rc<Self>>, k: usize, val: <F::M as Monoid>::S) -> Option<Rc<Self>> {
        debug_assert!(k <= Self::len(&p));
        let (a, b) = Self::split(p, k);
        Self::merge3(a, Some(Self::new_leaf(val)), b)
    }
    fn remove(p: Option<Rc<Self>>, k: usize) -> (Option<Rc<Self>>, <F::M as Monoid>::S) {
        debug_assert!(k < Self::len(&p));
        let (a, b, c) = Self::split3(p, k, k + 1);
        (Self::merge(a, c), b.unwrap().val())
    }

    /// 配列 v[l, r) を元に木を線形時間で構築する.
    ///
    /// # Required
    /// l ≦ r ≦ v.len()
    ///
    /// # Ensured
    /// 返却される木の根は黒.
    fn build(v: &[<F::M as Monoid>::S], l: usize, r: usize) -> Option<Rc<Self>> {
        debug_assert!(l <= r && r <= v.len());
        if l == r {
            return None
        }
        if l + 1 == r {
            return Some(Self::new_leaf(v[l].clone()));
        }
        Self::merge(
            Self::build(v, l, (l + r) / 2),
            Self::build(v, (l + r) / 2, r),
        )
    }

    fn is_leaf(&self) -> bool {
        self.black && self.height == 1
    }

    /// 木 p の葉が持つ値を格納した配列 v を線形時間で構築する.
    fn collect(mut p: Rc<Self>, v: &mut Vec<<F::M as Monoid>::S>) -> Rc<Self> {
        if !p.is_leaf() {
            let black = p.black;
            let (mut l, mut r) = Self::detach(p);
            l = Self::collect(l, v);
            r = Self::collect(r, v);
            p = Self::new(l, r, black);
        } else {
            v.push(p.val());
        }
        p
    }

    fn min_left<G: Fn(&<F::M as Monoid>::S) -> bool>(
        p: Rc<Self>,
        g: G,
        k: &mut usize,
        sm: <F::M as Monoid>::S,
    ) -> Rc<Self> {
        if p.is_leaf() {
            if g(&F::binary_operation(&p.val(), &sm)) {
                *k -= 1;
            }
            return p;
        }

        let black = p.black;
        let (mut l, mut r) = Self::detach(p);

        let nxt = F::binary_operation(&r.val(), &sm);
        if g(&nxt) {
            *k -= r.size;
            l = Self::min_left(l, g, k, nxt);
        } else {
            r = Self::min_left(r, g, k, sm);
        }

        Self::new(l, r, black)
    }

    fn max_right<G: Fn(&<F::M as Monoid>::S) -> bool>(
        p: Rc<Self>,
        g: G,
        k: &mut usize,
        sm: <F::M as Monoid>::S,
    ) -> Rc<Self> {
        if p.is_leaf() {
            if g(&F::binary_operation(&sm, &p.val())) {
                *k += 1;
            }
            return p;
        }

        let black = p.black;
        let (mut l, mut r) = Self::detach(p);

        let nxt = F::binary_operation(&sm, &l.val());
        if g(&nxt) {
            *k += l.size;
            r = Self::max_right(r, g, k, nxt);
        } else {
            l = Self::max_right(l, g, k, sm);
        }

        Self::new(l, r, black)
    }

    fn apply(mut p: Rc<Self>, f: F::F) -> Rc<Self> {
        Rc::make_mut(&mut p).val = F::mapping(&f, &p.val);
        Rc::make_mut(&mut p).lazy = F::composition(&f, &p.lazy);
        p
    }

    fn reverse(mut p: Rc<Self>) -> Rc<Self> {
        Rc::make_mut(&mut p).rev ^= true;
        p
    }
}
impl<F: MapMonoid> Clone for RedBlackNode<F> {
    fn clone(&self) -> Self {
        Self {
            l: self.l.clone(),
            r: self.r.clone(),
            black: self.black.clone(),
            height: self.height.clone(),
            size: self.size.clone(),
            val: self.val.clone(),
            lazy: self.lazy.clone(),
            rev: self.rev.clone(),
        }
    }
}

pub struct RedBlackTree<F: MapMonoid> {
    root: Option<Rc<RedBlackNode<F>>>,
}
impl<F: MapMonoid> RedBlackTree<F> {
    fn new(root: Option<Rc<RedBlackNode<F>>>) -> Self {
        Self { root }
    }
    pub fn len(&mut self) -> usize {
        self.root.as_ref().map_or(0, |p| p.size)
    }
    pub fn merge(&mut self, other: &mut Self) {
        self.root = RedBlackNode::<F>::merge(
            replace(&mut self.root, None),
            replace(&mut other.root, None),
        );
    }
    pub fn merge3(&mut self, b: &mut Self, c: &mut Self) {
        self.root = RedBlackNode::<F>::merge3(
            replace(&mut self.root, None),
            replace(&mut b.root, None),
            replace(&mut c.root, None),
        );
    }
    pub fn split(mut self, k: usize) -> (Self, Self) {
        debug_assert!(k <= self.len());
        let (l, r) = RedBlackNode::<F>::split(replace(&mut self.root, None), k);
        (Self::new(l), Self::new(r))
    }
    pub fn split3(mut self, l: usize, r: usize) -> (Self, Self, Self) {
        debug_assert!(l <= r && r <= self.len());
        let (a, b, c) = RedBlackNode::<F>::split3(replace(&mut self.root, None), l, r);
        (Self::new(a), Self::new(b), Self::new(c))
    }

    pub fn insert(&mut self, k: usize, val: <F::M as Monoid>::S) {
        debug_assert!(k <= self.len());
        self.root = RedBlackNode::<F>::insert(replace(&mut self.root, None), k, val);
    }
    pub fn remove(&mut self, k: usize) -> <F::M as Monoid>::S {
        debug_assert!(k < self.len());
        let (root, val) = RedBlackNode::<F>::remove(replace(&mut self.root, None), k);
        self.root = root;
        val
    }
    pub fn get(&mut self, k: usize) -> <F::M as Monoid>::S {
        debug_assert!(k < self.len());
        let val = self.remove(k);
        self.insert(k, val.clone());
        val
    }
    pub fn collect(&mut self) -> Vec<<F::M as Monoid>::S> {
        if self.len() == 0 {
            return vec![];
        }
        let mut v = vec![];
        self.root = Some(RedBlackNode::<F>::collect(
            replace(&mut self.root, None).unwrap(),
            &mut v,
        ));
        v
    }

    /// 次を両方満たす l を返す.
    /// * g(prod(l, r)) = true
    /// * g(prod(l-1, r)) = false or l == 0
    ///
    /// # Required
    /// * g(identity()) = true
    /// * r ≦ n
    ///
    /// # 計算量
    /// O(log n)
    pub fn min_left<G: Fn(&<F::M as Monoid>::S) -> bool>(&mut self, r: usize, g: G) -> usize {
        debug_assert!(g(&<F::M as Monoid>::identity()));
        debug_assert!(r <= self.len());
        if r == 0 {
            return r;
        }
        let (mut a, b) = RedBlackNode::<F>::split(replace(&mut self.root, None), r);

        let mut k = r;
        a = Some(RedBlackNode::<F>::min_left(
            a.unwrap(),
            g,
            &mut k,
            <F::M as Monoid>::identity(),
        ));
        self.root = RedBlackNode::<F>::merge(a, b);
        k
    }

    /// 次を両方満たす r を返す.
    /// * g(prod(l, r)) = true
    /// * g(prod(l, r+1)) = false or r == n
    ///
    /// # Required
    /// * g(identity()) = true
    /// * l ≦ n
    ///
    /// # 計算量
    /// O(log n)
    pub fn max_right<G: Fn(&<F::M as Monoid>::S) -> bool>(&mut self, l: usize, g: G) -> usize {
        debug_assert!(g(&<F::M as Monoid>::identity()));
        debug_assert!(l <= self.len());
        if l == self.len() {
            return l;
        }
        let (a, mut b) = RedBlackNode::<F>::split(replace(&mut self.root, None), l);

        let mut k = l;
        b = Some(RedBlackNode::<F>::max_right(
            b.unwrap(),
            g,
            &mut k,
            <F::M as Monoid>::identity(),
        ));
        self.root = RedBlackNode::<F>::merge(a, b);
        k
    }

    pub fn prod(&mut self, l: usize, r: usize) -> <F::M as Monoid>::S {
        debug_assert!(l <= r && r <= self.len());
        if l == r {
            return <F::M as Monoid>::identity();
        }

        let (a, b, c) = RedBlackNode::<F>::split3(replace(&mut self.root, None), l, r);

        let val = b.as_ref().unwrap().val();

        self.root = RedBlackNode::<F>::merge3(a, b, c);
        val
    }

    pub fn apply_range(&mut self, l: usize, r: usize, f: F::F) {
        debug_assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }
        let (a, mut b, c) = RedBlackNode::<F>::split3(replace(&mut self.root, None), l, r);

        b = Some(RedBlackNode::<F>::apply(b.unwrap(), f));

        self.root = RedBlackNode::<F>::merge3(a, b, c);
    }

    pub fn reverse_range(&mut self, l: usize, r: usize) {
        debug_assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }
        let (a, mut b, c) = RedBlackNode::<F>::split3(replace(&mut self.root, None), l, r);

        b = Some(RedBlackNode::<F>::reverse(b.unwrap()));

        self.root = RedBlackNode::<F>::merge3(a, b, c);
    }
}
impl<F: MapMonoid> Clone for RedBlackTree<F> {
    fn clone(&self) -> Self {
        Self::new(self.root.clone())
    }
}
impl<F: MapMonoid> From<Vec<<F::M as Monoid>::S>> for RedBlackTree<F> {
    fn from(v: Vec<<F::M as Monoid>::S>) -> Self {
        Self::new(RedBlackNode::<F>::build(&v, 0, v.len()))
    }
}
