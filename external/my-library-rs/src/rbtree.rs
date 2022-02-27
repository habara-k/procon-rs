const RED: bool = false;
const BLACK: bool = true;

struct Base {
    black: bool,
    height: usize,
    size: usize,
}
impl Base {
    fn new(l: &Self, r: &Self, black: bool) -> Self {
        assert_eq!(l.height, r.height);
        assert!(l.black || black);
        assert!(r.black || black);
        Self {
            black,
            height: l.height + black as usize,
            size: l.size + r.size,
        }
    }
    fn new_leaf() -> Self {
        Self {
            black: true,
            height: 1,
            size: 1,
        }
    }
    fn is_leaf(&self) -> bool {
        self.black && self.height == 1
    }
    fn into_root(mut self) -> Self {
        if !self.black {
            self.black = true;
            self.height += 1;
        }
        self
    }
}

pub trait Node {
    type Item: Clone;
    fn new(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self>;
    fn new_leaf(val: Self::Item) -> Box<Self>;
    fn detach(self: Box<Self>) -> (Box<Self>, Box<Self>);
    fn into_root(self: Box<Self>) -> Box<Self>;
    fn black(&self) -> bool;
    fn height(&self) -> usize;
    fn size(&self) -> usize;
    fn val(&self) -> Self::Item;

    fn len(p: &Option<Box<Self>>) -> usize {
        if let Some(p) = p {
            return p.size();
        }
        0
    }
    fn merge(a: Option<Box<Self>>, b: Option<Box<Self>>) -> Option<Box<Self>> {
        if a.is_none() {
            return b;
        }
        if b.is_none() {
            return a;
        }
        let (a, b) = (a.unwrap(), b.unwrap());
        assert!(a.black() && b.black());
        Some(Self::merge_sub(a, b).into_root())
    }
    fn merge_sub(a: Box<Self>, b: Box<Self>) -> Box<Self> {
        // # Require
        //     a.black == true, b.black == true
        // # Ensure
        //     return.height == max(a.height, b.height)
        //     [WARNING] return.black may be false!
        assert!(a.black());
        assert!(b.black());

        if a.height() < b.height() {
            let (l, r) = b.detach();
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

            let (ll, lr) = l.detach();
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
                Self::new(Self::new(c, lr, BLACK), r.into_root(), RED)
            };
        }
        if a.height() > b.height() {
            // Do the reverse of the above procedure.
            let (l, r) = a.detach();
            if r.black() {
                return Self::new(l, Self::merge_sub(r, b), BLACK);
            }

            let (rl, rr) = r.detach();
            let c = Self::merge_sub(rr, b);
            if c.black() {
                return Self::new(l, Self::new(rl, c, RED), BLACK);
            }

            return if l.black() {
                Self::new(Self::new(l, rl, RED), c, BLACK)
            } else {
                Self::new(l.into_root(), Self::new(rl, c, BLACK), RED)
            };
        }

        // Connect directly:
        //         (RED,h)
        //         /     \
        //   a(BLACK,h)  b(BLACK,h)
        Self::new(a, b, RED)
    }
    fn split_range(
        p: Option<Box<Self>>,
        l: usize,
        r: usize,
    ) -> (Option<Box<Self>>, Option<Box<Self>>, Option<Box<Self>>) {
        assert!(l <= r && r <= Self::len(&p));
        let (p, c) = Self::split(p, r);
        let (a, b) = Self::split(p, l);
        (a, b, c)
    }
    fn split(p: Option<Box<Self>>, k: usize) -> (Option<Box<Self>>, Option<Box<Self>>) {
        assert!(k <= Self::len(&p));
        if k == 0 {
            return (None, p);
        }
        if k == Self::len(&p) {
            return (p, None);
        }
        let (l, r) = p.unwrap().detach();
        if k < l.size() {
            let (a, b) = Self::split(Some(l), k);
            return (a, Self::merge(b, Some(r.into_root())));
        }
        if k > l.size() {
            let (a, b) = Self::split(Some(r), k - l.size());
            return (Self::merge(Some(l.into_root()), a), b);
        }
        (Some(l.into_root()), Some(r.into_root()))
    }
    fn insert(p: Option<Box<Self>>, k: usize, val: Self::Item) -> Option<Box<Self>> {
        assert!(k <= Self::len(&p));
        let (a, b) = Self::split(p, k);
        Self::merge(Self::merge(a, Some(Self::new_leaf(val))), b)
    }
    fn remove(p: Option<Box<Self>>, k: usize) -> (Option<Box<Self>>, Self::Item) {
        assert!(k < Self::len(&p));
        let (a, b, c) = Self::split_range(p, k, k + 1);
        (Self::merge(a, c), b.unwrap().val())
    }
    fn build(v: &[Self::Item], l: usize, r: usize) -> Option<Box<Self>> {
        assert!(l <= r && r <= v.len());
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
}

pub trait Root {
    type Node: Node;
    fn root(&self) -> &Option<Box<Self::Node>>;
    fn mut_root(&mut self) -> &mut Option<Box<Self::Node>>;
    fn new(root: Option<Box<Self::Node>>) -> Self;
}

use std::mem;
pub trait Tree: Root {
    /// 要素数を返す.
    fn len(&self) -> usize {
        Self::Node::len(self.root())
    }
    /// `k` 番目に `val` を挿入する.
    fn insert(&mut self, k: usize, val: <Self::Node as Node>::Item) {
        assert!(k <= self.len());
        let root = mem::replace(self.mut_root(), None);
        *self.mut_root() = Self::Node::insert(root, k, val);
    }
    /// `k` 番目の要素を削除し, その値を返す.
    fn remove(&mut self, k: usize) -> <Self::Node as Node>::Item {
        assert!(k < self.len());
        let root = mem::replace(self.mut_root(), None);
        let (root, val) = Self::Node::remove(root, k);
        *self.mut_root() = root;
        val
    }
    /// [0,n) => [0,k), [k,n)
    fn split(&mut self, k: usize, other: &mut Self) {
        let root = mem::replace(self.mut_root(), None);
        let (l, r) = Self::Node::split(root, k);
        *self.mut_root() = l;
        *other.mut_root() = r;
    }
    /// [0,k), [k,n) => [0,n)
    fn merge(&mut self, other: &mut Self) {
        let root = mem::replace(self.mut_root(), None);
        *self.mut_root() = Self::Node::merge(root, mem::replace(other.mut_root(), None));
    }
    /// `k` 番目の要素を返す.
    fn get(&mut self, k: usize) -> <Self::Node as Node>::Item {
        assert!(k < self.len());
        let val = self.remove(k);
        self.insert(k, val.clone());
        val
    }
}

pub use crate::algebra::Monoid;
pub trait RangeFold<M: Monoid, T: Node<Item = M::S>>: Tree<Node = T>
{
    fn prod(&mut self, l: usize, r: usize) -> M::S {
        assert!(l <= r && r <= self.len());
        if l == r {
            return M::identity();
        }

        let root = mem::replace(self.mut_root(), None);
        let (a, b, c) = Self::Node::split_range(root, l, r);

        let val = b.as_ref().unwrap().val();

        *self.mut_root() = Self::Node::merge(Self::Node::merge(a, b), c);
        val
    }
}

pub use crate::algebra::MapMonoid;
pub trait Appliable<F: MapMonoid>: Node<Item = <F::M as Monoid>::S> {
    fn apply(self: Box<Self>, f: F::F) -> Box<Self>;
}

pub trait LazyEval<F: MapMonoid, T: Appliable<F>>: Tree<Node = T> {
    fn apply_range(&mut self, l: usize, r: usize, f: F::F) {
        assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }
        let root = mem::replace(self.mut_root(), None);
        let (a, mut b, c) = Self::Node::split_range(root, l, r);

        b = Some(b.unwrap().apply(f));

        *self.mut_root() = Self::Node::merge(Self::Node::merge(a, b), c);
    }
}

pub trait Reversible: Node {
    fn reverse(self: Box<Self>) -> Box<Self>;
}
pub trait Reverse<T: Reversible>: Tree<Node = T> {
    fn reverse_range(&mut self, l: usize, r: usize) {
        assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }
        let root = mem::replace(self.mut_root(), None);
        let (a, mut b, c) = Self::Node::split_range(root, l, r);

        b = Some(b.unwrap().reverse());

        *self.mut_root() = Self::Node::merge(Self::Node::merge(a, b), c);
    }
}

macro_rules! impl_node {
    ($node:ident<$param:ident : $bound:tt>, $val:ty) => {
        impl<$param: $bound> Node for $node<$param> {
            type Item = $val;
            fn new(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self> {
                Self::new(l, r, black)
            }
            fn new_leaf(val: Self::Item) -> Box<Self> {
                Self::new_leaf(val)
            }
            fn detach(self: Box<Self>) -> (Box<Self>, Box<Self>) {
                self.detach()
            }
            fn into_root(mut self: Box<Self>) -> Box<Self> {
                self.base = self.base.into_root();
                self
            }
            fn black(&self) -> bool {
                self.base.black
            }
            fn height(&self) -> usize {
                self.base.height
            }
            fn size(&self) -> usize {
                self.base.size
            }
            fn val(&self) -> Self::Item {
                self.val.clone()
            }
        }
    };
}

macro_rules! impl_tree {
    ($tree:ident<$param:ident : $bound:tt>, $node:ty) => {
        impl<$param: $bound> Root for $tree<$param> {
            type Node = $node;
            fn root(&self) -> &Option<Box<Self::Node>> {
                &self.root
            }
            fn mut_root(&mut self) -> &mut Option<Box<Self::Node>> {
                &mut self.root
            }
            fn new(root: Option<Box<Self::Node>>) -> Self {
                Self { root }
            }
        }
        impl<$param: $bound> Tree for $tree<$param> {}
        impl<$param: $bound> From<Vec<<$node as Node>::Item>> for $tree<$param> {
            fn from(v: Vec<<$node as Node>::Item>) -> Self {
                Self {
                    root: <Self as Root>::Node::build(&v, 0, v.len()),
                }
            }
        }
        impl<$param: $bound> Default for $tree<$param> {
            fn default() -> Self {
                Self { root: None }
            }
        }
    };
}

/// 列を管理する平衡二分木.
/// 挿入, 削除, 取得, 分割, 統合, lower_bound を O(log n) で行う.
///
/// # Example
/// ```
/// use my_library_rs::*;
///
/// let mut v: RBTree<u32> = vec![60, 30, 30, 40].into();
/// v.insert(0, 10);  // [10, 60, 30, 30, 40]
/// v.remove(1);      // [10, 30, 30, 40]
///
/// assert_eq!(v.len(), 4);
/// assert_eq!((v.get(0), v.get(1), v.get(2), v.get(3)), (10, 30, 30, 40));
/// assert_eq!((v.lower_bound(25), v.lower_bound(30), v.lower_bound(35)), (1, 1, 3));
///
/// let mut t: RBTree<u32> = Default::default();
/// v.split(2, &mut t);  // [10, 30], [30, 40];
/// assert_eq!(v.len(), 2);
/// assert_eq!((v.get(0), v.get(1)), (10, 30));
/// assert_eq!(t.len(), 2);
/// assert_eq!((t.get(0), t.get(1)), (30, 40));
///
/// t.merge(&mut v);  // [30, 40, 10, 20];
/// assert_eq!(t.len(), 4);
/// assert_eq!((t.get(0), t.get(1), t.get(2), t.get(3)), (30, 40, 10, 30));
/// assert_eq!(v.len(), 0);
/// ```
pub struct RBTree<T> {
    root: Option<Box<RBNode<T>>>,
}
impl_tree!(RBTree<T: Clone>, RBNode<T>);
impl<T: Clone + Ord> RBTree<T> {
    pub fn lower_bound(&self, val: T) -> usize {
        if self.root().is_none() {
            return 0;
        }

        let mut p = self.root().as_ref().unwrap();
        let mut k = 0;

        while let (Some(l), Some(r)) = (&p.l, &p.r) {
            if l.val < val {
                p = r;
                k += l.size();
            } else {
                p = l;
            }
        }

        k + (p.val < val) as usize
    }
}

pub struct RBNode<T> {
    val: T,
    base: Base,
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
}
impl<T: Clone> RBNode<T> {
    fn new(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self> {
        Box::new(Self {
            val: r.val.clone(),
            base: Base::new(&l.base, &r.base, black),
            l: Some(l),
            r: Some(r),
        })
    }
    fn new_leaf(val: T) -> Box<Self> {
        Box::new(Self {
            val,
            base: Base::new_leaf(),
            l: None,
            r: None,
        })
    }
    fn detach(self: Box<Self>) -> (Box<Self>, Box<Self>) {
        assert!(!self.base.is_leaf());
        (self.l.unwrap(), self.r.unwrap())
    }
}
impl_node!(RBNode<T: Clone>, T);

/// モノイドが載る平衡二分木.
/// 挿入, 削除, 区間取得, 分割, 統合を O(log n) で行う.
///
/// # Example
/// ```
/// use my_library_rs::*;
///
/// pub struct RangeSum;
/// impl Monoid for RangeSum {
///     type S = u32;
///     fn identity() -> Self::S { 0 }
///     fn binary_operation(a: &Self::S, b: &Self::S) -> Self::S { *a + *b }
/// }
///
/// let mut seg: RBSegtree<RangeSum> = vec![1, 100, 0, 1000].into();
/// assert_eq!(seg.remove(2), 0);  // [1, 100, 1000]
/// seg.insert(1, 10);  // [1, 10, 100, 1000]
///
/// assert_eq!((seg.prod(0, 4), seg.prod(0, 3), seg.prod(1, 2)), (1111, 111, 10));
/// ```
pub struct RBSegtree<M: Monoid> {
    root: Option<Box<MonoidRBNode<M>>>,
}
impl_tree!(RBSegtree<M: Monoid>, MonoidRBNode<M>);
impl<M: Monoid> RangeFold<M, MonoidRBNode<M>> for RBSegtree<M> {}

pub struct MonoidRBNode<M: Monoid> {
    val: M::S,
    base: Base,
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
}
impl<M: Monoid> MonoidRBNode<M> {
    fn new(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self> {
        Box::new(Self {
            val: M::binary_operation(&l.val, &r.val),
            base: Base::new(&l.base, &r.base, black),
            l: Some(l),
            r: Some(r),
        })
    }
    fn new_leaf(val: M::S) -> Box<Self> {
        Box::new(Self {
            val,
            base: Base::new_leaf(),
            l: None,
            r: None,
        })
    }
    fn detach(self: Box<Self>) -> (Box<Self>, Box<Self>) {
        (self.l.unwrap(), self.r.unwrap())
    }
}
impl_node!(MonoidRBNode<M: Monoid>, M::S);

/// 作用素モノイドが載る平衡二分木.
/// 挿入, 削除, 区間取得, 区間作用, 分割, 統合 を O(log n) で行う.
///
/// # Example
/// ```
/// use my_library_rs::*;
/// use std::cmp::min;
///
/// pub struct RangeMin;
/// impl Monoid for RangeMin
/// {
///     type S = u32;
///     fn identity() -> Self::S { Self::S::max_value() }
///     fn binary_operation(&a: &Self::S, &b: &Self::S) -> Self::S { min(a, b) }
/// }
/// struct RangeAddRangeMin;
/// impl MapMonoid for RangeAddRangeMin {
///     type M = RangeMin;
///     type F = u32;
///
///     fn identity_map() -> Self::F { 0 }
///     fn mapping(&f: &Self::F, &a: &<Self::M as Monoid>::S) -> <Self::M as Monoid>::S { a + f }
///     fn composition(&f: &Self::F, &g: &Self::F) -> Self::F { f + g }
/// }
///
/// let mut seg: RBLazySegtree<RangeAddRangeMin> = vec![1, 100, 0, 1000].into();
/// assert_eq!(seg.remove(2), 0);  // [1, 100, 1000]
/// seg.insert(1, 10);  // [1, 10, 100, 1000]
///
/// assert_eq!((seg.prod(0, 4), seg.prod(0, 3), seg.prod(1, 2)), (1, 1, 10));
///
/// seg.apply_range(2, 4, 20);  // [1, 10, 120, 1020]
/// seg.apply_range(0, 3, 3000);   // [3001, 3010, 3120, 1020]
/// assert_eq!((seg.get(0), seg.get(1), seg.get(2), seg.get(3)), (3001, 3010, 3120, 1020));
/// ```
pub struct RBLazySegtree<F: MapMonoid> {
    root: Option<Box<MapMonoidRBNode<F>>>,
}
impl_tree!(
    RBLazySegtree<F: MapMonoid>,
    MapMonoidRBNode<F>
);
impl<F: MapMonoid> RangeFold<F::M, MapMonoidRBNode<F>> for RBLazySegtree<F> {}
impl<F: MapMonoid> LazyEval<F, MapMonoidRBNode<F>> for RBLazySegtree<F> {}

pub struct MapMonoidRBNode<F: MapMonoid> {
    val: <F::M as Monoid>::S,
    base: Base,
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
    lazy: F::F,
}
impl<F: MapMonoid> MapMonoidRBNode<F> {
    fn new(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self> {
        Box::new(Self {
            val: F::binary_operation(&l.val, &r.val),
            base: Base::new(&l.base, &r.base, black),
            l: Some(l),
            r: Some(r),
            lazy: F::identity_map(),
        })
    }
    fn new_leaf(val: <F::M as Monoid>::S) -> Box<Self> {
        Box::new(Self {
            val,
            base: Base::new_leaf(),
            l: None,
            r: None,
            lazy: F::identity_map(),
        })
    }
    fn detach(self: Box<Self>) -> (Box<Self>, Box<Self>) {
        let (mut l, mut r) = (self.l.unwrap(), self.r.unwrap());
        l.val = F::mapping(&self.lazy, &l.val);
        r.val = F::mapping(&self.lazy, &r.val);
        l.lazy = F::composition(&self.lazy, &l.lazy);
        r.lazy = F::composition(&self.lazy, &r.lazy);
        (l, r)
    }
}
impl_node!(MapMonoidRBNode<F: MapMonoid>, <F::M as Monoid>::S);
impl<F: MapMonoid> Appliable<F> for MapMonoidRBNode<F> {
    fn apply(mut self: Box<Self>, f: F::F) -> Box<Self> {
        self.val = F::mapping(&f, &self.val);
        self.lazy = F::composition(&f, &self.lazy);
        self
    }
}

/// 作用素モノイドが載る, 区間反転が可能な平衡二分木.
/// 挿入, 削除, 区間取得, 区間作用, 分割, 統合, 区間反転 を O(log n) で行う.
///
/// # Example
/// ```
/// use my_library_rs::*;
/// use std::cmp::min;
///
/// pub struct RangeMin;
/// impl Monoid for RangeMin
/// {
///     type S = u32;
///     fn identity() -> Self::S { Self::S::max_value() }
///     fn binary_operation(&a: &Self::S, &b: &Self::S) -> Self::S { min(a, b) }
/// }
/// struct RangeAddRangeMin;
/// impl MapMonoid for RangeAddRangeMin {
///     type M = RangeMin;
///     type F = u32;
///
///     fn identity_map() -> Self::F { 0 }
///     fn mapping(&f: &Self::F, &a: &<Self::M as Monoid>::S) -> <Self::M as Monoid>::S { a + f }
///     fn composition(&f: &Self::F, &g: &Self::F) -> Self::F { f + g }
/// }
///
/// let mut seg: ReversibleRBLazySegtree<RangeAddRangeMin> = vec![1, 100, 0, 1000].into();
/// assert_eq!(seg.remove(2), 0);  // [1, 100, 1000]
/// seg.insert(1, 10);  // [1, 10, 100, 1000]
///
/// assert_eq!((seg.prod(0, 4), seg.prod(0, 3), seg.prod(1, 2)), (1, 1, 10));
///
/// seg.apply_range(2, 4, 20);  // [1, 10, 120, 1020]
/// seg.apply_range(0, 3, 3000);   // [3001, 3010, 3120, 1020]
/// assert_eq!((seg.get(0), seg.get(1), seg.get(2), seg.get(3)), (3001, 3010, 3120, 1020));
///
/// seg.reverse_range(1, 4); // [3001, 1020, 3120, 3010];
/// seg.reverse_range(0, 2); // [1020, 3001, 3120, 3010];
/// assert_eq!((seg.get(0), seg.get(1), seg.get(2), seg.get(3)), (1020, 3001, 3120, 3010));
/// ```
pub struct ReversibleRBLazySegtree<F: MapMonoid> {
    root: Option<Box<ReversibleMapMonoidRBNode<F>>>,
}
impl_tree!(
    ReversibleRBLazySegtree<F: MapMonoid>,
    ReversibleMapMonoidRBNode<F>
);
impl<F: MapMonoid> RangeFold<F::M, ReversibleMapMonoidRBNode<F>> for ReversibleRBLazySegtree<F> {}
impl<F: MapMonoid> LazyEval<F, ReversibleMapMonoidRBNode<F>> for ReversibleRBLazySegtree<F> {}
impl<F: MapMonoid> Reverse<ReversibleMapMonoidRBNode<F>> for ReversibleRBLazySegtree<F> {}

pub struct ReversibleMapMonoidRBNode<F: MapMonoid> {
    val: <F::M as Monoid>::S,
    base: Base,
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
    lazy: F::F,
    rev: bool,
}
impl<F: MapMonoid> ReversibleMapMonoidRBNode<F> {
    fn new(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self> {
        Box::new(Self {
            val: F::binary_operation(&l.val, &r.val),
            base: Base::new(&l.base, &r.base, black),
            l: Some(l),
            r: Some(r),
            lazy: F::identity_map(),
            rev: false,
        })
    }
    fn new_leaf(val: <F::M as Monoid>::S) -> Box<Self> {
        Box::new(Self {
            val,
            base: Base::new_leaf(),
            l: None,
            r: None,
            lazy: F::identity_map(),
            rev: false,
        })
    }
    fn detach(self: Box<Self>) -> (Box<Self>, Box<Self>) {
        let (mut l, mut r) = (self.l.unwrap(), self.r.unwrap());
        l.val = F::mapping(&self.lazy, &l.val);
        r.val = F::mapping(&self.lazy, &r.val);
        l.lazy = F::composition(&self.lazy, &l.lazy);
        r.lazy = F::composition(&self.lazy, &r.lazy);
        l.rev ^= self.rev;
        r.rev ^= self.rev;
        if self.rev {
            return (r, l);
        }
        (l, r)
    }
}
impl_node!(ReversibleMapMonoidRBNode<F: MapMonoid>, <F::M as Monoid>::S);
impl<F: MapMonoid> Appliable<F> for ReversibleMapMonoidRBNode<F> {
    fn apply(mut self: Box<Self>, f: F::F) -> Box<Self> {
        self.val = F::mapping(&f, &self.val);
        self.lazy = F::composition(&f, &self.lazy);
        self
    }
}
impl<F: MapMonoid> Reversible for ReversibleMapMonoidRBNode<F> {
    fn reverse(mut self: Box<Self>) -> Box<Self> {
        self.rev ^= true;
        self
    }
}
