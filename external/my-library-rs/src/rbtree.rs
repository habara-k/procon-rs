const RED: bool = false;
const BLACK: bool = true;

#[derive(Clone)]
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

use std::ops::Deref;

pub trait Node {
    type Value: Clone;
    type Link: Deref<Target = Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link;
    fn new_leaf(val: Self::Value) -> Self::Link;
    fn detach(p: Self::Link) -> (Self::Link, Self::Link);
    fn make_root(p: Self::Link) -> Self::Link;
    fn black(&self) -> bool;
    fn height(&self) -> usize;
    fn size(&self) -> usize;
    fn val(&self) -> Self::Value;

    fn len(p: &Option<Self::Link>) -> usize {
        if let Some(p) = p {
            return p.size();
        }
        0
    }
    fn merge(a: Option<Self::Link>, b: Option<Self::Link>) -> Option<Self::Link> {
        if a.is_none() {
            return b;
        }
        if b.is_none() {
            return a;
        }
        let (a, b) = (a.unwrap(), b.unwrap());
        assert!(a.black() && b.black());
        Some(Self::make_root(Self::merge_sub(a, b)))
    }
    fn merge_sub(a: Self::Link, b: Self::Link) -> Self::Link {
        // # Require
        //     a.black == true, b.black == true
        // # Ensure
        //     return.height == max(a.height, b.height)
        //     [WARNING] return.black may be false!
        assert!(a.black());
        assert!(b.black());

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
    fn split_range(
        p: Option<Self::Link>,
        l: usize,
        r: usize,
    ) -> (Option<Self::Link>, Option<Self::Link>, Option<Self::Link>) {
        assert!(l <= r && r <= Self::len(&p));
        let (p, c) = Self::split(p, r);
        let (a, b) = Self::split(p, l);
        (a, b, c)
    }
    fn split(p: Option<Self::Link>, k: usize) -> (Option<Self::Link>, Option<Self::Link>) {
        assert!(k <= Self::len(&p));
        if k == 0 {
            return (None, p);
        }
        if k == Self::len(&p) {
            return (p, None);
        }
        let (l, r) = Self::detach(p.unwrap());
        if k < l.size() {
            let (a, b) = Self::split(Some(l), k);
            return (a, Self::merge(b, Some(Self::make_root(r))));
        }
        if k > l.size() {
            let (a, b) = Self::split(Some(r), k - l.size());
            return (Self::merge(Some(Self::make_root(l)), a), b);
        }
        (Some(Self::make_root(l)), Some(Self::make_root(r)))
    }
    fn insert(p: Option<Self::Link>, k: usize, val: Self::Value) -> Option<Self::Link> {
        assert!(k <= Self::len(&p));
        let (a, b) = Self::split(p, k);
        Self::merge(Self::merge(a, Some(Self::new_leaf(val))), b)
    }
    fn remove(p: Option<Self::Link>, k: usize) -> (Option<Self::Link>, Self::Value) {
        assert!(k < Self::len(&p));
        let (a, b, c) = Self::split_range(p, k, k + 1);
        (Self::merge(a, c), b.unwrap().val())
    }
    fn build(v: &[Self::Value], l: usize, r: usize) -> Option<Self::Link> {
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
    fn root(&self) -> &Option<<Self::Node as Node>::Link>;
    fn mut_root(&mut self) -> &mut Option<<Self::Node as Node>::Link>;
    fn new(root: Option<<Self::Node as Node>::Link>) -> Self;
}

use std::mem;
pub trait Tree: Root {
    /// 要素数を返す.
    fn len(&self) -> usize {
        Self::Node::len(self.root())
    }
    /// `k` 番目に `val` を挿入する.
    fn insert(&mut self, k: usize, val: <Self::Node as Node>::Value) {
        assert!(k <= self.len());
        let root = mem::replace(self.mut_root(), None);
        *self.mut_root() = Self::Node::insert(root, k, val);
    }
    /// `k` 番目の要素を削除し, その値を返す.
    fn remove(&mut self, k: usize) -> <Self::Node as Node>::Value {
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
    fn get(&mut self, k: usize) -> <Self::Node as Node>::Value {
        assert!(k < self.len());
        let val = self.remove(k);
        self.insert(k, val.clone());
        val
    }
}

pub use crate::algebra::Monoid;
pub trait RangeFold<M, T>: Tree<Node = T>
where
    M: Monoid,
    T: Node<Value = M::S>,
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
pub trait Apply<F: MapMonoid>: Node<Value = <F::M as Monoid>::S> {
    fn apply(p: <Self as Node>::Link, f: F::F) -> <Self as Node>::Link;
}

pub trait RangeApply<F, T>: Tree<Node = T>
where
    F: MapMonoid,
    T: Apply<F>,
{
    fn apply_range(&mut self, l: usize, r: usize, f: F::F) {
        assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }
        let root = mem::replace(self.mut_root(), None);
        let (a, mut b, c) = Self::Node::split_range(root, l, r);

        b = Some(T::apply(b.unwrap(), f));
        //b = Some(Self::apply(b.uwnrap()));

        *self.mut_root() = Self::Node::merge(Self::Node::merge(a, b), c);
    }
}

pub trait Reverse: Node {
    fn reverse(p: <Self as Node>::Link) -> <Self as Node>::Link;
}
pub trait RangeReverse<T: Reverse>: Tree<Node = T> {
    fn reverse_range(&mut self, l: usize, r: usize) {
        assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }
        let root = mem::replace(self.mut_root(), None);
        let (a, mut b, c) = Self::Node::split_range(root, l, r);

        b = Some(T::reverse(b.unwrap()));

        *self.mut_root() = Self::Node::merge(Self::Node::merge(a, b), c);
    }
}

macro_rules! impl_node {
    ($node:ident<$param:ident : $bound:tt>, $val:ty, $link:ty) => {
        impl<$param: $bound> Node for $node<$param> {
            type Value = $val;
            type Link = $link;
            fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link {
                Self::new(l, r, black)
            }
            fn new_leaf(val: Self::Value) -> Self::Link {
                Self::new_leaf(val)
            }
            fn detach(p: Self::Link) -> (Self::Link, Self::Link) {
                Self::detach(p)
            }
            fn make_root(p: Self::Link) -> Self::Link {
                Self::make_root(p)
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
            fn val(&self) -> Self::Value {
                self.val.clone()
            }
        }
    };
}
macro_rules! impl_apply {
    ($node:ident<$param:ident : $bound:tt>, $map_monoid:ty) => {
        impl<$param: $bound> Apply<$map_monoid> for $node<$param> {
            fn apply(mut p: <Self as Node>::Link, f: <$map_monoid>::F) -> <Self as Node>::Link {
                p.val = <$map_monoid>::mapping(&f, &p.val());
                p.lazy = <$map_monoid>::composition(&f, &p.lazy);
                p
            }
        }
    };
}
macro_rules! impl_reverse {
    ($node:ident<$param:ident : $bound:tt>) => {
        impl<$param: $bound> Reverse for $node<$param> {
            fn reverse(mut p: <Self as Node>::Link) -> <Self as Node>::Link {
                p.rev ^= true;
                p
            }
        }
    };
}

macro_rules! impl_tree {
    ($tree:ident<$param:ident : $bound:tt>, $node:ty) => {
        impl<$param: $bound> Root for $tree<$param> {
            type Node = $node;
            fn root(&self) -> &Option<<Self::Node as Node>::Link> {
                &self.root
            }
            fn mut_root(&mut self) -> &mut Option<<Self::Node as Node>::Link> {
                &mut self.root
            }
            fn new(root: Option<<Self::Node as Node>::Link>) -> Self {
                Self { root }
            }
        }
        impl<$param: $bound> Tree for $tree<$param> {}
        impl<$param: $bound> From<Vec<<$node as Node>::Value>> for $tree<$param> {
            fn from(v: Vec<<$node as Node>::Value>) -> Self {
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
    root: Option<Box<RightNode<T>>>,
}
impl_tree!(RBTree<T: Clone>, RightNode<T>);
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

pub struct RightNode<T> {
    val: T,
    base: Base,
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
}
impl<T: Clone> RightNode<T> {
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
    fn detach(p: Box<Self>) -> (Box<Self>, Box<Self>) {
        assert!(!p.base.is_leaf());
        (p.l.unwrap(), p.r.unwrap())
    }
    fn make_root(mut p: Box<Self>) -> Box<Self> {
        p.base = p.base.into_root();
        p
    }
}
impl_node!(RightNode<T: Clone>, T, Box<RightNode<T>>);

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
    root: Option<Box<MonoidNode<M>>>,
}
impl_tree!(RBSegtree<M: Monoid>, MonoidNode<M>);
impl<M: Monoid> RangeFold<M, MonoidNode<M>> for RBSegtree<M> {}

pub struct MonoidNode<M: Monoid> {
    val: M::S,
    base: Base,
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
}
impl<M: Monoid> MonoidNode<M> {
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
    fn detach(p: Box<Self>) -> (Box<Self>, Box<Self>) {
        (p.l.unwrap(), p.r.unwrap())
    }
    fn make_root(mut p: Box<Self>) -> Box<Self> {
        p.base = p.base.into_root();
        p
    }
}
impl_node!(MonoidNode<M: Monoid>, M::S, Box<MonoidNode<M>>);

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
    root: Option<Box<MapMonoidNode<F>>>,
}
impl_tree!(RBLazySegtree<F: MapMonoid>, MapMonoidNode<F>);
impl<F: MapMonoid> RangeFold<F::M, MapMonoidNode<F>> for RBLazySegtree<F> {}
impl<F: MapMonoid> RangeApply<F, MapMonoidNode<F>> for RBLazySegtree<F> {}

pub struct MapMonoidNode<F: MapMonoid> {
    val: <F::M as Monoid>::S,
    base: Base,
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
    lazy: F::F,
}
impl<F: MapMonoid> MapMonoidNode<F> {
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
    fn detach(p: Box<Self>) -> (Box<Self>, Box<Self>) {
        let (mut l, mut r) = (p.l.unwrap(), p.r.unwrap());
        l.val = F::mapping(&p.lazy, &l.val);
        r.val = F::mapping(&p.lazy, &r.val);
        l.lazy = F::composition(&p.lazy, &l.lazy);
        r.lazy = F::composition(&p.lazy, &r.lazy);
        (l, r)
    }
    fn make_root(mut p: Box<Self>) -> Box<Self> {
        p.base = p.base.into_root();
        p
    }
}
impl_node!(MapMonoidNode<F: MapMonoid>, <F::M as Monoid>::S, Box<MapMonoidNode<F>>);
impl_apply!(MapMonoidNode<F: MapMonoid>, F);

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
    root: Option<Box<ReversibleMapMonoidNode<F>>>,
}
impl_tree!(
    ReversibleRBLazySegtree<F: MapMonoid>,
    ReversibleMapMonoidNode<F>
);
impl<F: MapMonoid> RangeFold<F::M, ReversibleMapMonoidNode<F>> for ReversibleRBLazySegtree<F> {}
impl<F: MapMonoid> RangeApply<F, ReversibleMapMonoidNode<F>> for ReversibleRBLazySegtree<F> {}
impl<F: MapMonoid> RangeReverse<ReversibleMapMonoidNode<F>> for ReversibleRBLazySegtree<F> {}

pub struct ReversibleMapMonoidNode<F: MapMonoid> {
    val: <F::M as Monoid>::S,
    base: Base,
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
    lazy: F::F,
    rev: bool,
}
impl<F: MapMonoid> ReversibleMapMonoidNode<F> {
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
    fn detach(p: Box<Self>) -> (Box<Self>, Box<Self>) {
        let (mut l, mut r) = (p.l.unwrap(), p.r.unwrap());
        l.val = F::mapping(&p.lazy, &l.val);
        r.val = F::mapping(&p.lazy, &r.val);
        l.lazy = F::composition(&p.lazy, &l.lazy);
        r.lazy = F::composition(&p.lazy, &r.lazy);
        l.rev ^= p.rev;
        r.rev ^= p.rev;
        if p.rev {
            return (r, l);
        }
        (l, r)
    }
    fn make_root(mut p: Box<Self>) -> Box<Self> {
        p.base = p.base.into_root();
        p
    }
}
impl_node!(ReversibleMapMonoidNode<F: MapMonoid>, <F::M as Monoid>::S, Box<ReversibleMapMonoidNode<F>>);
impl_apply!(ReversibleMapMonoidNode<F: MapMonoid>, F);
impl_reverse!(ReversibleMapMonoidNode<F: MapMonoid>);

// 以下永続
use std::rc::Rc;

/// 列を管理する永続平衡二分木.
/// 挿入, 削除, 取得, 分割, 統合, lower_bound を O(log n) で行う.
///
/// # Example
/// ```
/// use my_library_rs::*;
///
/// let mut v: PersistentRBTree<u32> = vec![60, 30, 30, 40].into();
/// v.insert(0, 10);  // [10, 60, 30, 30, 40]
/// v.remove(1);      // [10, 30, 30, 40]
///
/// assert_eq!(v.len(), 4);
/// assert_eq!((v.get(0), v.get(1), v.get(2), v.get(3)), (10, 30, 30, 40));
/// assert_eq!((v.lower_bound(25), v.lower_bound(30), v.lower_bound(35)), (1, 1, 3));
///
/// let mut t: PersistentRBTree<u32> = Default::default();
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
///
/// let mut s = t.clone();
/// t.merge(&mut s);  // [30, 40, 10, 20, 30, 40, 10, 20]
/// assert_eq!((t.get(0), t.get(1), t.get(2), t.get(3)), (30, 40, 10, 30));
/// assert_eq!((t.get(4), t.get(5), t.get(6), t.get(7)), (30, 40, 10, 30));
/// ```
#[derive(Clone)]
pub struct PersistentRBTree<T> {
    root: Option<Rc<PersistentRightNode<T>>>,
}
impl_tree!(PersistentRBTree<T: Clone>, PersistentRightNode<T>);
impl<T: Clone + Ord> PersistentRBTree<T> {
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

pub struct PersistentRightNode<T> {
    val: T,
    base: Base,
    l: Option<Rc<Self>>,
    r: Option<Rc<Self>>,
}
impl<T: Clone> PersistentRightNode<T> {
    fn new(l: Rc<Self>, r: Rc<Self>, black: bool) -> Rc<Self> {
        Rc::new(Self {
            val: r.val.clone(),
            base: Base::new(&l.base, &r.base, black),
            l: Some(l),
            r: Some(r),
        })
    }
    fn new_leaf(val: T) -> Rc<Self> {
        Rc::new(Self {
            val,
            base: Base::new_leaf(),
            l: None,
            r: None,
        })
    }
    fn detach(p: Rc<Self>) -> (Rc<Self>, Rc<Self>) {
        assert!(!p.base.is_leaf());
        (p.l.as_ref().unwrap().clone(), p.r.as_ref().unwrap().clone())
    }
    fn make_root(p: Rc<Self>) -> Rc<Self> {
        Rc::new(Self {
            base: p.base.clone().into_root(),
            val: p.val.clone(),
            l: p.l.clone(),
            r: p.r.clone(),
        })
    }
}
impl_node!(PersistentRightNode<T: Clone>, T, Rc<PersistentRightNode<T>>);
