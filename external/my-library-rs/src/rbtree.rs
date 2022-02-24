use crate::rbtree_traits::{
    BuildFromSeq, Insert, LazyEval, Merge, NewLeaf, NodeElem, NodeOps, RangeFold, Remove,
    Reversible, Root, Split, Value,
};

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
pub struct RightNode<T: Clone> {
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
    height: usize,
    black: bool,
    size: usize,
    val: T,
}
impl<T: Clone> NodeOps for RightNode<T> {
    fn connect(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self> {
        assert_eq!(l.height, r.height);
        assert!(l.black || black);
        assert!(r.black || black);
        Box::new(Self {
            size: l.size + r.size,
            height: l.height + black as usize,
            val: r.val.clone(),
            black,
            l: Some(l),
            r: Some(r),
        })
    }
    fn detach(p: Box<Self>) -> (Box<Self>, Box<Self>) {
        (p.l.unwrap(), p.r.unwrap())
    }
}
impl<T: Clone> NewLeaf<T> for RightNode<T> {
    fn new_leaf(val: T) -> Box<Self> {
        Box::new(Self {
            l: None,
            r: None,
            height: 1,
            black: true,
            size: 1,
            val,
        })
    }
}
impl<T: Clone + Ord> RBTree<T> {
    pub fn lower_bound(&self, val: T) -> usize {
        if self.root().is_none() {
            return 0;
        }

        let mut p = self.root().as_ref().unwrap();
        let mut k = 0;

        while let (Some(l), Some(r)) = (p.l(), p.r()) {
            if l.val() < val {
                p = r;
                k += l.size();
            } else {
                p = l;
            }
        }

        k + (p.val() < val) as usize
    }
}

use crate::algebra::Monoid;
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
pub struct MonoidNode<M: Monoid> {
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
    height: usize,
    black: bool,
    size: usize,

    val: M::S,
}
impl<M: Monoid> NodeOps for MonoidNode<M> {
    fn connect(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self> {
        assert_eq!(l.height, r.height);
        assert!(l.black || black);
        assert!(r.black || black);
        Box::new(Self {
            size: l.size + r.size,
            height: l.height + black as usize,
            val: M::binary_operation(&l.val, &r.val),
            black,
            l: Some(l),
            r: Some(r),
        })
    }
    fn detach(p: Box<Self>) -> (Box<Self>, Box<Self>) {
        (p.l.unwrap(), p.r.unwrap())
    }
}
impl<M: Monoid> NewLeaf<M::S> for MonoidNode<M> {
    fn new_leaf(val: M::S) -> Box<Self> {
        Box::new(Self {
            l: None,
            r: None,
            height: 1,
            black: true,
            size: 1,
            val,
        })
    }
}
impl<M: Monoid> RangeFold<M> for RBSegtree<M> {}

use crate::algebra::MapMonoid;
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
pub struct MapMonoidNode<F: MapMonoid> {
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
    height: usize,
    black: bool,
    size: usize,

    val: <F::M as Monoid>::S,
    lazy: F::F,
}
impl<F: MapMonoid> NodeOps for MapMonoidNode<F> {
    fn connect(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self> {
        assert_eq!(l.height, r.height);
        assert!(l.black || black);
        assert!(r.black || black);
        Box::new(Self {
            size: l.size + r.size,
            height: l.height + black as usize,
            val: F::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            black,
            l: Some(l),
            r: Some(r),
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
}

impl<F: MapMonoid> NewLeaf<<F::M as Monoid>::S> for MapMonoidNode<F> {
    fn new_leaf(val: <F::M as Monoid>::S) -> Box<Self> {
        Box::new(Self {
            l: None,
            r: None,
            height: 1,
            black: true,
            size: 1,
            val,
            lazy: F::identity_map(),
        })
    }
}
impl<F: MapMonoid> RangeFold<F::M> for RBLazySegtree<F> {}
impl<F: MapMonoid> LazyEval<F> for RBLazySegtree<F> {
    fn apply(p: &mut Box<Self::Node>, f: F::F) {
        p.val = F::mapping(&f, &p.val);
        p.lazy = F::composition(&f, &p.lazy);
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
pub struct ReversibleMapMonoidNode<F: MapMonoid> {
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
    height: usize,
    black: bool,
    size: usize,

    val: <F::M as Monoid>::S,
    lazy: F::F,
    rev: bool,
}
impl<F: MapMonoid> NodeOps for ReversibleMapMonoidNode<F> {
    fn connect(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self> {
        assert_eq!(l.height, r.height);
        assert!(l.black || black);
        assert!(r.black || black);
        Box::new(Self {
            size: l.size + r.size,
            height: l.height + black as usize,
            val: F::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            rev: false,
            black,
            l: Some(l),
            r: Some(r),
        })
    }
    fn detach(p: Box<Self>) -> (Box<Self>, Box<Self>) {
        let (mut l, mut r) = (p.l.unwrap(), p.r.unwrap());
        l.val = F::mapping(&p.lazy, &l.val);
        r.val = F::mapping(&p.lazy, &r.val);
        l.lazy = F::composition(&p.lazy, &l.lazy);
        r.lazy = F::composition(&p.lazy, &r.lazy);
        if p.rev {
            std::mem::swap(&mut l.l, &mut l.r);
            std::mem::swap(&mut r.l, &mut r.r);
            l.rev ^= true;
            r.rev ^= true;
        }
        (l, r)
    }
}
impl<F: MapMonoid> NewLeaf<<F::M as Monoid>::S> for ReversibleMapMonoidNode<F> {
    fn new_leaf(val: <F::M as Monoid>::S) -> Box<Self> {
        Box::new(Self {
            l: None,
            r: None,
            height: 1,
            black: true,
            size: 1,
            val,
            lazy: F::identity_map(),
            rev: false,
        })
    }
}
impl<F: MapMonoid> RangeFold<F::M> for ReversibleRBLazySegtree<F> {}
impl<F: MapMonoid> LazyEval<F> for ReversibleRBLazySegtree<F> {
    fn apply(p: &mut Box<Self::Node>, f: F::F) {
        p.val = F::mapping(&f, &p.val);
        p.lazy = F::composition(&f, &p.lazy);
    }
}
impl<F: MapMonoid> Reversible<<F::M as Monoid>::S> for ReversibleRBLazySegtree<F> {
    fn reverse(p: &mut Box<Self::Node>) {
        std::mem::swap(&mut p.l, &mut p.r);
        p.rev ^= true;
    }
}

// 宣言的マクロでボイラープレートを除去する.
macro_rules! impl_boilerplate {
    () => {};
    (for $self:ident<$param:ident : $bound:tt> { val => { $val_type:ty }, node => $node_type:ty }; $($rest:tt)*) => {
        pub struct $self<$param:$bound> {
            root: Option<Box<$node_type>>,
        }

        impl<$param:$bound> NodeElem for $node_type {
            fn l(&self) -> &Option<Box<Self>> {
                &self.l
            }
            fn r(&self) -> &Option<Box<Self>> {
                &self.r
            }
            fn height(&self) -> usize {
                self.height
            }
            fn black(&self) -> bool {
                self.black
            }
            fn size(&self) -> usize {
                self.size
            }
        }
        impl<$param: $bound> Merge for $node_type {}
        impl<$param: $bound> Split for $node_type {}
        impl<$param: $bound> Value<$val_type> for $node_type {
            fn val(&self) -> $val_type {
                self.val.clone()
            }
        }
        impl<$param: $bound> Insert<$val_type> for $node_type {}
        impl<$param: $bound> Remove<$val_type> for $node_type {}
        impl<$param: $bound> BuildFromSeq<$val_type> for $node_type {}

        impl<$param: $bound> Root<$val_type> for $self<$param> {
            type Node = $node_type;
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
        impl<$param: $bound> From<Vec<$val_type>> for $self<$param> {
            fn from(v: Vec<$val_type>) -> Self {
                Self {
                    root: <Self as Root<$val_type>>::Node::build(&v, 0, v.len()),
                }
            }
        }
        impl<$param: $bound> Default for $self<$param> {
            fn default() -> Self {
                vec![].into()
            }
        }

        impl_boilerplate!($($rest)*);
    };
}
impl_boilerplate! {
    for RBTree<T: Clone> { val => { T }, node => RightNode<T> };
    for RBSegtree<M: Monoid> { val => { M::S }, node => MonoidNode<M> };
    for RBLazySegtree<F: MapMonoid> { val => { <F::M as Monoid>::S }, node => MapMonoidNode<F> };
    for ReversibleRBLazySegtree<F: MapMonoid> { val => { <F::M as Monoid>::S }, node => ReversibleMapMonoidNode<F> };
}
