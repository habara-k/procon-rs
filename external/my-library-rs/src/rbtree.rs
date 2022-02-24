use crate::rbtree_traits::{
    BuildFromSeq, Insert, LazyEval, Merge, Node, RangeFold, Remove, Root, Split, Value,
};

/// 列を管理する平衡二分木.
/// 挿入, 削除, 取得, lower_bound を O(log n) で行う.
///
/// # Example
/// ```
/// use my_library_rs::*;
///
/// let mut v: RBTree<u32> = vec![60, 20, 30, 40].into();
/// v.insert(0, 10);  // [10, 60, 20, 30, 40]
/// v.insert(3, 30);  // [10, 60, 20, 30, 30, 40]
/// v.remove(1);      // [10, 20, 30, 30, 40]
///
/// assert_eq!(v.len(), 5);
/// assert_eq!(v.get(0), 10);
/// assert_eq!(v.get(1), 20);
/// assert_eq!(v.get(2), 30);
/// assert_eq!(v.get(3), 30);
/// assert_eq!(v.get(4), 40);
///
/// assert_eq!(v.lower_bound(0), 0);
/// assert_eq!(v.lower_bound(100), 5);
/// assert_eq!(v.lower_bound(25), 2);
/// assert_eq!(v.lower_bound(30), 2);
/// assert_eq!(v.lower_bound(35), 4);
/// ```
pub struct RBTree<T> {
    root: Option<Box<RightNode<T>>>,
}

pub struct RightNode<T> {
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
    height: usize,
    black: bool,
    size: usize,

    val: T,
}
impl<T: Clone> Node for RightNode<T> {
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
impl<T: Clone> Value<T> for RightNode<T> {
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
    fn get_val(&self) -> T {
        self.val.clone()
    }
}
impl<T: Clone> Merge for RightNode<T> {}
impl<T: Clone> Split for RightNode<T> {}
impl<T: Clone> Insert<T> for RightNode<T> {}
impl<T: Clone> Remove<T> for RightNode<T> {}
impl<T: Clone> BuildFromSeq<T> for RightNode<T> {}

impl<T: Clone> Root<T> for RBTree<T> {
    type Node = RightNode<T>;
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
impl<T: Clone> From<Vec<T>> for RBTree<T> {
    fn from(v: Vec<T>) -> Self {
        Self {
            root: <Self as Root<T>>::Node::build(&v, 0, v.len()),
        }
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
            if l.get_val() < val {
                p = r;
                k += l.size();
            } else {
                p = l;
            }
        }

        k + (p.get_val() < val) as usize
    }
}

use crate::algebra::Monoid;
/// モノイドが載る平衡二分木.
/// 挿入, 削除, 区間取得を O(log n) で行う.
///
/// # Example
/// ```
/// use my_library_rs::*;
///
/// pub struct RangeSum;
/// impl Monoid for RangeSum {
///     type S = u32;
///     fn identity() -> Self::S {
///         0
///     }
///     fn binary_operation(a: &Self::S, b: &Self::S) -> Self::S {
///         *a + *b
///     }
/// }
///
/// let mut seg: RBSegtree<RangeSum> = vec![1, 100, 1000, 0, 10000].into();
/// assert_eq!(seg.remove(3), 0);  // [1, 100, 1000, 10000]
/// seg.insert(1, 10);  // [1, 10, 100, 1000, 10000]
///
/// assert_eq!(seg.prod(0, 5), 11111);
/// assert_eq!(seg.prod(1, 4), 1110);
/// assert_eq!(seg.prod(3, 5), 11000);
/// ```
pub struct RBSegtree<M: Monoid> {
    root: Option<Box<MonoidNode<M>>>,
}

pub struct MonoidNode<M: Monoid> {
    l: Option<Box<Self>>,
    r: Option<Box<Self>>,
    height: usize,
    black: bool,
    size: usize,

    val: M::S,
}
impl<M: Monoid> Node for MonoidNode<M> {
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
impl<M: Monoid> Value<M::S> for MonoidNode<M> {
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
    fn get_val(&self) -> M::S {
        self.val.clone()
    }
}
impl<M: Monoid> Merge for MonoidNode<M> {}
impl<M: Monoid> Split for MonoidNode<M> {}
impl<M: Monoid> Insert<M::S> for MonoidNode<M> {}
impl<M: Monoid> Remove<M::S> for MonoidNode<M> {}
impl<M: Monoid> BuildFromSeq<M::S> for MonoidNode<M> {}

impl<M: Monoid> Root<M::S> for RBSegtree<M> {
    type Node = MonoidNode<M>;
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

impl<M: Monoid> From<Vec<M::S>> for RBSegtree<M> {
    fn from(v: Vec<M::S>) -> Self {
        Self {
            root: <Self as Root<M::S>>::Node::build(&v, 0, v.len()),
        }
    }
}

impl<M: Monoid> RangeFold<M> for RBSegtree<M> {}

use crate::algebra::MapMonoid;
/// 作用素モノイドが載る平衡二分木.
/// 挿入, 削除, 区間取得, 区間作用 を O(log n) で行う.
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
///     fn identity() -> Self::S {
///         Self::S::max_value()
///     }
///     fn binary_operation(&a: &Self::S, &b: &Self::S) -> Self::S {
///         min(a, b)
///     }
/// }
/// struct RangeAddRangeMin;
/// impl MapMonoid for RangeAddRangeMin {
///     type M = RangeMin;
///     type F = u32;
///
///     fn identity_map() -> Self::F {
///         0
///     }
///     fn mapping(&f: &Self::F, &a: &<Self::M as Monoid>::S) -> <Self::M as Monoid>::S {
///         a + f
///     }
///     fn composition(&f: &Self::F, &g: &Self::F) -> Self::F {
///         f + g
///     }
/// }
///
/// let mut seg: RBLazySegtree<RangeAddRangeMin> = vec![1, 100, 1000, 0, 10000].into();
/// assert_eq!(seg.remove(3), 0);  // [1, 100, 1000, 10000]
/// seg.insert(1, 10);  // [1, 10, 100, 1000, 10000]
///
/// assert_eq!(seg.prod(0, 5), 1);
/// assert_eq!(seg.prod(1, 4), 10);
/// assert_eq!(seg.prod(3, 5), 1000);
///
/// seg.apply_range(2, 5, 20);  // [1, 10, 120, 1020, 10020]
/// seg.apply_range(0, 3, 3000);   // [3001, 3010, 3120, 1020, 10020]
/// assert_eq!(seg.get(0), 3001);
/// assert_eq!(seg.get(1), 3010);
/// assert_eq!(seg.get(2), 3120);
/// assert_eq!(seg.get(3), 1020);
/// assert_eq!(seg.get(4), 10020);
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
impl<F: MapMonoid> Node for MapMonoidNode<F> {
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
impl<F: MapMonoid> MapMonoidNode<F> {
    fn apply(p: &mut Box<Self>, f: F::F) {
        p.val = F::mapping(&f, &p.val);
        p.lazy = F::composition(&f, &p.lazy);
    }
}

impl<F: MapMonoid> Value<<F::M as Monoid>::S> for MapMonoidNode<F> {
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
    fn get_val(&self) -> <F::M as Monoid>::S {
        self.val.clone()
    }
}
impl<F: MapMonoid> Merge for MapMonoidNode<F> {}
impl<F: MapMonoid> Split for MapMonoidNode<F> {}
impl<F: MapMonoid> Insert<<F::M as Monoid>::S> for MapMonoidNode<F> {}
impl<F: MapMonoid> Remove<<F::M as Monoid>::S> for MapMonoidNode<F> {}
impl<F: MapMonoid> BuildFromSeq<<F::M as Monoid>::S> for MapMonoidNode<F> {}

pub struct RBLazySegtree<F: MapMonoid> {
    root: Option<Box<MapMonoidNode<F>>>,
}
impl<F: MapMonoid> Root<<F::M as Monoid>::S> for RBLazySegtree<F> {
    type Node = MapMonoidNode<F>;
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

impl<F: MapMonoid> From<Vec<<F::M as Monoid>::S>> for RBLazySegtree<F> {
    fn from(v: Vec<<F::M as Monoid>::S>) -> Self {
        Self {
            root: <Self as Root<<F::M as Monoid>::S>>::Node::build(&v, 0, v.len()),
        }
    }
}

impl<F: MapMonoid> RangeFold<F::M> for RBLazySegtree<F> {}

impl<F: MapMonoid> LazyEval<F> for RBLazySegtree<F> {
    fn apply(p: &mut Box<Self::Node>, f: F::F) {
        Self::Node::apply(p, f);
    }
}
