use crate::rbtree_traits::*;

macro_rules! impl_node {
    (
        $node:ty where [$($params:tt)*];
        val = $val_type:ty;
        link = $link_type:ty;
        new($l:ident, $r:ident, $black:ident) = $new:block;
        new_leaf($new_val:ident) = $new_leaf:block;
        detach($($p1:tt)*) = $detach:block;
        make_black($($p2:tt)*) = $make_black:block;
        val(&$self:ident) = $get_val:block;
    ) => {
        impl<$($params)*> Node for $node {
            type Value = $val_type;
            type Link = $link_type;
            fn new($l: Self::Link, $r: Self::Link, $black: bool) -> Self::Link {
                $new
            }
            fn new_leaf($new_val: Self::Value) -> Self::Link {
                $new_leaf
            }
            fn detach($($p1)*: Self::Link) -> (Self::Link, Self::Link) {
                $detach
            }
            fn make_black($($p2)*: Self::Link) -> Self::Link {
                $make_black
            }
            fn val(&$self) -> Self::Value {
                $get_val
            }
            fn base(&self) -> &Base<Self> {
                &self.base
            }
        }
    };
}
macro_rules! impl_persistent_node {
    (
        $node:ty where [$($params:tt)*];
        clone(&$self:ident) = $clone:block;
    ) => {
        impl<$($params)*> Clone for $node {
            fn clone(&$self) -> Self {
                $clone
            }
        }
    };
}

macro_rules! impl_tree {
    (
        $tree:ty where [$($params:tt)*];
        node = $node:ty;
    ) => {
        impl<$($params)*> Root for $tree {
            type Node = $node;
            fn root(&mut self) -> &mut Option<<Self::Node as Node>::Link> {
                &mut self.root
            }
            fn new(root: Option<<Self::Node as Node>::Link>) -> Self {
                Self { root }
            }
        }
        impl<$($params)*> Tree for $tree {}
        impl<$($params)*> From<Vec<<$node as Node>::Value>> for $tree {
            fn from(v: Vec<<$node as Node>::Value>) -> Self {
                Self {
                    root: <Self as Root>::Node::build(&v, 0, v.len()),
                }
            }
        }
        impl<$($params)*> Default for $tree {
            fn default() -> Self {
                Self { root: None }
            }
        }
    };
}
macro_rules! impl_persistent_tree {
    (
        $tree:ty where [$($params:tt)*];
    ) => {
        impl<$($params)*> Clone for $tree {
            fn clone(&self) -> Self {
                Self {
                    root: self.root.clone()
                }
            }
        }
    };
}

macro_rules! impl_range_fold {
    (
        tree = $tree:ty where [$($tree_params:tt)*];
        node = $node:ty;
        monoid = $monoid:ty;
    ) => {
        impl<$($tree_params)*> RangeFold<$monoid, $node> for $tree {}
    };
}
macro_rules! impl_binary_search {
    (
        tree = $tree:ty where [$($tree_params:tt)*];
        node = $node:ty where [$($node_params:tt)*];
        monoid = $monoid:ty;
    ) => {
        impl<$($node_params)*> MinLeft<$monoid> for $node {}
        impl<$($node_params)*> MaxRight<$monoid> for $node {}
        impl<$($tree_params)*> BinarySearch<$monoid, $node> for $tree {}
    };
}
macro_rules! impl_range_apply {
    (
        tree = $tree:ty where [$($tree_params:tt)*];
        node = $node:ty where [$($node_params:tt)*];
        map_monoid = $map_monoid:ty;
        apply($f:ident, $($p:tt)*) = $apply:block;
    ) => {
        impl<$($tree_params)*> RangeApply<$map_monoid, $node> for $tree {}
        impl<$($node_params)*> Apply<$map_monoid> for $node {
            fn apply($($p)*: <Self as Node>::Link, $f: <$map_monoid>::F) -> <Self as Node>::Link {
                $apply
            }
        }
    };
}
macro_rules! impl_range_reverse {
    (
        tree = $tree:ty where [$($tree_params:tt)*];
        node = $node:ty where [$($node_params:tt)*];
        reverse($($p:tt)*) = $reverse:block;
    ) => {
        impl<$($tree_params)*> RangeReverse<$node> for $tree {}
        impl<$($node_params)*> Reverse for $node {
            fn reverse($($p)*: <Self as Node>::Link) -> <Self as Node>::Link {
                $reverse
            }
        }
    };
}

/// 列を管理する平衡二分木.
/// 挿入, 削除, 分割, 統合 を O(log n) で行う.
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
///
/// let (mut v, mut t) = v.split(2);  // [10, 30], [30, 40];
/// assert_eq!(v.collect_vec(), vec![10, 30]);
/// assert_eq!(t.collect_vec(), vec![30, 40]);
///
/// t.merge(&mut v);  // [30, 40, 10, 30];
/// assert_eq!(t.collect_vec(), vec![30, 40, 10, 30]);
/// assert_eq!(v.collect_vec(), vec![]);
/// ```
pub struct RBTree<U: Clone> {
    root: Option<Box<OptionNode<U>>>,
}
impl_tree! {
    RBTree<U> where [U: Clone];
    node = OptionNode<U>;
}

pub struct OptionNode<U: Clone> {
    val: Option<U>,
    base: Base<Self>,
}
impl_node! {
    OptionNode<U> where [U: Clone];
    val = U;
    link = Box<OptionNode<U>>;
    new(l, r, black) = {
        Box::new(Self {
            val: None,
            base: Base::new(l, r, black),
        })
    };
    new_leaf(val) = {
        Box::new(Self {
            val: Some(val),
            base: Base::new_leaf(),
        })
    };
    detach(p) = {
        p.base.detach()
    };
    make_black(mut p) = {
        if !p.base.black() {
            p.base.make_black();
        }
        p
    };
    val(&self) = {
        self.val.as_ref().unwrap().clone()
    };
}

/// モノイドが載る平衡二分木.
/// 挿入, 削除, 分割, 統合, 区間取得, 二分探索 を O(log n) で行う.
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
///
/// assert_eq!(seg.min_left(4, |x| x <= 1110), 1);
/// assert_eq!(seg.min_left(4, |x| x < 1110), 2);
/// assert_eq!(seg.max_right(1, |x| x <= 110), 3);
/// assert_eq!(seg.max_right(1, |x| x < 110), 2);
/// ```
pub struct RBSegtree<M: Monoid> {
    root: Option<Box<MonoidNode<M>>>,
}
impl_tree! {
    RBSegtree<M> where [M: Monoid];
    node = MonoidNode<M>;
}

pub struct MonoidNode<M: Monoid> {
    val: M::S,
    base: Base<Self>,
}
impl_node! {
    MonoidNode<M> where [M: Monoid];
    val = M::S;
    link = Box<MonoidNode<M>>;
    new(l, r, black) = {
        Box::new(Self {
            val: M::binary_operation(&l.val, &r.val),
            base: Base::new(l, r, black),
        })
    };
    new_leaf(val) = {
        Box::new(Self {
            val,
            base: Base::new_leaf(),
        })
    };
    detach(p) = {
        p.base.detach()
    };
    make_black(mut p) = {
        if !p.base.black() {
            p.base.make_black();
        }
        p
    };
    val(&self) = {
        self.val.clone()
    };
}

impl_range_fold! {
    tree = RBSegtree<M> where [M: Monoid];
    node = MonoidNode<M>;
    monoid = M;
}
impl_binary_search! {
    tree = RBSegtree<M> where [M: Monoid];
    node = MonoidNode<M> where [M: Monoid];
    monoid = M;
}

/// 作用素モノイドが載る平衡二分木.
/// 挿入, 削除, 分割, 統合, 区間取得, 二分探索, 区間作用 を O(log n) で行う.
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
/// assert_eq!(seg.collect_vec(), vec![3001, 3010, 3120, 1020]);
/// ```
pub struct RBLazySegtree<F: MapMonoid> {
    root: Option<Box<MapMonoidNode<F>>>,
}
impl_tree! {
    RBLazySegtree<F> where [F: MapMonoid];
    node = MapMonoidNode<F>;
}

pub struct MapMonoidNode<F: MapMonoid> {
    val: <F::M as Monoid>::S,
    lazy: F::F,
    base: Base<Self>,
}
impl_node! {
    MapMonoidNode<F> where [F: MapMonoid];
    val = <F::M as Monoid>::S;
    link = Box<MapMonoidNode<F>>;
    new(l, r, black) = {
        Box::new(Self {
            val: F::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            base: Base::new(l, r, black),
        })
    };
    new_leaf(val) = {
        Box::new(Self {
            val,
            lazy: F::identity_map(),
            base: Base::new_leaf(),
        })
    };
    detach(p) = {
        let (mut l, mut r) = p.base.detach();
        l.val = F::mapping(&p.lazy, &l.val);
        r.val = F::mapping(&p.lazy, &r.val);
        l.lazy = F::composition(&p.lazy, &l.lazy);
        r.lazy = F::composition(&p.lazy, &r.lazy);
        (l, r)
    };
    make_black(mut p) = {
        if !p.base.black() {
            p.base.make_black();
        }
        p
    };
    val(&self) = {
        self.val.clone()
    };
}

impl_range_fold! {
    tree = RBLazySegtree<F> where [F: MapMonoid];
    node = MapMonoidNode<F>;
    monoid = F::M;
}
impl_binary_search! {
    tree = RBLazySegtree<F> where [F: MapMonoid];
    node = MapMonoidNode<F> where [F: MapMonoid];
    monoid = F::M;
}
impl_range_apply! {
    tree = RBLazySegtree<F> where [F: MapMonoid];
    node = MapMonoidNode<F> where [F: MapMonoid];
    map_monoid = F;
    apply(f, mut p) = {
        p.val = F::mapping(&f, &p.val);
        p.lazy = F::composition(&f, &p.lazy);
        p
    };
}

/// 作用素モノイドが載る, 区間反転が可能な平衡二分木.
/// 挿入, 削除, 分割, 統合, 区間取得, 二分探索, 区間作用, 区間反転 を O(log n) で行う.
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
/// assert_eq!(seg.collect_vec(), vec![3001, 3010, 3120, 1020]);
///
/// seg.reverse_range(1, 4); // [3001, 1020, 3120, 3010];
/// seg.reverse_range(0, 2); // [1020, 3001, 3120, 3010];
/// assert_eq!(seg.collect_vec(), vec![1020, 3001, 3120, 3010]);
/// ```
pub struct ReversibleRBLazySegtree<F: MapMonoid> {
    root: Option<Box<ReversibleMapMonoidNode<F>>>,
}
impl_tree! {
    ReversibleRBLazySegtree<F> where [F: MapMonoid];
    node = ReversibleMapMonoidNode<F>;
}

pub struct ReversibleMapMonoidNode<F: MapMonoid> {
    val: <F::M as Monoid>::S,
    lazy: F::F,
    rev: bool,
    base: Base<Self>,
}
impl_node! {
    ReversibleMapMonoidNode<F> where [F: MapMonoid];
    val = <F::M as Monoid>::S;
    link = Box<ReversibleMapMonoidNode<F>>;
    new(l, r, black) = {
        Box::new(Self {
            val: F::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            rev: false,
            base: Base::new(l, r, black),
        })
    };
    new_leaf(val) = {
        Box::new(Self {
            val,
            lazy: F::identity_map(),
            rev: false,
            base: Base::new_leaf(),
        })
    };
    detach(p) = {
        let (mut l, mut r) = p.base.detach();
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
    };
    make_black(mut p) = {
        if !p.base.black() {
            p.base.make_black();
        }
        p
    };
    val(&self) = {
        self.val.clone()
    };
}

impl_range_fold! {
    tree = ReversibleRBLazySegtree<F> where [F: MapMonoid];
    node = ReversibleMapMonoidNode<F>;
    monoid = F::M;
}
impl_binary_search! {
    tree = ReversibleRBLazySegtree<F> where [F: MapMonoid];
    node = ReversibleMapMonoidNode<F> where [F: MapMonoid];
    monoid = F::M;
}
impl_range_apply! {
    tree = ReversibleRBLazySegtree<F> where [F: MapMonoid];
    node = ReversibleMapMonoidNode<F> where [F: MapMonoid];
    map_monoid = F;
    apply(f, mut p) = {
        p.val = F::mapping(&f, &p.val);
        p.lazy = F::composition(&f, &p.lazy);
        p
    };
}
impl_range_reverse! {
    tree = ReversibleRBLazySegtree<F> where [F: MapMonoid];
    node = ReversibleMapMonoidNode<F> where [F: MapMonoid];
    reverse(mut p) = {
        p.rev ^= true;
        p
    };
}

use std::rc::Rc;
/// 列を管理する永続平衡二分木.
/// 挿入, 削除, 分割, 統合 を O(log n), 複製 を O(1) で行う.
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
///
/// let (mut v, mut t) = v.split(2);  // [10, 30], [30, 40];
/// assert_eq!(v.collect_vec(), vec![10, 30]);
/// assert_eq!(t.collect_vec(), vec![30, 40]);
///
/// t.merge(&mut v);  // [30, 40, 10, 30];
/// assert_eq!(t.collect_vec(), vec![30, 40, 10, 30]);
/// assert_eq!(v.collect_vec(), vec![]);
///
/// let mut s = t.clone();
/// t.merge(&mut s);  // [30, 40, 10, 30, 30, 40, 10, 30]
/// assert_eq!(t.collect_vec(), vec![30, 40, 10, 30, 30, 40, 10, 30]);
/// ```
pub struct PersistentRBTree<U: Clone> {
    root: Option<Rc<PersistentOptionNode<U>>>,
}
impl_tree! {
    PersistentRBTree<U> where [U: Clone];
    node = PersistentOptionNode<U>;
}
impl_persistent_tree! {
    PersistentRBTree<U> where [U: Clone];
}

pub struct PersistentOptionNode<U: Clone> {
    val: Option<U>,
    base: Base<Self>,
}
impl_node! {
    PersistentOptionNode<U> where [U: Clone];
    val = U;
    link = Rc<PersistentOptionNode<U>>;
    new(l, r, black) = {
        Rc::new(Self {
            val: None,
            base: Base::new(l, r, black),
        })
    };
    new_leaf(val) = {
        Rc::new(Self {
            val: Some(val),
            base: Base::new_leaf(),
        })
    };
    detach(p) = {
        p.base.clone().detach()
    };
    make_black(mut p) = {
        if !p.base.black() {
            Rc::make_mut(&mut p).base.make_black();
        }
        p
    };
    val(&self) = {
        self.val.as_ref().unwrap().clone()
    };
}
impl_persistent_node! {
    PersistentOptionNode<U> where [U: Clone];
    clone(&self) = {
        Self {
            val: self.val.clone(),
            base: self.base.clone(),
        }
    };
}

/// モノイドが載る永続平衡二分木.
/// 挿入, 削除, 分割, 統合, 区間取得, 二分探索 を O(log n), 複製 を O(1) で行う.
pub struct PersistentRBSegtree<M: Monoid> {
    root: Option<Rc<PersistentMonoidNode<M>>>,
}
impl_tree! {
    PersistentRBSegtree<M> where [M: Monoid];
    node = PersistentMonoidNode<M>;
}
impl_persistent_tree! {
    PersistentRBSegtree<M> where [M: Monoid];
}

pub struct PersistentMonoidNode<M: Monoid> {
    val: M::S,
    base: Base<Self>,
}
impl_node! {
    PersistentMonoidNode<M> where [M: Monoid];
    val = M::S;
    link = Rc<PersistentMonoidNode<M>>;
    new(l, r, black) = {
        Rc::new(Self {
            val: M::binary_operation(&l.val, &r.val),
            base: Base::new(l, r, black),
        })
    };
    new_leaf(val) = {
        Rc::new(Self {
            val,
            base: Base::new_leaf(),
        })
    };
    detach(p) = {
        p.base.clone().detach()
    };
    make_black(mut p) = {
        if !p.base.black() {
            Rc::make_mut(&mut p).base.make_black();
        }
        p
    };
    val(&self) = {
        self.val.clone()
    };
}
impl_persistent_node! {
    PersistentMonoidNode<M> where [M: Monoid];
    clone(&self) = {
        Self {
            val: self.val.clone(),
            base: self.base.clone(),
        }
    };
}

impl_range_fold! {
    tree = PersistentRBSegtree<M> where [M: Monoid];
    node = PersistentMonoidNode<M>;
    monoid = M;
}
impl_binary_search! {
    tree = PersistentRBSegtree<M> where [M: Monoid];
    node = PersistentMonoidNode<M> where [M: Monoid];
    monoid = M;
}

/// 作用素モノイドが載る永続平衡二分木.
/// 挿入, 削除, 分割, 統合, 区間取得, 二分探索, 区間作用 を O(log n), 複製 を O(1) で行う.
pub struct PersistentRBLazySegtree<F: MapMonoid> {
    root: Option<Rc<PersistentMapMonoidNode<F>>>,
}
impl_tree! {
    PersistentRBLazySegtree<F> where [F: MapMonoid];
    node = PersistentMapMonoidNode<F>;
}
impl_persistent_tree! {
    PersistentRBLazySegtree<F> where [F: MapMonoid];
}

pub struct PersistentMapMonoidNode<F: MapMonoid> {
    val: <F::M as Monoid>::S,
    lazy: F::F,
    base: Base<Self>,
}
impl_node! {
    PersistentMapMonoidNode<F> where [F: MapMonoid];
    val = <F::M as Monoid>::S;
    link = Rc<PersistentMapMonoidNode<F>>;
    new(l, r, black) = {
        Rc::new(Self {
            val: F::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            base: Base::new(l, r, black),
        })
    };
    new_leaf(val) = {
        Rc::new(Self {
            val,
            lazy: F::identity_map(),
            base: Base::new_leaf(),
        })
    };
    detach(p) = {
        let (mut l, mut r) = p.base.clone().detach();
        Rc::make_mut(&mut l).val = F::mapping(&p.lazy, &l.val);
        Rc::make_mut(&mut r).val = F::mapping(&p.lazy, &r.val);
        Rc::make_mut(&mut l).lazy = F::composition(&p.lazy, &l.lazy);
        Rc::make_mut(&mut r).lazy = F::composition(&p.lazy, &r.lazy);
        (l, r)
    };
    make_black(mut p) = {
        if !p.base.black() {
            Rc::make_mut(&mut p).base.make_black();
        }
        p
    };
    val(&self) = {
        self.val.clone()
    };
}
impl_persistent_node! {
    PersistentMapMonoidNode<F> where [F: MapMonoid];
    clone(&self) = {
        Self {
            val: self.val.clone(),
            lazy: self.lazy.clone(),
            base: self.base.clone(),
        }
    };
}

impl_range_fold! {
    tree = PersistentRBLazySegtree<F> where [F: MapMonoid];
    node = PersistentMapMonoidNode<F>;
    monoid = F::M;
}
impl_binary_search! {
    tree = PersistentRBLazySegtree<F> where [F: MapMonoid];
    node = PersistentMapMonoidNode<F> where [F: MapMonoid];
    monoid = F::M;
}
impl_range_apply! {
    tree = PersistentRBLazySegtree<F> where [F: MapMonoid];
    node = PersistentMapMonoidNode<F> where [F: MapMonoid];
    map_monoid = F;
    apply(f, mut p) = {
        Rc::make_mut(&mut p).val = F::mapping(&f, &p.val);
        Rc::make_mut(&mut p).lazy = F::composition(&f, &p.lazy);
        p
    };
}

/// 作用素モノイドが載る, 区間反転が可能な永続平衡二分木.
/// 挿入, 削除, 分割, 統合, 区間取得, 二分探索, 区間作用, 区間反転 を O(log n), 複製 を O(1) で行う.
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
/// let mut seg: PersistentReversibleRBLazySegtree<RangeAddRangeMin> = vec![1, 100, 0, 1000].into();
/// assert_eq!(seg.remove(2), 0);  // [1, 100, 1000]
/// seg.insert(1, 10);  // [1, 10, 100, 1000]
///
/// assert_eq!((seg.prod(0, 4), seg.prod(0, 3), seg.prod(1, 2)), (1, 1, 10));
///
/// seg.apply_range(2, 4, 20);  // [1, 10, 120, 1020]
/// seg.apply_range(0, 3, 3000);   // [3001, 3010, 3120, 1020]
/// assert_eq!(seg.collect_vec(), vec![3001, 3010, 3120, 1020]);
///
/// seg.reverse_range(1, 4); // [3001, 1020, 3120, 3010];
/// seg.reverse_range(0, 2); // [1020, 3001, 3120, 3010];
/// assert_eq!(seg.collect_vec(), vec![1020, 3001, 3120, 3010]);
///
/// let mut t = seg.clone();
/// seg.merge(&mut t);  // [1020, 3001, 3120, 3010, 1020, 3001, 3120, 3010]
/// seg.apply_range(2, 5, 50000);  // [1020, 3001, 53120, 53010, 51020, 3001, 3120, 3010]
/// seg.reverse_range(1, 6);  // [1020, 3001, 51020, 53010, 53120, 3001, 3120, 3010]
/// assert_eq!(seg.collect_vec(), vec![1020, 3001, 51020, 53010, 53120, 3001, 3120, 3010]);
/// ```
pub struct PersistentReversibleRBLazySegtree<F: MapMonoid> {
    root: Option<Rc<PersistentReversibleMapMonoidNode<F>>>,
}
impl_tree! {
    PersistentReversibleRBLazySegtree<F> where [F: MapMonoid];
    node = PersistentReversibleMapMonoidNode<F>;
}
impl_persistent_tree! {
    PersistentReversibleRBLazySegtree<F> where [F: MapMonoid];
}

pub struct PersistentReversibleMapMonoidNode<F: MapMonoid> {
    val: <F::M as Monoid>::S,
    lazy: F::F,
    rev: bool,
    base: Base<Self>,
}
impl_node! {
    PersistentReversibleMapMonoidNode<F> where [F: MapMonoid];
    val = <F::M as Monoid>::S;
    link = Rc<PersistentReversibleMapMonoidNode<F>>;
    new(l, r, black) = {
        Rc::new(Self {
            val: F::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            rev: false,
            base: Base::new(l, r, black),
        })
    };
    new_leaf(val) = {
        Rc::new(Self {
            val,
            lazy: F::identity_map(),
            rev: false,
            base: Base::new_leaf(),
        })
    };
    detach(p) = {
        let (mut l, mut r) = p.base.clone().detach();
        Rc::make_mut(&mut l).val = F::mapping(&p.lazy, &l.val);
        Rc::make_mut(&mut r).val = F::mapping(&p.lazy, &r.val);
        Rc::make_mut(&mut l).lazy = F::composition(&p.lazy, &l.lazy);
        Rc::make_mut(&mut r).lazy = F::composition(&p.lazy, &r.lazy);
        Rc::make_mut(&mut l).rev ^= p.rev;
        Rc::make_mut(&mut r).rev ^= p.rev;
        if p.rev {
            return (r, l);
        }
        (l, r)
    };
    make_black(mut p) = {
        if !p.base.black() {
            Rc::make_mut(&mut p).base.make_black();
        }
        p
    };
    val(&self) = {
        self.val.clone()
    };
}
impl_persistent_node! {
    PersistentReversibleMapMonoidNode<F> where [F: MapMonoid];
    clone(&self) = {
        Self {
            val: self.val.clone(),
            lazy: self.lazy.clone(),
            rev: self.rev.clone(),
            base: self.base.clone(),
        }
    };
}

impl_range_fold! {
    tree = PersistentReversibleRBLazySegtree<F> where [F: MapMonoid];
    node = PersistentReversibleMapMonoidNode<F>;
    monoid = F::M;
}
impl_binary_search! {
    tree = PersistentReversibleRBLazySegtree<F> where [F: MapMonoid];
    node = PersistentReversibleMapMonoidNode<F> where [F: MapMonoid];
    monoid = F::M;
}
impl_range_apply! {
    tree = PersistentReversibleRBLazySegtree<F> where [F: MapMonoid];
    node = PersistentReversibleMapMonoidNode<F> where [F: MapMonoid];
    map_monoid = F;
    apply(f, mut p) = {
        Rc::make_mut(&mut p).val = F::mapping(&f, &p.val);
        Rc::make_mut(&mut p).lazy = F::composition(&f, &p.lazy);
        p
    };
}
impl_range_reverse! {
    tree = PersistentReversibleRBLazySegtree<F> where [F: MapMonoid];
    node = PersistentReversibleMapMonoidNode<F> where [F: MapMonoid];
    reverse(mut p) = {
        Rc::make_mut(&mut p).rev ^= true;
        p
    };
}
