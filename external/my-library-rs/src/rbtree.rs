use crate::algebra::{MapMonoid, Monoid};
use crate::rbtree_traits::*;
use std::rc::Rc;

/// 赤黒木が平衡を保つために必要な情報を管理する構造体
pub struct Base<T: Node> {
    l: Option<T::Link>,
    r: Option<T::Link>,
    black: bool,
    height: usize, // 黒高さ
    size: usize,   // 葉の数
}

impl<T: Node> Base<T> {
    pub fn new(l: T::Link, r: T::Link, black: bool) -> Self {
        debug_assert_eq!(l.height(), r.height());
        debug_assert!(l.black() || black);
        debug_assert!(r.black() || black);
        Self {
            black,
            height: l.height() + black as usize,
            size: l.size() + r.size(),
            l: Some(l),
            r: Some(r),
        }
    }
    pub fn new_leaf() -> Self {
        Self {
            black: true,
            height: 1,
            size: 1,
            l: None,
            r: None,
        }
    }
    pub fn is_leaf(&self) -> bool {
        self.black && self.height == 1
    }
    pub fn make_root(&mut self) {
        if !self.black {
            self.black = true;
            self.height += 1;
        }
    }
    pub fn detach(self) -> (T::Link, T::Link) {
        debug_assert!(!self.is_leaf());
        (self.l.unwrap(), self.r.unwrap())
    }
    pub fn black(&self) -> bool {
        self.black
    }
    pub fn height(&self) -> usize {
        self.height
    }
    pub fn size(&self) -> usize {
        self.size
    }
}

/// 列を管理する平衡二分木.
/// 挿入, 削除, 分割, 併合 を O(log n) で行う.
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
pub type RBTree<U> = Tree<OptionNode<U>>;

pub struct OptionNode<U: Clone> {
    val: Option<U>,
    base: Base<Self>,
}
impl<U: Clone> Node for OptionNode<U> {
    type Value = U;
    type Link = Box<Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link {
        Box::new(Self {
            val: None,
            base: Base::new(l, r, black),
        })
    }
    fn new_leaf(val: Self::Value) -> Self::Link {
        Box::new(Self {
            val: Some(val),
            base: Base::new_leaf(),
        })
    }
    fn detach(p: Self::Link) -> (Self::Link, Self::Link) {
        p.base.detach()
    }
    fn make_root(mut p: Self::Link) -> Self::Link {
        p.base.make_root();
        p
    }
    fn val(&self) -> Self::Value {
        self.val.as_ref().unwrap().clone()
    }
    fn black(&self) -> bool {
        self.base.black()
    }
    fn height(&self) -> usize {
        self.base.height()
    }
    fn size(&self) -> usize {
        self.base.size()
    }
}

/// モノイドが載る平衡二分木.
/// 挿入, 削除, 分割, 併合, 区間取得, 二分探索 を O(log n) で行う.
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
pub type RBSegtree<M> = Tree<SegtreeNode<M>>;

pub struct SegtreeNode<M: Monoid> {
    val: M::S,
    base: Base<Self>,
}
impl<M: Monoid> Node for SegtreeNode<M> {
    type Value = M::S;
    type Link = Box<Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link {
        Box::new(Self {
            val: M::binary_operation(&l.val, &r.val),
            base: Base::new(l, r, black),
        })
    }
    fn new_leaf(val: Self::Value) -> Self::Link {
        Box::new(Self {
            val,
            base: Base::new_leaf(),
        })
    }
    fn detach(p: Self::Link) -> (Self::Link, Self::Link) {
        p.base.detach()
    }
    fn make_root(mut p: Self::Link) -> Self::Link {
        p.base.make_root();
        p
    }
    fn val(&self) -> Self::Value {
        self.val.clone()
    }
    fn black(&self) -> bool {
        self.base.black()
    }
    fn height(&self) -> usize {
        self.base.height()
    }
    fn size(&self) -> usize {
        self.base.size()
    }
}
impl<M: Monoid> MonoidNode for SegtreeNode<M> {
    type M = M;
}

/// 作用素モノイドが載る平衡二分木.
/// 挿入, 削除, 分割, 併合, 区間取得, 二分探索, 区間作用 を O(log n) で行う.
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
pub type RBLazySegtree<F> = Tree<LazySegtreeNode<F>>;

pub struct LazySegtreeNode<F: MapMonoid> {
    val: <F::M as Monoid>::S,
    lazy: F::F,
    base: Base<Self>,
}
impl<F: MapMonoid> Node for LazySegtreeNode<F> {
    type Value = <F::M as Monoid>::S;
    type Link = Box<Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link {
        Box::new(Self {
            val: F::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            base: Base::new(l, r, black),
        })
    }
    fn new_leaf(val: Self::Value) -> Self::Link {
        Box::new(Self {
            val,
            lazy: F::identity_map(),
            base: Base::new_leaf(),
        })
    }
    fn detach(p: Self::Link) -> (Self::Link, Self::Link) {
        let (mut l, mut r) = p.base.detach();
        l.val = F::mapping(&p.lazy, &l.val);
        r.val = F::mapping(&p.lazy, &r.val);
        l.lazy = F::composition(&p.lazy, &l.lazy);
        r.lazy = F::composition(&p.lazy, &r.lazy);
        (l, r)
    }
    fn make_root(mut p: Self::Link) -> Self::Link {
        p.base.make_root();
        p
    }
    fn val(&self) -> Self::Value {
        self.val.clone()
    }
    fn black(&self) -> bool {
        self.base.black()
    }
    fn height(&self) -> usize {
        self.base.height()
    }
    fn size(&self) -> usize {
        self.base.size()
    }
}
impl<F: MapMonoid> MonoidNode for LazySegtreeNode<F> {
    type M = F::M;
}
impl<F: MapMonoid> MapMonoidNode for LazySegtreeNode<F> {
    type F = F;
    fn apply(mut p: <Self as Node>::Link, f: F::F) -> <Self as Node>::Link {
        p.val = F::mapping(&f, &p.val);
        p.lazy = F::composition(&f, &p.lazy);
        p
    }
}

/// 作用素モノイドが載る, 区間反転が可能な平衡二分木.
/// 挿入, 削除, 分割, 併合, 区間取得, 二分探索, 区間作用, 区間反転 を O(log n) で行う.
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
pub type ReversibleRBLazySegtree<F> = Tree<ReversibleLazySegtreeNode<F>>;

pub struct ReversibleLazySegtreeNode<F: MapMonoid> {
    val: <F::M as Monoid>::S,
    lazy: F::F,
    rev: bool,
    base: Base<Self>,
}
impl<F: MapMonoid> Node for ReversibleLazySegtreeNode<F> {
    type Value = <F::M as Monoid>::S;
    type Link = Box<Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link {
        Box::new(Self {
            val: F::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            rev: false,
            base: Base::new(l, r, black),
        })
    }
    fn new_leaf(val: Self::Value) -> Self::Link {
        Box::new(Self {
            val,
            lazy: F::identity_map(),
            rev: false,
            base: Base::new_leaf(),
        })
    }
    fn detach(p: Self::Link) -> (Self::Link, Self::Link) {
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
    }
    fn make_root(mut p: Self::Link) -> Self::Link {
        p.base.make_root();
        p
    }
    fn val(&self) -> Self::Value {
        self.val.clone()
    }
    fn black(&self) -> bool {
        self.base.black()
    }
    fn height(&self) -> usize {
        self.base.height()
    }
    fn size(&self) -> usize {
        self.base.size()
    }
}
impl<F: MapMonoid> MonoidNode for ReversibleLazySegtreeNode<F> {
    type M = F::M;
}
impl<F: MapMonoid> MapMonoidNode for ReversibleLazySegtreeNode<F> {
    type F = F;
    fn apply(mut p: <Self as Node>::Link, f: F::F) -> <Self as Node>::Link {
        p.val = F::mapping(&f, &p.val);
        p.lazy = F::composition(&f, &p.lazy);
        p
    }
}
impl<F: MapMonoid> ReversibleNode for ReversibleLazySegtreeNode<F> {
    fn reverse(mut p: <Self as Node>::Link) -> <Self as Node>::Link {
        p.rev ^= true;
        p
    }
}

impl<T> Clone for Base<T>
where
    T: Node<Link = Rc<T>>,
{
    fn clone(&self) -> Self {
        Self {
            black: self.black,
            height: self.height,
            size: self.size,
            l: self.l.clone(),
            r: self.r.clone(),
        }
    }
}

/// 列を管理する永続平衡二分木.
/// 挿入, 削除, 分割, 併合 を O(log n), 複製 を O(1) で行う.
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
pub type PersistentRBTree<U> = Tree<PersistentOptionNode<U>>;

pub struct PersistentOptionNode<U: Clone> {
    val: Option<U>,
    base: Base<Self>,
}
impl<U: Clone> Clone for PersistentOptionNode<U> {
    fn clone(&self) -> Self {
        Self {
            val: self.val.clone(),
            base: self.base.clone(),
        }
    }
}
impl<U: Clone> Node for PersistentOptionNode<U> {
    type Value = U;
    type Link = Rc<Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link {
        Rc::new(Self {
            val: None,
            base: Base::new(l, r, black),
        })
    }
    fn new_leaf(val: Self::Value) -> Self::Link {
        Rc::new(Self {
            val: Some(val),
            base: Base::new_leaf(),
        })
    }
    fn detach(p: Self::Link) -> (Self::Link, Self::Link) {
        p.base.clone().detach()
    }
    fn make_root(mut p: Self::Link) -> Self::Link {
        if !p.base.black() {
            Rc::make_mut(&mut p).base.make_root();
        }
        p
    }
    fn val(&self) -> Self::Value {
        self.val.as_ref().unwrap().clone()
    }
    fn black(&self) -> bool {
        self.base.black()
    }
    fn height(&self) -> usize {
        self.base.height()
    }
    fn size(&self) -> usize {
        self.base.size()
    }
}

/// モノイドが載る永続平衡二分木.
/// 挿入, 削除, 分割, 併合, 区間取得, 二分探索 を O(log n), 複製 を O(1) で行う.
pub type PersistentRBSegtree<M> = Tree<PersistentSegtreeNode<M>>;

pub struct PersistentSegtreeNode<M: Monoid> {
    val: M::S,
    base: Base<Self>,
}
impl<M: Monoid> Clone for PersistentSegtreeNode<M> {
    fn clone(&self) -> Self {
        Self {
            val: self.val.clone(),
            base: self.base.clone(),
        }
    }
}
impl<M: Monoid> Node for PersistentSegtreeNode<M> {
    type Value = M::S;
    type Link = Rc<Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link {
        Rc::new(Self {
            val: M::binary_operation(&l.val, &r.val),
            base: Base::new(l, r, black),
        })
    }
    fn new_leaf(val: Self::Value) -> Self::Link {
        Rc::new(Self {
            val,
            base: Base::new_leaf(),
        })
    }
    fn detach(p: Self::Link) -> (Self::Link, Self::Link) {
        p.base.clone().detach()
    }
    fn make_root(mut p: Self::Link) -> Self::Link {
        if !p.base.black() {
            Rc::make_mut(&mut p).base.make_root();
        }
        p
    }
    fn val(&self) -> Self::Value {
        self.val.clone()
    }
    fn black(&self) -> bool {
        self.base.black()
    }
    fn height(&self) -> usize {
        self.base.height()
    }
    fn size(&self) -> usize {
        self.base.size()
    }
}
impl<M: Monoid> MonoidNode for PersistentSegtreeNode<M> {
    type M = M;
}

/// 作用素モノイドが載る永続平衡二分木.
/// 挿入, 削除, 分割, 併合, 区間取得, 二分探索, 区間作用 を O(log n), 複製 を O(1) で行う.
pub type PersistentRBLazySegtree<F> = Tree<PersistentLazySegtreeNode<F>>;

pub struct PersistentLazySegtreeNode<F: MapMonoid> {
    val: <F::M as Monoid>::S,
    lazy: F::F,
    base: Base<Self>,
}
impl<F: MapMonoid> Clone for PersistentLazySegtreeNode<F> {
    fn clone(&self) -> Self {
        Self {
            val: self.val.clone(),
            lazy: self.lazy.clone(),
            base: self.base.clone(),
        }
    }
}
impl<F: MapMonoid> Node for PersistentLazySegtreeNode<F> {
    type Value = <F::M as Monoid>::S;
    type Link = Rc<Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link {
        Rc::new(Self {
            val: F::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            base: Base::new(l, r, black),
        })
    }
    fn new_leaf(val: Self::Value) -> Self::Link {
        Rc::new(Self {
            val,
            lazy: F::identity_map(),
            base: Base::new_leaf(),
        })
    }
    fn detach(p: Self::Link) -> (Self::Link, Self::Link) {
        let (mut l, mut r) = p.base.clone().detach();
        Rc::make_mut(&mut l).val = F::mapping(&p.lazy, &l.val);
        Rc::make_mut(&mut r).val = F::mapping(&p.lazy, &r.val);
        Rc::make_mut(&mut l).lazy = F::composition(&p.lazy, &l.lazy);
        Rc::make_mut(&mut r).lazy = F::composition(&p.lazy, &r.lazy);
        (l, r)
    }
    fn make_root(mut p: Self::Link) -> Self::Link {
        if !p.base.black() {
            Rc::make_mut(&mut p).base.make_root();
        }
        p
    }
    fn val(&self) -> Self::Value {
        self.val.clone()
    }
    fn black(&self) -> bool {
        self.base.black()
    }
    fn height(&self) -> usize {
        self.base.height()
    }
    fn size(&self) -> usize {
        self.base.size()
    }
}
impl<F: MapMonoid> MonoidNode for PersistentLazySegtreeNode<F> {
    type M = F::M;
}
impl<F: MapMonoid> MapMonoidNode for PersistentLazySegtreeNode<F> {
    type F = F;
    fn apply(mut p: <Self as Node>::Link, f: F::F) -> <Self as Node>::Link {
        Rc::make_mut(&mut p).val = F::mapping(&f, &p.val);
        Rc::make_mut(&mut p).lazy = F::composition(&f, &p.lazy);
        p
    }
}

/// 作用素モノイドが載る, 区間反転が可能な永続平衡二分木.
/// 挿入, 削除, 分割, 併合, 区間取得, 二分探索, 区間作用, 区間反転 を O(log n), 複製 を O(1) で行う.
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
pub type PersistentReversibleRBLazySegtree<F> = Tree<PersistentReversibleLazySegtreeNode<F>>;

pub struct PersistentReversibleLazySegtreeNode<F: MapMonoid> {
    val: <F::M as Monoid>::S,
    lazy: F::F,
    rev: bool,
    base: Base<Self>,
}
impl<F: MapMonoid> Clone for PersistentReversibleLazySegtreeNode<F> {
    fn clone(&self) -> Self {
        Self {
            val: self.val.clone(),
            lazy: self.lazy.clone(),
            rev: self.rev.clone(),
            base: self.base.clone(),
        }
    }
}
impl<F: MapMonoid> Node for PersistentReversibleLazySegtreeNode<F> {
    type Value = <F::M as Monoid>::S;
    type Link = Rc<Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link {
        Rc::new(Self {
            val: F::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            rev: false,
            base: Base::new(l, r, black),
        })
    }
    fn new_leaf(val: Self::Value) -> Self::Link {
        Rc::new(Self {
            val,
            lazy: F::identity_map(),
            rev: false,
            base: Base::new_leaf(),
        })
    }
    fn detach(p: Self::Link) -> (Self::Link, Self::Link) {
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
    }
    fn make_root(mut p: Self::Link) -> Self::Link {
        if !p.base.black() {
            Rc::make_mut(&mut p).base.make_root();
        }
        p
    }
    fn val(&self) -> Self::Value {
        self.val.clone()
    }
    fn black(&self) -> bool {
        self.base.black()
    }
    fn height(&self) -> usize {
        self.base.height()
    }
    fn size(&self) -> usize {
        self.base.size()
    }
}
impl<F: MapMonoid> MonoidNode for PersistentReversibleLazySegtreeNode<F> {
    type M = F::M;
}
impl<F: MapMonoid> MapMonoidNode for PersistentReversibleLazySegtreeNode<F> {
    type F = F;
    fn apply(mut p: <Self as Node>::Link, f: F::F) -> <Self as Node>::Link {
        Rc::make_mut(&mut p).val = F::mapping(&f, &p.val);
        Rc::make_mut(&mut p).lazy = F::composition(&f, &p.lazy);
        p
    }
}
impl<F: MapMonoid> ReversibleNode for PersistentReversibleLazySegtreeNode<F> {
    fn reverse(mut p: <Self as Node>::Link) -> <Self as Node>::Link {
        Rc::make_mut(&mut p).rev ^= true;
        p
    }
}
