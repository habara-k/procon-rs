use crate::algebra::{DefaultMonoid, MapMonoid, Monoid, NullMapMonoid};
use crate::rbtree_traits::{MapMonoidNode, MonoidNode, Node, ReversibleNode, Tree};
use std::rc::Rc;

/// 作用素モノイドが載る, 区間反転が可能な平衡二分木.
/// 挿入, 削除, 分割, 併合, 区間取得, 二分探索, 区間作用, 区間反転を O(log n) で行う.
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
///     fn identity_map() -> Self::F { 0 }
///     fn mapping(&f: &Self::F, &a: &<Self::M as Monoid>::S) -> <Self::M as Monoid>::S { a + f }
///     fn composition(&f: &Self::F, &g: &Self::F) -> Self::F { f + g }
/// }
///
/// let mut seg: RedBlackTree<u32, RangeMin, RangeAddRangeMin, Reversible> = vec![100, 1, 0, 10].into();
/// assert_eq!(seg.remove(2), 0);  // [100, 1, 10]
/// seg.insert(1, 1000);  // [100, 1000, 1, 10]
///
/// let (mut x, mut y) = seg.split(2);
/// assert_eq!(x.collect_vec(), vec![100, 1000]);
/// assert_eq!(y.collect_vec(), vec![1, 10]);
///
/// y.merge(&mut x);  // [1, 10, 100, 1000]
/// seg = y;
/// assert_eq!(seg.collect_vec(), vec![1, 10, 100, 1000]);
///
/// assert_eq!(seg.prod(1, 4), 10);
/// assert_eq!(seg.min_left(4, |x| x > 10), 2);
///
/// seg.apply_range(2, 4, 20);  // [1, 10, 120, 1020]
/// assert_eq!(seg.collect_vec(), vec![1, 10, 120, 1020]);
///
/// seg.reverse_range(1, 4); // [1, 1020, 120, 10];
/// assert_eq!(seg.collect_vec(), vec![1, 1020, 120, 10]);
///
/// let mut seg: RedBlackTree<i32> = vec![0, 3, 8, 2].into();
/// seg.insert(0, 10);  // [10, 0, 3, 8, 2]
/// seg.remove(4);  // [10, 0, 3, 8]
/// assert_eq!(seg.collect_vec(), vec![10, 0, 3, 8]);
pub type RedBlackTree<U, M = DefaultMonoid<U>, F = NullMapMonoid<U>, R = UnReversible> =
    Tree<RedBlackNode<U, M, F, R>>;

/// 作用素モノイドが載る, 区間反転が可能な永続平衡二分木.
/// 挿入, 削除, 分割, 併合, 区間取得, 二分探索, 区間作用, 区間反転を O(log n) で, 複製をO(1) で行う.
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
///     fn identity_map() -> Self::F { 0 }
///     fn mapping(&f: &Self::F, &a: &<Self::M as Monoid>::S) -> <Self::M as Monoid>::S { a + f }
///     fn composition(&f: &Self::F, &g: &Self::F) -> Self::F { f + g }
/// }
///
/// let mut seg: PersistentRedBlackTree<u32, RangeMin, RangeAddRangeMin, Reversible> = vec![100, 1, 0, 10].into();
/// assert_eq!(seg.remove(2), 0);  // [100, 1, 10]
/// seg.insert(1, 1000);  // [100, 1000, 1, 10]
///
/// let (mut x, mut y) = seg.split(2);
/// assert_eq!(x.collect_vec(), vec![100, 1000]);
/// assert_eq!(y.collect_vec(), vec![1, 10]);
///
/// y.merge(&mut x);  // [1, 10, 100, 1000]
/// seg = y;
/// assert_eq!(seg.collect_vec(), vec![1, 10, 100, 1000]);
///
/// assert_eq!(seg.prod(1, 4), 10);
/// assert_eq!(seg.min_left(4, |x| x > 10), 2);
///
/// seg.apply_range(2, 4, 20);  // [1, 10, 120, 1020]
/// assert_eq!(seg.collect_vec(), vec![1, 10, 120, 1020]);
///
/// seg.reverse_range(1, 4); // [1, 1020, 120, 10];
/// assert_eq!(seg.collect_vec(), vec![1, 1020, 120, 10]);
///
/// seg.merge(&mut seg.clone());
/// assert_eq!(seg.collect_vec(), vec![1, 1020, 120, 10, 1, 1020, 120, 10]);
///
/// let mut seg: PersistentRedBlackTree<i32> = vec![0, 3, 8, 2].into();
/// seg.insert(0, 10);  // [10, 0, 3, 8, 2]
/// seg.remove(4);  // [10, 0, 3, 8]
/// assert_eq!(seg.collect_vec(), vec![10, 0, 3, 8]);
///
/// let mut tmp = seg.clone();
/// let (mut x, mut y) = seg.split(2);
/// x.merge(&mut tmp);
/// x.merge(&mut y);
/// assert_eq!(x.collect_vec(), vec![10, 0, 10, 0, 3, 8, 3, 8]);
pub type PersistentRedBlackTree<U, M = DefaultMonoid<U>, F = NullMapMonoid<U>, R = UnReversible> =
    Tree<PersistentRedBlackNode<U, M, F, R>>;

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

impl<T: Node<Link = Rc<T>>> Clone for Base<T> {
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

pub trait ReverseFlag: Clone {
    fn default() -> Self;
    fn on(&self) -> bool {
        false
    }
    fn toggle(&mut self) {}
}

impl ReverseFlag for bool {
    fn default() -> Self {
        false
    }
    fn on(&self) -> bool {
        *self
    }
    fn toggle(&mut self) {
        *self ^= true;
    }
}
impl ReverseFlag for () {
    fn default() -> Self {
        ()
    }
}

pub type Reversible = bool;
pub type UnReversible = ();

pub struct RedBlackNode<U: Clone, M: Monoid<S = U>, F: MapMonoid<M = M>, R: ReverseFlag> {
    val: U,
    lazy: F::F,
    rev: R,
    base: Base<Self>,
}
impl<U: Clone, M: Monoid<S = U>, F: MapMonoid<M = M>, R: ReverseFlag> Node
    for RedBlackNode<U, M, F, R>
{
    type Value = U;
    type Link = Box<Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link {
        Self {
            val: M::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            rev: R::default(),
            base: Base::new(l, r, black),
        }
        .into()
    }
    fn new_leaf(val: Self::Value) -> Self::Link {
        Self {
            val,
            lazy: F::identity_map(),
            rev: R::default(),
            base: Base::new_leaf(),
        }
        .into()
    }
    fn detach(p: Self::Link) -> (Self::Link, Self::Link) {
        let (mut l, mut r) = p.base.detach();
        l.val = F::mapping(&p.lazy, &l.val);
        r.val = F::mapping(&p.lazy, &r.val);
        l.lazy = F::composition(&p.lazy, &l.lazy);
        r.lazy = F::composition(&p.lazy, &r.lazy);
        if p.rev.on() {
            l.rev.toggle();
            r.rev.toggle();
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
impl<U: Clone, M: Monoid<S = U>, F: MapMonoid<M = M>, R: ReverseFlag> MonoidNode
    for RedBlackNode<U, M, F, R>
{
    type M = M;
}
impl<U: Clone, M: Monoid<S = U>, F: MapMonoid<M = M>, R: ReverseFlag> MapMonoidNode
    for RedBlackNode<U, M, F, R>
{
    type F = F;
    fn apply(mut p: <Self as Node>::Link, f: F::F) -> <Self as Node>::Link {
        p.val = F::mapping(&f, &p.val);
        p.lazy = F::composition(&f, &p.lazy);
        p
    }
}
impl<U: Clone, M: Monoid<S = U>, F: MapMonoid<M = M>, R: ReverseFlag> ReversibleNode
    for RedBlackNode<U, M, F, R>
{
    fn reverse(mut p: <Self as Node>::Link) -> <Self as Node>::Link {
        p.rev.toggle();
        p
    }
}

pub struct PersistentRedBlackNode<U: Clone, M: Monoid<S = U>, F: MapMonoid<M = M>, R: ReverseFlag> {
    val: U,
    lazy: F::F,
    rev: R,
    base: Base<Self>,
}
impl<U: Clone, M: Monoid<S = U>, F: MapMonoid<M = M>, R: ReverseFlag> Clone
    for PersistentRedBlackNode<U, M, F, R>
{
    fn clone(&self) -> Self {
        Self {
            val: self.val.clone(),
            lazy: self.lazy.clone(),
            rev: self.rev.clone(),
            base: self.base.clone(),
        }
    }
}
impl<U: Clone, M: Monoid<S = U>, F: MapMonoid<M = M>, R: ReverseFlag> Node
    for PersistentRedBlackNode<U, M, F, R>
{
    type Value = U;
    type Link = Rc<Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link {
        Self {
            val: M::binary_operation(&l.val, &r.val),
            lazy: F::identity_map(),
            rev: R::default(),
            base: Base::new(l, r, black),
        }
        .into()
    }
    fn new_leaf(val: Self::Value) -> Self::Link {
        Self {
            val,
            lazy: F::identity_map(),
            rev: R::default(),
            base: Base::new_leaf(),
        }
        .into()
    }
    fn detach(p: Self::Link) -> (Self::Link, Self::Link) {
        let (mut l, mut r) = p.base.clone().detach();
        Rc::make_mut(&mut l).val = F::mapping(&p.lazy, &l.val);
        Rc::make_mut(&mut r).val = F::mapping(&p.lazy, &r.val);
        Rc::make_mut(&mut l).lazy = F::composition(&p.lazy, &l.lazy);
        Rc::make_mut(&mut r).lazy = F::composition(&p.lazy, &r.lazy);
        if p.rev.on() {
            Rc::make_mut(&mut l).rev.toggle();
            Rc::make_mut(&mut r).rev.toggle();
            return (r, l);
        }
        (l, r)
    }
    fn make_root(mut p: Self::Link) -> Self::Link {
        Rc::make_mut(&mut p).base.make_root();
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
impl<U: Clone, M: Monoid<S = U>, F: MapMonoid<M = M>, R: ReverseFlag> MonoidNode
    for PersistentRedBlackNode<U, M, F, R>
{
    type M = M;
}
impl<U: Clone, M: Monoid<S = U>, F: MapMonoid<M = M>, R: ReverseFlag> MapMonoidNode
    for PersistentRedBlackNode<U, M, F, R>
{
    type F = F;
    fn apply(mut p: <Self as Node>::Link, f: F::F) -> <Self as Node>::Link {
        Rc::make_mut(&mut p).val = F::mapping(&f, &p.val);
        Rc::make_mut(&mut p).lazy = F::composition(&f, &p.lazy);
        p
    }
}
impl<U: Clone, M: Monoid<S = U>, F: MapMonoid<M = M>, R: ReverseFlag> ReversibleNode
    for PersistentRedBlackNode<U, M, F, R>
{
    fn reverse(mut p: <Self as Node>::Link) -> <Self as Node>::Link {
        Rc::make_mut(&mut p).rev.toggle();
        p
    }
}
