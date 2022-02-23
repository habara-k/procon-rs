use std::boxed::Box;
use std::marker::PhantomData;
use std::mem;

/// 赤黒木に載せるデータの抽象化
pub trait NodeData {
    type T: Clone;
    /// モノイドを載せる.
    fn on_connect(l: &Self::T, r: &Self::T) -> Self::T;
    /// 作用素モノイドを載せる.
    fn on_detach(data: &Self::T, l: &mut Self::T, r: &mut Self::T);
}

/// 赤黒木を実装するクラス
struct Node<D: NodeData> {
    l: Option<Box<Node<D>>>,
    r: Option<Box<Node<D>>>,
    len: usize,    // the number of leaves in the subtree rooted by this node.
    height: usize, // the black height of the subtree rooted by this node.
    black: bool,
    data: D::T,
}

impl<D: NodeData> Node<D> {
    /// Constants
    const RED: bool = false;
    const BLACK: bool = true;

    /// Constructors
    fn new_leaf(data: D::T) -> Box<Self> {
        Box::new(Self {
            len: 1,
            height: 1,
            data,
            black: Self::BLACK,
            l: None,
            r: None,
        })
    }
    fn connect(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self> {
        assert_eq!(l.height, r.height);
        assert!(l.black || black);
        assert!(r.black || black);
        Box::new(Self {
            len: l.len + r.len,
            height: l.height + black as usize,
            data: D::on_connect(&l.data, &r.data),
            black,
            l: Some(l),
            r: Some(r),
        })
    }
    pub fn build(data: &[D::T], l: usize, r: usize) -> Option<Box<Self>> {
        assert!(l <= r && r <= data.len());
        match r - l {
            0 => None,
            1 => Some(Self::new_leaf(data[l].clone())),
            _ => Self::merge(
                Self::build(data, l, (l + r) / 2),
                Self::build(data, (l + r) / 2, r),
            ),
        }
    }

    /// Accessors
    fn len(p: &Option<Box<Self>>) -> usize {
        if let Some(p) = p {
            p.len
        } else {
            0
        }
    }

    /// Split
    pub fn split_range(
        p: Option<Box<Self>>,
        l: usize,
        r: usize,
    ) -> (Option<Box<Self>>, Option<Box<Self>>, Option<Box<Self>>) {
        assert!(l <= r && r <= Self::len(&p));
        let (a, c) = Self::split(p, r);
        let (a, b) = Self::split(a, l);
        (a, b, c)
    }
    pub fn split(p: Option<Box<Self>>, k: usize) -> (Option<Box<Self>>, Option<Box<Self>>) {
        assert!(k <= Self::len(&p));
        if k == 0 {
            return (None, p);
        }
        if k == Self::len(&p) {
            return (p, None);
        }
        let p = p.unwrap();
        let (l, r) = Self::detach(p);
        if k < l.len {
            let (a, b) = Self::split(Some(l), k);
            return (a, Self::merge(b, Some(Self::as_root(r))));
        }
        if k > l.len {
            let (a, b) = Self::split(Some(r), k - l.len);
            return (Self::merge(Some(Self::as_root(l)), a), b);
        }
        (Some(Self::as_root(l)), Some(Self::as_root(r)))
    }

    /// Merge
    pub fn merge(a: Option<Box<Self>>, b: Option<Box<Self>>) -> Option<Box<Self>> {
        if a.is_none() {
            return b;
        }
        if b.is_none() {
            return a;
        }
        let (a, b) = (a.unwrap(), b.unwrap());
        assert!(a.black && b.black);
        return Some(Self::as_root(Self::merge_sub(a, b)));
    }
    fn merge_sub(a: Box<Self>, b: Box<Self>) -> Box<Self> {
        // # Require
        //     a.black == true, b.black == true
        // # Ensure
        //     return.height == max(a.height, b.height)
        //     [WARNING] return.black may be false!
        assert!(a.black);
        assert!(b.black);

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
                return Self::connect(Self::merge_sub(a, l), r, Self::BLACK);
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
                return Self::connect(Self::connect(c, lr, Self::RED), r, Self::BLACK);
            }

            return if r.black {
                // Rotate tree:
                //             (BLACK,h+1)                (BLACK,h+1)
                //             /    \                     /     \
                //         (RED,h)  r(BLACK,h)   =>   c(RED,h)  (RED,h)
                //             \                                /    \
                //   c(RED,h)   lr(BLACK,h)              lr(BLACK,h)  r(BLACK,h)
                Self::connect(c, Self::connect(lr, r, Self::RED), Self::BLACK)
            } else {
                // Change color:
                //             (BLACK,h+1)                   (RED,h+1)
                //             /    \                        /       \
                //         (RED,h)  r(RED,h)     =>      (BLACK,h+1)  r(BLACK,h+1)
                //             \                          /     \
                //   c(RED,h)   lr(BLACK,h)           c(RED,h)   lr(BLACK,h)
                Self::connect(
                    Self::connect(c, lr, Self::BLACK),
                    Self::as_root(r),
                    Self::RED,
                )
            };
        }
        if a.height > b.height {
            // Do the reverse of the above procedure.
            let (l, r) = Self::detach(a);
            if r.black {
                return Self::connect(l, Self::merge_sub(r, b), Self::BLACK);
            }

            let (rl, rr) = Self::detach(r);
            let c = Self::merge_sub(rr, b);
            if c.black {
                return Self::connect(l, Self::connect(rl, c, Self::RED), Self::BLACK);
            }

            return if l.black {
                Self::connect(Self::connect(l, rl, Self::RED), c, Self::BLACK)
            } else {
                Self::connect(
                    Self::as_root(l),
                    Self::connect(rl, c, Self::BLACK),
                    Self::RED,
                )
            };
        }

        // Connect directly:
        //         (RED,h)
        //         /     \
        //   a(BLACK,h)  b(BLACK,h)
        return Self::connect(a, b, Self::RED);
    }

    /// Utils
    fn as_root(p: Box<Self>) -> Box<Self> {
        if p.black {
            return p;
        }
        let (l, r) = Self::detach(p);
        Self::connect(l, r, Self::BLACK)
    }
    fn detach(p: Box<Self>) -> (Box<Self>, Box<Self>) {
        let (mut l, mut r) = (p.l.unwrap(), p.r.unwrap());
        D::on_detach(&p.data, &mut l.data, &mut r.data);
        (l, r)
    }
}

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
pub struct RBTree<T: Clone> {
    root: Option<Box<Node<RightData<T>>>>,
}

struct RightData<T>(PhantomData<fn() -> T>);
impl<T: Clone> NodeData for RightData<T> {
    type T = T;
    fn on_connect(_l: &Self::T, r: &Self::T) -> Self::T {
        r.clone()
    }
    fn on_detach(_data: &Self::T, _l: &mut Self::T, _r: &mut Self::T) {}
}

/// Constructors
impl<T: Clone> Default for RBTree<T> {
    fn default() -> Self {
        Self { root: None }
    }
}
impl<T: Clone + Default> RBTree<T> {
    pub fn new(n: usize) -> RBTree<T> {
        vec![T::default(); n].into()
    }
}
impl<T: Clone> From<Vec<T>> for RBTree<T> {
    fn from(v: Vec<T>) -> Self {
        Self {
            root: Node::<RightData<T>>::build(&v, 0, v.len()),
        }
    }
}

impl<T: Clone> RBTree<T> {
    pub fn len(&self) -> usize {
        Node::<RightData<T>>::len(&self.root)
    }
    pub fn insert(&mut self, k: usize, data: T) {
        assert!(k <= self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b) = Node::<RightData<T>>::split(root, k);
        self.root = Node::<RightData<T>>::merge(
            Node::<RightData<T>>::merge(a, Some(Node::<RightData<T>>::new_leaf(data))),
            b,
        );
    }
    pub fn remove(&mut self, k: usize) -> T {
        assert!(k < self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = Node::<RightData<T>>::split_range(root, k, k + 1);
        self.root = Node::<RightData<T>>::merge(a, c);
        b.unwrap().data
    }
    pub fn get(&mut self, k: usize) -> T {
        assert!(k <= self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = Node::<RightData<T>>::split_range(root, k, k + 1);
        let x = b.as_ref().unwrap().as_ref().data.clone();
        self.root = Node::<RightData<T>>::merge(Node::<RightData<T>>::merge(a, b), c);
        x
    }
}

impl<T: Clone + Ord> RBTree<T> {
    pub fn lower_bound(&mut self, data: T) -> usize {
        if self.root.is_none() {
            return 0;
        }

        let mut p = self.root.as_ref().unwrap();
        let mut k = 0;

        while let (Some(l), Some(r)) = (&p.l, &p.r) {
            if l.data < data {
                p = r;
                k += l.len;
            } else {
                p = l;
            }
        }

        k + (p.data < data) as usize
    }
}

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
    root: Option<Box<Node<MonoidData<M>>>>,
}

/// ac-library-rs と同じ形式
pub trait Monoid {
    type S: Clone;
    fn identity() -> Self::S;
    fn binary_operation(a: &Self::S, b: &Self::S) -> Self::S;
}

struct MonoidData<M>(PhantomData<fn() -> M>);
impl<M: Monoid> NodeData for MonoidData<M> {
    type T = M::S;
    fn on_connect(l: &Self::T, r: &Self::T) -> Self::T {
        M::binary_operation(l, r)
    }
    fn on_detach(_data: &Self::T, _l: &mut Self::T, _r: &mut Self::T) {}
}

/// Constructors
impl<M: Monoid> Default for RBSegtree<M> {
    fn default() -> Self {
        Self { root: None }
    }
}
impl<M: Monoid> RBSegtree<M> {
    pub fn new(n: usize) -> RBSegtree<M> {
        vec![M::identity(); n].into()
    }
}
impl<M: Monoid> From<Vec<M::S>> for RBSegtree<M> {
    fn from(v: Vec<M::S>) -> Self {
        Self {
            root: Node::<MonoidData<M>>::build(&v, 0, v.len()),
        }
    }
}

impl<M: Monoid> RBSegtree<M> {
    pub fn len(&self) -> usize {
        Node::<MonoidData<M>>::len(&self.root)
    }
    pub fn insert(&mut self, k: usize, data: M::S) {
        assert!(k <= self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b) = Node::<MonoidData<M>>::split(root, k);
        self.root = Node::<MonoidData<M>>::merge(
            Node::<MonoidData<M>>::merge(a, Some(Node::<MonoidData<M>>::new_leaf(data))),
            b,
        );
    }
    pub fn remove(&mut self, k: usize) -> M::S {
        assert!(k < self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = Node::<MonoidData<M>>::split_range(root, k, k + 1);
        self.root = Node::<MonoidData<M>>::merge(a, c);
        b.unwrap().data
    }
    pub fn get(&mut self, k: usize) -> M::S {
        assert!(k <= self.len());
        self.prod(k, k + 1)
    }

    pub fn prod(&mut self, l: usize, r: usize) -> M::S {
        assert!(l <= r && r <= self.len());
        if l == r {
            return M::identity();
        }

        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = Node::<MonoidData<M>>::split_range(root, l, r);

        let x = b.as_ref().unwrap().as_ref().data.clone();

        self.root = Node::<MonoidData<M>>::merge(Node::<MonoidData<M>>::merge(a, b), c);
        x
    }
}

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
pub struct RBLazySegtree<M: MapMonoid> {
    root: Option<Box<Node<MapMonoidData<M>>>>,
}

/// ac-library-rs と同じ形式
pub trait MapMonoid {
    type M: Monoid;
    type F: Clone;
    // type S = <Self::M as Monoid>::S;
    fn identity_element() -> <Self::M as Monoid>::S {
        Self::M::identity()
    }
    fn binary_operation(
        a: &<Self::M as Monoid>::S,
        b: &<Self::M as Monoid>::S,
    ) -> <Self::M as Monoid>::S {
        Self::M::binary_operation(a, b)
    }
    fn identity_map() -> Self::F;
    fn mapping(f: &Self::F, x: &<Self::M as Monoid>::S) -> <Self::M as Monoid>::S;
    fn composition(f: &Self::F, g: &Self::F) -> Self::F;
}

struct MapMonoidData<F>(PhantomData<fn() -> F>);
impl<F: MapMonoid> NodeData for MapMonoidData<F> {
    type T = (<F::M as Monoid>::S, F::F);
    fn on_connect((a, _): &Self::T, (b, _): &Self::T) -> Self::T {
        (F::binary_operation(a, b), F::identity_map())
    }
    fn on_detach((_, f): &Self::T, (b, g): &mut Self::T, (c, h): &mut Self::T) {
        *b = F::mapping(f, b);
        *c = F::mapping(f, c);
        *g = F::composition(f, g);
        *h = F::composition(f, h);
    }
}

/// Constructors
impl<F: MapMonoid> Default for RBLazySegtree<F> {
    fn default() -> Self {
        Self { root: None }
    }
}
impl<F: MapMonoid> RBLazySegtree<F> {
    pub fn new(n: usize) -> RBLazySegtree<F> {
        vec![F::identity_element(); n].into()
    }
}
impl<F: MapMonoid> From<Vec<<F::M as Monoid>::S>> for RBLazySegtree<F> {
    fn from(v: Vec<<F::M as Monoid>::S>) -> Self {
        let v: Vec<_> = v.iter().map(|e| (e.clone(), F::identity_map())).collect();
        Self {
            root: Node::<MapMonoidData<F>>::build(&v, 0, v.len()),
        }
    }
}

impl<F: MapMonoid> RBLazySegtree<F> {
    pub fn len(&self) -> usize {
        Node::<MapMonoidData<F>>::len(&self.root)
    }
    pub fn insert(&mut self, k: usize, data: <F::M as Monoid>::S) {
        assert!(k <= self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b) = Node::<MapMonoidData<F>>::split(root, k);
        self.root = Node::<MapMonoidData<F>>::merge(
            Node::<MapMonoidData<F>>::merge(
                a,
                Some(Node::<MapMonoidData<F>>::new_leaf((
                    data,
                    F::identity_map(),
                ))),
            ),
            b,
        );
    }
    pub fn remove(&mut self, k: usize) -> <F::M as Monoid>::S {
        assert!(k < self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = Node::<MapMonoidData<F>>::split_range(root, k, k + 1);
        self.root = Node::<MapMonoidData<F>>::merge(a, c);
        b.unwrap().data.0
    }
    pub fn get(&mut self, k: usize) -> <F::M as Monoid>::S {
        assert!(k <= self.len());
        self.prod(k, k + 1)
    }

    pub fn prod(&mut self, l: usize, r: usize) -> <F::M as Monoid>::S {
        assert!(l <= r && r <= self.len());
        if l == r {
            return F::identity_element();
        }

        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = Node::<MapMonoidData<F>>::split_range(root, l, r);

        let x = b.as_ref().unwrap().as_ref().data.clone().0;

        self.root = Node::<MapMonoidData<F>>::merge(Node::<MapMonoidData<F>>::merge(a, b), c);
        x
    }

    pub fn apply_range(&mut self, l: usize, r: usize, f: F::F) {
        assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }

        let root = mem::replace(&mut self.root, None);
        let (a, mut b, c) = Node::<MapMonoidData<F>>::split_range(root, l, r);

        let (data, lazy) = &mut b.as_mut().unwrap().data;

        *data = F::mapping(&f, data);
        *lazy = F::composition(&f, lazy);

        self.root = Node::<MapMonoidData<F>>::merge(Node::<MapMonoidData<F>>::merge(a, b), c);
    }
}
