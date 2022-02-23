use std::boxed::Box;
use std::marker::PhantomData;
use std::mem;

/// 赤黒木に載せるデータの抽象化
pub trait Data {
    type T: Clone;
    /// モノイドを載せる.
    fn on_connect(l: &Self::T, r: &Self::T) -> Self::T;
    /// 作用素モノイドを載せる.
    fn on_detach(data: &Self::T, l: &mut Self::T, r: &mut Self::T);
}

/// 赤黒木を実装するクラス
struct Node<M>
where
    M: Data,
{
    l: Option<Box<Node<M>>>,
    r: Option<Box<Node<M>>>,
    len: usize,
    height: usize, // the black height of the subtree rooted by it.
    black: bool,
    data: M::T,
}

impl<M> Node<M>
where
    M: Data,
{
    /// Constants
    const RED: bool = false;
    const BLACK: bool = true;

    /// Constructors
    fn new_leaf(data: M::T) -> Box<Self> {
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
            data: M::on_connect(&l.data, &r.data),
            black,
            l: Some(l),
            r: Some(r),
        })
    }
    pub fn build(data: &Vec<M::T>, l: usize, r: usize) -> Option<Box<Self>> {
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
        M::on_detach(&p.data, &mut l.data, &mut r.data);
        (l, r)
    }
}

/// 列を管理する平衡二分木.
/// 挿入, 削除, 取得を O(log n) で行う.
///
/// # Example
/// ```
/// use my_library_rs::*;
///
/// let mut v: RBTree<u32> = vec![60, 20, 40, 50].into();
/// v.insert(0, 10);  // [10, 60, 20, 40, 50]
/// v.insert(3, 30);  // [10, 60, 20, 30, 40, 50]
/// v.remove(1);      // [10, 20, 30, 40, 50]
///
/// assert_eq!(v.len(), 5);
/// assert_eq!(v.get(0), 10);
/// assert_eq!(v.get(1), 20);
/// assert_eq!(v.get(2), 30);
/// assert_eq!(v.get(3), 40);
/// assert_eq!(v.get(4), 50);
/// ```
pub struct RBTree<T>
where
    T: Clone
{
    root: Option<Box<Node<OnlyLeaf<T>>>>,
}

struct OnlyLeaf<T>(PhantomData<fn() -> T>);
impl<T> Data for OnlyLeaf<T>
where
    T: Clone
{
    type T = T;
    fn on_connect(_l: &Self::T, r: &Self::T) -> Self::T {
        r.clone()
    }
    fn on_detach(_data: &Self::T, _l: &mut Self::T, _r: &mut Self::T) {}
}

impl<T> RBTree<T>
where
    T: Clone
{
    pub fn new() -> Self {
        Self { root: None }
    }
    pub fn len(&self) -> usize {
        <Node<OnlyLeaf<T>>>::len(&self.root)
    }
    pub fn insert(&mut self, k: usize, data: T) {
        assert!(k <= self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b) = <Node<OnlyLeaf<T>>>::split(root, k);
        self.root = <Node<OnlyLeaf<T>>>::merge(
            <Node<OnlyLeaf<T>>>::merge(a, Some(<Node<OnlyLeaf<T>>>::new_leaf(data))),
            b,
        );
    }
    pub fn remove(&mut self, k: usize) -> T {
        assert!(k < self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = <Node<OnlyLeaf<T>>>::split_range(root, k, k + 1);
        self.root = <Node<OnlyLeaf<T>>>::merge(a, c);
        b.unwrap().data
    }
    pub fn get(&mut self, k: usize) -> T {
        assert!(k <= self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = <Node<OnlyLeaf<T>>>::split_range(root, k, k + 1);
        let x = b.as_ref().unwrap().as_ref().data.clone();
        self.root = <Node<OnlyLeaf<T>>>::merge(<Node<OnlyLeaf<T>>>::merge(a, b), c);
        x
    }
}

impl<T> From<Vec<T>> for RBTree<T>
where
    T: Clone
{
    fn from(v: Vec<T>) -> Self {
        Self {
            root: <Node<OnlyLeaf<T>>>::build(&v, 0, v.len()),
        }
    }
}

/// モノイドが載る平衡二分木.
/// 挿入, 削除, 区間取得を O(log n) で行う.
///
/// # Example
/// ```
/// use my_library_rs::*;
/// use std::marker::PhantomData;
/// use num::Zero;
/// use std::ops::Add;
///
/// pub struct Additive<S>(PhantomData<fn() -> S>);
/// impl<S> Monoid for Additive<S>
///     where
///         S: Copy + Add<Output = S> + Zero,
/// {
///     type S = S;
///     fn identity() -> Self::S {
///         S::zero()
///     }
///     fn binary_operation(a: &Self::S, b: &Self::S) -> Self::S {
///         *a + *b
///     }
/// }
///
/// let mut seg: RBSegtree<Additive<u32>> = vec![1, 100, 1000, 0, 10000].into();
/// assert_eq!(seg.remove(3), 0);  // [1, 100, 1000, 10000]
/// seg.insert(1, 10);  // [1, 10, 100, 1000, 10000]
///
/// assert_eq!(seg.prod(0, 5), 11111);
/// assert_eq!(seg.prod(1, 4), 1110);
/// assert_eq!(seg.prod(3, 5), 11000);
/// ```
pub struct RBSegtree<M: Monoid>
{
    root: Option<Box<Node<MonoidData<M>>>>,
}

/// ac-library-rs と同じ形式
pub trait Monoid {
    type S: Clone;
    fn identity() -> Self::S;
    fn binary_operation(a: &Self::S, b: &Self::S) -> Self::S;
}

struct MonoidData<M>(PhantomData<fn() -> M>);
impl<M> Data for MonoidData<M>
    where
        M: Monoid,
{
    type T = M::S;
    fn on_connect(l: &Self::T, r: &Self::T) -> Self::T {
        M::binary_operation(l, r)
    }
    fn on_detach(_data: &Self::T, _l: &mut Self::T, _r: &mut Self::T) {}
}

impl<M> RBSegtree<M>
    where
        M: Monoid
{
    pub fn new() -> Self {
        Self { root: None }
    }
    pub fn len(&self) -> usize {
        <Node<MonoidData<M>>>::len(&self.root)
    }
    pub fn insert(&mut self, k: usize, data: M::S) {
        assert!(k <= self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b) = <Node<MonoidData<M>>>::split(root, k);
        self.root = <Node<MonoidData<M>>>::merge(
            <Node<MonoidData<M>>>::merge(a, Some(<Node<MonoidData<M>>>::new_leaf(data))),
            b,
        );
    }
    pub fn remove(&mut self, k: usize) -> M::S {
        assert!(k < self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = <Node<MonoidData<M>>>::split_range(root, k, k + 1);
        self.root = <Node<MonoidData<M>>>::merge(a, c);
        b.unwrap().data
    }
    pub fn get(&mut self, k: usize) -> M::S {
        assert!(k <= self.len());
        self.prod(k, k + 1)
    }

    pub fn prod(&mut self, l: usize, r: usize) -> M::S {
        assert!(l <= r && r <= self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = <Node<MonoidData<M>>>::split_range(root, l, r);
        let x = b.as_ref().unwrap().as_ref().data.clone();
        self.root = <Node<MonoidData<M>>>::merge(<Node<MonoidData<M>>>::merge(a, b), c);
        x
    }
}

impl<M> From<Vec<M::S>> for RBSegtree<M>
    where
        M: Monoid
{
    fn from(v: Vec<M::S>) -> Self {
        Self {
            root: <Node<MonoidData<M>>>::build(&v, 0, v.len()),
        }
    }
}
