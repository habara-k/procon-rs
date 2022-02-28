const RED: bool = false;
const BLACK: bool = true;

#[derive(Clone)]
pub struct Base {
    black: bool,
    height: usize,
    size: usize,
}
impl Base {
    pub fn new(l: &Self, r: &Self, black: bool) -> Self {
        assert_eq!(l.height, r.height);
        assert!(l.black || black);
        assert!(r.black || black);
        Self {
            black,
            height: l.height + black as usize,
            size: l.size + r.size,
        }
    }
    pub fn new_leaf() -> Self {
        Self {
            black: false,
            height: 0,
            size: 1,
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
}

use std::ops::Deref;

pub trait Node {
    type Value: Clone;
    type Link: Deref<Target = Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link;
    fn new_leaf(val: Self::Value) -> Self::Link;
    fn detach(p: Self::Link) -> (Self::Link, Self::Link);
    fn make_root(p: Self::Link) -> Self::Link;
    fn val(&self) -> Self::Value;
    fn base(&self) -> &Base;

    fn black(&self) -> bool {
        self.base().black
    }
    fn height(&self) -> usize {
        self.base().height
    }
    fn size(&self) -> usize {
        self.base().size
    }
    fn is_leaf(&self) -> bool {
        self.base().is_leaf()
    }

    fn len(p: &Option<Self::Link>) -> usize {
        p.as_ref().map_or(0, |p| p.size())
    }
    fn merge(a: Option<Self::Link>, b: Option<Self::Link>) -> Option<Self::Link> {
        if a.is_none() {
            return b;
        }
        if b.is_none() {
            return a;
        }
        let (a, b) = (a.unwrap(), b.unwrap());
        Some(Self::merge_sub(Self::make_root(a), Self::make_root(b)))
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
            return (a, Self::merge(b, Some(r)));
        }
        if k > l.size() {
            let (a, b) = Self::split(Some(r), k - l.size());
            return (Self::merge(Some(l), a), b);
        }
        (Some(l), Some(r))
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
    fn collect_vec(mut p: Self::Link, v: &mut Vec<Self::Value>) -> Self::Link {
        if !p.is_leaf() {
            let black = p.black();
            let (mut l, mut r) = Self::detach(p);
            l = Self::collect_vec(l, v);
            r = Self::collect_vec(r, v);
            p = Self::new(l, r, black);
        } else {
            v.push(p.val());
        }
        p
    }
}

pub trait Root {
    type Node: Node;
    fn root(&mut self) -> &mut Option<<Self::Node as Node>::Link>;
    fn new(root: Option<<Self::Node as Node>::Link>) -> Self;
}

use std::mem;
pub trait Tree: Root + Sized {
    /// 要素数を返す.
    fn len(&mut self) -> usize {
        Self::Node::len(self.root())
    }
    /// `k` 番目に `val` を挿入する.
    fn insert(&mut self, k: usize, val: <Self::Node as Node>::Value) {
        assert!(k <= self.len());
        let root = mem::replace(self.root(), None);
        *self.root() = Self::Node::insert(root, k, val);
    }
    /// `k` 番目の要素を削除し, その値を返す.
    fn remove(&mut self, k: usize) -> <Self::Node as Node>::Value {
        assert!(k < self.len());
        let root = mem::replace(self.root(), None);
        let (root, val) = Self::Node::remove(root, k);
        *self.root() = root;
        val
    }
    /// [0,n) => [0,k), [k,n)
    fn split(mut self, k: usize) -> (Self, Self) {
        assert!(k <= self.len());
        let root = mem::replace(self.root(), None);
        let (l, r) = Self::Node::split(root, k);
        (Self::new(l), Self::new(r))
    }
    /// [0,n) => [0,l), [l,r), [r,n)
    fn split_range(mut self, l: usize, r: usize) -> (Self, Self, Self) {
        assert!(l <= r && r <= self.len());
        let root = mem::replace(self.root(), None);
        let (a, b, c) = Self::Node::split_range(root, l, r);
        (Self::new(a), Self::new(b), Self::new(c))
    }
    /// [0,k), [k,n) => [0,n)
    fn merge(&mut self, other: &mut Self) {
        let root = mem::replace(self.root(), None);
        *self.root() = Self::Node::merge(root, mem::replace(other.root(), None));
    }
    /// `k` 番目の要素を返す.
    fn get(&mut self, k: usize) -> <Self::Node as Node>::Value {
        assert!(k < self.len());
        let val = self.remove(k);
        self.insert(k, val.clone());
        val
    }
    fn collect_vec(&mut self) -> Vec<<Self::Node as Node>::Value> {
        if self.len() == 0 {
            return vec![];
        }
        let root = mem::replace(self.root(), None).unwrap();
        let mut v = vec![];
        *self.root() = Some(Self::Node::collect_vec(root, &mut v));
        v
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

        let root = mem::replace(self.root(), None);
        let (a, b, c) = Self::Node::split_range(root, l, r);

        let val = b.as_ref().unwrap().val();

        *self.root() = Self::Node::merge(Self::Node::merge(a, b), c);
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
        let root = mem::replace(self.root(), None);
        let (a, mut b, c) = Self::Node::split_range(root, l, r);

        b = Some(T::apply(b.unwrap(), f));

        *self.root() = Self::Node::merge(Self::Node::merge(a, b), c);
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
        let root = mem::replace(self.root(), None);
        let (a, mut b, c) = Self::Node::split_range(root, l, r);

        b = Some(T::reverse(b.unwrap()));

        *self.root() = Self::Node::merge(Self::Node::merge(a, b), c);
    }
}
