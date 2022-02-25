use std::boxed::Box;
use std::mem;

const RED: bool = false;
const BLACK: bool = true;

pub trait NodeAttributes {
    fn l(&self) -> &Option<Box<Self>>;
    fn r(&self) -> &Option<Box<Self>>;
    fn height(&self) -> usize;
    fn black(&self) -> bool;
    fn size(&self) -> usize;

    fn len(p: &Option<Box<Self>>) -> usize {
        if let Some(p) = p {
            return p.size();
        }
        0
    }
}

pub trait NodeOps: NodeAttributes {
    fn connect(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self>;
    fn detach(p: Box<Self>) -> (Box<Self>, Box<Self>);
    fn as_root(p: Box<Self>) -> Box<Self> {
        if p.black() {
            return p;
        }
        let (l, r) = Self::detach(p);
        Self::connect(l, r, BLACK)
    }
}

pub trait Merge: NodeOps {
    fn merge(a: Option<Box<Self>>, b: Option<Box<Self>>) -> Option<Box<Self>> {
        if a.is_none() {
            return b;
        }
        if b.is_none() {
            return a;
        }
        let (a, b) = (a.unwrap(), b.unwrap());
        assert!(a.black() && b.black());
        return Some(Self::as_root(Self::merge_sub(a, b)));
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
            let (l, r) = Self::detach(b);
            //      b(BLACK,h+1)
            //       /     \
            //   l(*,h)    r(*,h)

            if l.black() {
                // Connect directly:
                //               (BLACK,h+1)
                //                /        \
                //   merge_sub(a,l)(*,h)   r(*,h)
                return Self::connect(Self::merge_sub(a, l), r, BLACK);
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
                return Self::connect(Self::connect(c, lr, RED), r, BLACK);
            }

            return if r.black() {
                // Rotate tree:
                //             (BLACK,h+1)                (BLACK,h+1)
                //             /    \                     /     \
                //         (RED,h)  r(BLACK,h)   =>   c(RED,h)  (RED,h)
                //             \                                /    \
                //   c(RED,h)   lr(BLACK,h)              lr(BLACK,h)  r(BLACK,h)
                Self::connect(c, Self::connect(lr, r, RED), BLACK)
            } else {
                // Change color:
                //             (BLACK,h+1)                   (RED,h+1)
                //             /    \                        /       \
                //         (RED,h)  r(RED,h)     =>      (BLACK,h+1)  r(BLACK,h+1)
                //             \                          /     \
                //   c(RED,h)   lr(BLACK,h)           c(RED,h)   lr(BLACK,h)
                Self::connect(Self::connect(c, lr, BLACK), Self::as_root(r), RED)
            };
        }
        if a.height() > b.height() {
            // Do the reverse of the above procedure.
            let (l, r) = Self::detach(a);
            if r.black() {
                return Self::connect(l, Self::merge_sub(r, b), BLACK);
            }

            let (rl, rr) = Self::detach(r);
            let c = Self::merge_sub(rr, b);
            if c.black() {
                return Self::connect(l, Self::connect(rl, c, RED), BLACK);
            }

            return if l.black() {
                Self::connect(Self::connect(l, rl, RED), c, BLACK)
            } else {
                Self::connect(Self::as_root(l), Self::connect(rl, c, BLACK), RED)
            };
        }

        // Connect directly:
        //         (RED,h)
        //         /     \
        //   a(BLACK,h)  b(BLACK,h)
        return Self::connect(a, b, RED);
    }
}

pub trait Split: Merge {
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
        let (l, r) = Self::detach(p.unwrap());
        if k < l.size() {
            let (a, b) = Self::split(Some(l), k);
            return (a, Self::merge(b, Some(Self::as_root(r))));
        }
        if k > l.size() {
            let (a, b) = Self::split(Some(r), k - l.size());
            return (Self::merge(Some(Self::as_root(l)), a), b);
        }
        (Some(Self::as_root(l)), Some(Self::as_root(r)))
    }
}

pub trait Value<T> {
    fn val(&self) -> T;
}
pub trait NewLeaf<T> {
    fn new_leaf(val: T) -> Box<Self>;
}

pub trait Insert<T>: Split + Value<T> + NewLeaf<T> {
    fn insert(p: Option<Box<Self>>, k: usize, val: T) -> Option<Box<Self>> {
        assert!(k <= Self::len(&p));
        let (a, b) = Self::split(p, k);
        Self::merge(Self::merge(a, Some(Self::new_leaf(val))), b)
    }
}
pub trait Remove<T>: Split + Value<T> {
    fn remove(p: Option<Box<Self>>, k: usize) -> (Option<Box<Self>>, T) {
        assert!(k < Self::len(&p));
        let (a, b, c) = Self::split_range(p, k, k + 1);
        (Self::merge(a, c), b.unwrap().val())
    }
}

pub trait BuildFromSeq<T: Clone>: Merge + NewLeaf<T> {
    fn build(v: &[T], l: usize, r: usize) -> Option<Box<Self>> {
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

pub trait Root<T: Clone> {
    type Node: Insert<T> + Remove<T> + BuildFromSeq<T>;
    fn root(&self) -> &Option<Box<Self::Node>>;
    fn mut_root(&mut self) -> &mut Option<Box<Self::Node>>;
    fn new(root: Option<Box<Self::Node>>) -> Self;

    fn len(&self) -> usize {
        Self::Node::len(self.root())
    }
    fn insert(&mut self, k: usize, val: T) {
        assert!(k <= self.len());
        let root = mem::replace(self.mut_root(), None);
        *self.mut_root() = Self::Node::insert(root, k, val);
    }
    fn remove(&mut self, k: usize) -> T {
        assert!(k < self.len());
        let root = mem::replace(self.mut_root(), None);
        let (root, val) = Self::Node::remove(root, k);
        *self.mut_root() = root;
        val
    }
    fn split(&mut self, k: usize, other: &mut Self) {
        let root = mem::replace(self.mut_root(), None);
        let (l, r) = Self::Node::split(root, k);
        *self.mut_root() = l;
        *other.mut_root() = r;
    }
    fn merge(&mut self, other: &mut Self) {
        let root = mem::replace(self.mut_root(), None);
        *self.mut_root() = Self::Node::merge(root, mem::replace(other.mut_root(), None));
    }
    fn get(&mut self, k: usize) -> T {
        assert!(k < self.len());
        let val = self.remove(k);
        self.insert(k, val.clone());
        val
    }
}

use crate::algebra::{MapMonoid, Monoid};

pub trait RangeFold<M: Monoid>: Root<M::S> {
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

pub trait LazyEval<F: MapMonoid>: Root<<F::M as Monoid>::S> {
    fn apply_range(&mut self, l: usize, r: usize, f: F::F) {
        assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }
        let root = mem::replace(self.mut_root(), None);
        let (a, mut b, c) = Self::Node::split_range(root, l, r);

        Self::apply(b.as_mut().unwrap(), f);

        *self.mut_root() = Self::Node::merge(Self::Node::merge(a, b), c);
    }
    fn apply(p: &mut Box<Self::Node>, f: F::F);
}

pub trait Reversible<T: Clone>: Root<T> {
    fn reverse_range(&mut self, l: usize, r: usize) {
        assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }
        let root = mem::replace(self.mut_root(), None);
        let (a, mut b, c) = Self::Node::split_range(root, l, r);

        Self::reverse(b.as_mut().unwrap());

        *self.mut_root() = Self::Node::merge(Self::Node::merge(a, b), c);
    }
    fn reverse(p: &mut Box<Self::Node>);
}
