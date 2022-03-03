use crate::algebra::{MapMonoid, Monoid};
use std::mem;
use std::ops::Deref;

const RED: bool = false;
const BLACK: bool = true;

pub struct Base<T: Node> {
    l: Option<T::Link>,
    r: Option<T::Link>,
    black: bool,
    height: usize,
    size: usize,
}

impl<T, L> Clone for Base<T>
where
    T: Node<Link = L>,
    L: Deref<Target = T> + Clone,
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

impl<T: Node> Base<T> {
    pub fn new(l: T::Link, r: T::Link, black: bool) -> Self {
        assert_eq!(l.height(), r.height());
        assert!(l.black() || black);
        assert!(r.black() || black);
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
        assert!(!self.is_leaf());
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

pub trait Node: Sized {
    type Value: Clone;
    type Link: Deref<Target = Self>;
    fn new(l: Self::Link, r: Self::Link, black: bool) -> Self::Link;
    fn new_leaf(val: Self::Value) -> Self::Link;
    fn detach(p: Self::Link) -> (Self::Link, Self::Link);
    fn make_root(p: Self::Link) -> Self::Link;
    fn val(&self) -> Self::Value;
    fn base(&self) -> &Base<Self>;

    fn black(&self) -> bool {
        self.base().black()
    }
    fn height(&self) -> usize {
        self.base().height()
    }
    fn size(&self) -> usize {
        self.base().size()
    }
    fn is_leaf(&self) -> bool {
        self.base().is_leaf()
    }

    fn len(p: &Option<Self::Link>) -> usize {
        p.as_ref().map_or(0, |p| p.size())
    }
    fn is_root(p: &Option<Self::Link>) -> bool {
        p.as_ref().map_or(true, |p| p.black())
    }
    fn merge(a: Option<Self::Link>, b: Option<Self::Link>) -> Option<Self::Link> {
        assert!(Self::is_root(&a) && Self::is_root(&b));
        if a.is_none() {
            return b;
        }
        if b.is_none() {
            return a;
        }
        let (a, b) = (a.unwrap(), b.unwrap());
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
    fn split(p: Option<Self::Link>, k: usize) -> (Option<Self::Link>, Option<Self::Link>) {
        assert!(k <= Self::len(&p));
        assert!(Self::is_root(&p));
        if k == 0 {
            return (None, p);
        }
        if k == Self::len(&p) {
            return (p, None);
        }
        let (l, r) = Self::detach(p.unwrap());
        let (l, r) = (Self::make_root(l), Self::make_root(r));
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
        assert!(Self::is_root(&p));
        let (p, c) = Self::split(p, r);
        let (a, b) = Self::split(p, l);
        (a, b, c)
    }
    fn insert(p: Option<Self::Link>, k: usize, val: Self::Value) -> Option<Self::Link> {
        assert!(k <= Self::len(&p));
        assert!(Self::is_root(&p));
        let (a, b) = Self::split(p, k);
        Self::merge(Self::merge(a, Some(Self::new_leaf(val))), b)
    }
    fn remove(p: Option<Self::Link>, k: usize) -> (Option<Self::Link>, Self::Value) {
        assert!(k < Self::len(&p));
        assert!(Self::is_root(&p));
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

pub struct Tree<T: Node> {
    root: Option<T::Link>,
}
impl<T: Node> Tree<T> {
    fn new(root: Option<T::Link>) -> Self {
        assert!(T::is_root(&root));
        Self { root }
    }
    pub fn len(&mut self) -> usize {
        T::len(&self.root)
    }
    pub fn insert(&mut self, k: usize, val: T::Value) {
        assert!(k <= self.len());
        let root = mem::replace(&mut self.root, None);
        self.root = T::insert(root, k, val);
    }
    pub fn remove(&mut self, k: usize) -> T::Value {
        assert!(k < self.len());
        let root = mem::replace(&mut self.root, None);
        let (root, val) = T::remove(root, k);
        self.root = root;
        val
    }
    pub fn split(mut self, k: usize) -> (Self, Self) {
        assert!(k <= self.len());
        let root = mem::replace(&mut self.root, None);
        let (l, r) = T::split(root, k);
        (Self::new(l), Self::new(r))
    }
    pub fn split_range(mut self, l: usize, r: usize) -> (Self, Self, Self) {
        assert!(l <= r && r <= self.len());
        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = T::split_range(root, l, r);
        (Self::new(a), Self::new(b), Self::new(c))
    }
    pub fn merge(&mut self, other: &mut Self) {
        let root = mem::replace(&mut self.root, None);
        self.root = T::merge(root, mem::replace(&mut other.root, None));
    }
    pub fn get(&mut self, k: usize) -> T::Value {
        assert!(k < self.len());
        let val = self.remove(k);
        self.insert(k, val.clone());
        val
    }
    pub fn collect_vec(&mut self) -> Vec<T::Value> {
        if self.len() == 0 {
            return vec![];
        }
        let root = mem::replace(&mut self.root, None).unwrap();
        let mut v = vec![];
        self.root = Some(T::collect_vec(root, &mut v));
        v
    }
}

pub trait MonoidNode: Node<Value = <<Self as MonoidNode>::M as Monoid>::S> {
    type M: Monoid;
    fn min_left<G: Fn(<Self::M as Monoid>::S) -> bool>(
        p: <Self as Node>::Link,
        g: G,
        k: &mut usize,
        sm: <Self::M as Monoid>::S,
    ) -> <Self as Node>::Link {
        if p.is_leaf() {
            if g(<Self::M as Monoid>::binary_operation(&p.val(), &sm)) {
                *k -= 1;
            }
            return p;
        }

        let black = p.black();
        let (mut l, mut r) = <Self as Node>::detach(p);

        let nxt = <Self::M as Monoid>::binary_operation(&r.val(), &sm);
        if g(nxt.clone()) {
            *k -= r.size();
            l = Self::min_left(l, g, k, nxt);
        } else {
            r = Self::min_left(r, g, k, sm);
        }

        <Self as Node>::new(l, r, black)
    }

    fn max_right<G: Fn(<Self::M as Monoid>::S) -> bool>(
        p: <Self as Node>::Link,
        g: G,
        k: &mut usize,
        sm: <Self::M as Monoid>::S,
    ) -> <Self as Node>::Link {
        if p.is_leaf() {
            if g(<Self::M as Monoid>::binary_operation(&sm, &p.val())) {
                *k += 1;
            }
            return p;
        }

        let black = p.black();
        let (mut l, mut r) = <Self as Node>::detach(p);

        let nxt = <Self::M as Monoid>::binary_operation(&sm, &l.val());
        if g(nxt.clone()) {
            *k += l.size();
            r = Self::max_right(r, g, k, nxt);
        } else {
            l = Self::max_right(l, g, k, sm);
        }

        <Self as Node>::new(l, r, black)
    }
}

impl<T: MonoidNode> Tree<T> {
    pub fn min_left<G: Fn(<T::M as Monoid>::S) -> bool>(&mut self, r: usize, g: G) -> usize {
        assert!(g(<T::M as Monoid>::identity()));
        assert!(r <= self.len());
        if r == 0 {
            return r;
        }
        let root = mem::replace(&mut self.root, None);
        let (mut a, b) = T::split(root, r);

        let mut k = r;
        a = Some(T::min_left(
            a.unwrap(),
            g,
            &mut k,
            <T::M as Monoid>::identity(),
        ));
        self.root = T::merge(a, b);
        k
    }

    pub fn max_right<G: Fn(<T::M as Monoid>::S) -> bool>(&mut self, l: usize, g: G) -> usize {
        assert!(g(<T::M as Monoid>::identity()));
        assert!(l <= self.len());
        if l == self.len() {
            return l;
        }
        let root = mem::replace(&mut self.root, None);
        let (a, mut b) = T::split(root, l);

        let mut k = l;
        b = Some(T::max_right(
            b.unwrap(),
            g,
            &mut k,
            <T::M as Monoid>::identity(),
        ));
        self.root = T::merge(a, b);
        k
    }

    pub fn prod(&mut self, l: usize, r: usize) -> <T::M as Monoid>::S {
        assert!(l <= r && r <= self.len());
        if l == r {
            return <T::M as Monoid>::identity();
        }

        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = T::split_range(root, l, r);

        let val = b.as_ref().unwrap().val();

        self.root = T::merge(T::merge(a, b), c);
        val
    }
}

pub trait MapMonoidNode:
    Node<Value = <<<Self as MapMonoidNode>::F as MapMonoid>::M as Monoid>::S>
{
    type F: MapMonoid;
    fn apply(p: <Self as Node>::Link, f: <Self::F as MapMonoid>::F) -> <Self as Node>::Link;
}

impl<T: MapMonoidNode> Tree<T> {
    pub fn apply_range(&mut self, l: usize, r: usize, f: <T::F as MapMonoid>::F) {
        assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }
        let root = mem::replace(&mut self.root, None);
        let (a, mut b, c) = T::split_range(root, l, r);

        b = Some(T::apply(b.unwrap(), f));

        self.root = T::merge(T::merge(a, b), c);
    }
}

pub trait ReversibleNode: Node {
    fn reverse(p: <Self as Node>::Link) -> <Self as Node>::Link;
}

impl<T: ReversibleNode> Tree<T> {
    pub fn reverse_range(&mut self, l: usize, r: usize) {
        assert!(l <= r && r <= self.len());
        if l == r {
            return;
        }
        let root = mem::replace(&mut self.root, None);
        let (a, mut b, c) = T::split_range(root, l, r);

        b = Some(T::reverse(b.unwrap()));

        self.root = T::merge(T::merge(a, b), c);
    }
}

impl<T: Node, L> Clone for Tree<T>
where
    T: Node<Link = L>,
    L: Deref<Target = T> + Clone,
{
    fn clone(&self) -> Self {
        Self::new(self.root.clone())
    }
}

impl<T, U> From<Vec<U>> for Tree<T>
where
    T: Node<Value = U>,
    U: Clone,
{
    fn from(v: Vec<U>) -> Self {
        Self::new(T::build(&v, 0, v.len()))
    }
}

impl<T: Node> Default for Tree<T> {
    fn default() -> Self {
        Self::new(None)
    }
}
