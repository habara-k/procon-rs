use std::boxed::Box;
use std::mem;

#[derive(Clone)]
struct RBTreeNode<S> {
    l: Option<Box<RBTreeNode<S>>>,
    r: Option<Box<RBTreeNode<S>>>,
    size: usize,
    height: usize, // the black height of the subtree rooted by it.
    black: bool,
    data: Option<S>,
}

impl<S> RBTreeNode<S> {
    const RED: bool = false;
    const BLACK: bool = true;

    fn new_leaf(data: S) -> Box<Self> {
        Box::new(Self {
            size: 1,
            height: 1,
            l: None,
            r: None,
            black: Self::BLACK,
            data: Some(data),
        })
    }
    fn connect(l: Box<Self>, r: Box<Self>, black: bool) -> Box<Self> {
        assert_eq!(l.height, r.height);
        assert!(l.black || black);
        assert!(r.black || black);
        Box::new(Self {
            size: l.size + r.size,
            height: l.height + black as usize,
            l: Some(l),
            r: Some(r),
            black,
            data: None,
        })
    }

    fn size(p: &Option<Box<Self>>) -> usize {
        if let Some(p) = p {
            p.size
        } else {
            0
        }
    }

    pub fn split_range(
        p: Option<Box<Self>>,
        l: usize,
        r: usize,
    ) -> (Option<Box<Self>>, Option<Box<Self>>, Option<Box<Self>>) {
        assert!(l <= r && r <= Self::size(&p));
        let (a, c) = Self::split(p, r);
        let (a, b) = Self::split(a, l);
        (a, b, c)
    }

    pub fn split(p: Option<Box<Self>>, k: usize) -> (Option<Box<Self>>, Option<Box<Self>>) {
        assert!(k <= Self::size(&p));
        if k == 0 {
            return (None, p);
        }
        if k == Self::size(&p) {
            return (p, None);
        }
        let p = p.unwrap();
        let (l, r) = (p.l.unwrap(), p.r.unwrap());
        if k < l.size {
            let (a, b) = Self::split(Some(l), k);
            return (a, Self::merge(b, Some(Self::as_root(r))));
        }
        if k > l.size {
            let (a, b) = Self::split(Some(r), k - l.size);
            return (Self::merge(Some(Self::as_root(l)), a), b);
        }
        (Some(l), Some(r))
    }

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
            let (l, r) = (b.l.unwrap(), b.r.unwrap());
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

            let (ll, lr) = (l.l.unwrap(), l.r.unwrap());
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
            // Reverse of the above.
            let (l, r) = (a.l.unwrap(), a.r.unwrap());
            if r.black {
                return Self::connect(l, Self::merge_sub(r, b), Self::BLACK);
            }

            let (rl, rr) = (r.l.unwrap(), r.r.unwrap());
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

    fn as_root(mut p: Box<Self>) -> Box<Self> {
        p.black = Self::BLACK;
        p
    }
}


/// 列を管理する平衡二分木.
/// 値の挿入, ランダムアクセスを O(log n) で行う.
///
/// # Example
/// ```
/// use my_library_rs::*;
///
/// let mut v = RBTree::new();
///
/// v.insert(0, 10);  // [10]
/// v.insert(0, 20);  // [20, 10]
/// v.insert(1, 30);  // [20, 30, 10]
///
/// assert_eq!(v.get(0), 20);
/// assert_eq!(v.get(1), 30);
/// assert_eq!(v.get(2), 10);
/// ```
pub struct RBTree<S> {
    root: Option<Box<RBTreeNode<S>>>,
}

impl<S> RBTree<S> {
    pub fn new() -> Self {
        Self { root: None }
    }
    pub fn size(&self) -> usize {
        RBTreeNode::size(&self.root)
    }
    pub fn insert(&mut self, k: usize, data: S) {
        assert!(k <= self.size());
        let root = mem::replace(&mut self.root, None);
        let (a, b) = RBTreeNode::split(root, k);
        self.root = RBTreeNode::merge(RBTreeNode::merge(a, Some(RBTreeNode::new_leaf(data))), b);
    }
}

impl<S> RBTree<S>
where
    S: Clone,
{
    pub fn get(&mut self, k: usize) -> S {
        assert!(k <= self.size());
        let root = mem::replace(&mut self.root, None);
        let (a, b, c) = RBTreeNode::split_range(root, k, k + 1);
        let x = b.clone().unwrap().data.unwrap();
        self.root = RBTreeNode::merge(RBTreeNode::merge(a, b), c);
        x
    }
}
