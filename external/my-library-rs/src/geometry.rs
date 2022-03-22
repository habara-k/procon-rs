use std::iter::Sum;
use std::ops::{Mul, Sub};

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub struct Point<T: Copy> {
    pub x: T,
    pub y: T,
}
impl<T: Copy> Point<T> {
    pub fn new(x: T, y: T) -> Self {
        Self { x, y }
    }
}
impl<T: Copy + Sub<Output = T>> Sub for Point<T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self::Output {
            x: self.x - rhs.x,
            y: self.y - rhs.y,
        }
    }
}

/// 外積を返す.
/// # Example
///
/// ```
/// use my_library_rs::*;
/// assert_eq!(cross(Point::new(4, 1), Point::new(3, 2)), 4*2 - 1*3);
/// ```
pub fn cross<T>(a: Point<T>, b: Point<T>) -> T
where
    T: Copy + Mul<Output = T> + Sub<Output = T>,
{
    a.x * b.y - a.y * b.x
}

/// 反時計回りの凸包を返す.
/// NOTE: (x座標,y座標)のtupleが一番小さい点を始点とする.
/// # Example
///
/// ```
/// use my_library_rs::*;
/// let ps = vec![Point::new(0, 0), Point::new(10, 0), Point::new(0, 10), Point::new(1, 1)];
/// assert_eq!(convex_hull(&ps), vec![Point::new(0, 0), Point::new(10, 0), Point::new(0, 10)]);
/// ```
pub fn convex_hull<T>(ps: &[Point<T>]) -> Vec<Point<T>>
where
    T: Copy + Ord + From<i32> + Sub<Output = T> + Mul<Output = T>,
{
    if ps.len() <= 1 {
        return ps.to_vec();
    }

    let mut order: Vec<usize> = (0..ps.len()).collect();
    order.sort_by_key(|&i| (ps[i].x, ps[i].y));

    let mut ch = vec![];
    for &i in order.iter() {
        while ch.len() >= 2
            && cross(
                ps[i] - ch[ch.len() - 1],
                ch[ch.len() - 1] - ch[ch.len() - 2],
            ) >= T::from(0)
        {
            ch.pop();
        }
        ch.push(ps[i]);
    }
    let n = ch.len();
    for &i in order.iter().rev().skip(1) {
        while ch.len() > n
            && cross(
                ps[i] - ch[ch.len() - 1],
                ch[ch.len() - 1] - ch[ch.len() - 2],
            ) >= T::from(0)
        {
            ch.pop();
        }
        ch.push(ps[i]);
    }

    ch.pop();
    ch
}

/// 多角形の符号付き面積の2倍を返す.
/// # Example
/// ```
/// use my_library_rs::*;
/// let ps = vec![Point::new(0, 0), Point::new(1, 0), Point::new(0, 1)];
/// assert_eq!(area_x2(&ps), 1);
///
/// let ps = vec![Point::new(0, 0), Point::new(0, 1), Point::new(1, 0)];
/// assert_eq!(area_x2(&ps), -1);
/// ```
pub fn area_x2<T>(ps: &[Point<T>]) -> T
where
    T: Copy + Mul<Output = T> + Sub<Output = T> + Sum,
{
    let n = ps.len();
    (0..n).map(|i| cross(ps[i], ps[(i + 1) % n])).sum::<T>()
}
