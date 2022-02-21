use std::cmp::Reverse;
use std::collections::BinaryHeap;
use num::{Bounded, Zero};

#[derive(Clone)]
pub struct Edge<T> {
    pub to: usize,
    pub cost: T,
}

pub fn dijkstra<T>(graph: &Vec<Vec<Edge<T>>>, s: usize) -> Vec<T>
where T: Copy + Bounded + Zero + Ord
{
    let mut dist = vec![T::max_value(); graph.len()];
    dist[s] = Zero::zero();

    let mut heap = BinaryHeap::new();
    heap.push((Reverse(dist[s]), s));

    while let Some((Reverse(d), u)) = heap.pop() {
        if d > dist[u] {
            continue;
        }
        for e in graph[u].iter() {
            if dist[e.to] > d + e.cost {
                dist[e.to] = d + e.cost;
                heap.push((Reverse(dist[e.to]), e.to));
            }
        }
    }

    dist
}
