use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::ops::Add;

#[derive(Clone)]
pub struct Edge<T> {
    pub to: usize,
    pub cost: T,
}

pub fn dijkstra<T>(graph: &[Vec<Edge<T>>], s: usize, max: T) -> Vec<T>
where
    T: Copy + From<usize> + Ord + Add<Output = T>,
{
    let mut dist = vec![max; graph.len()];
    dist[s] = T::from(0);

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
