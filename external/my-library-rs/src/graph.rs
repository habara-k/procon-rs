use std::collections::BinaryHeap;
use std::cmp::Reverse;

#[derive(Clone)]
pub struct Edge {
    pub to: usize,
    pub cost: u64,
}

pub fn dijkstra(graph: &Vec<Vec<Edge>>, s: usize) -> Vec<u64> {
    let mut dist = vec![std::u64::MAX; graph.len()];
    dist[s] = 0;

    let mut heap = BinaryHeap::new();
    heap.push((Reverse(0), s));

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
