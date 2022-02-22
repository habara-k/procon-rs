use std::mem::swap;

pub struct HLD {
    pub visit: Vec<usize>,
    pub leave: Vec<usize>,
    pub order: Vec<usize>,
    pub head: Vec<usize>,
    pub size: Vec<usize>,
    pub par: Vec<usize>,
    pub depth: Vec<usize>,
}

impl HLD {
    pub const NULL: usize = std::usize::MAX;
    pub fn new(g: &Vec<Vec<usize>>, root: usize) -> Self {
        let n = g.len();
        let mut hld = HLD {
            visit: vec![0; n],
            leave: vec![0; n],
            order: vec![0; n],
            head: vec![0; n],
            size: vec![1; n],
            par: vec![0; n],
            depth: vec![0; n],
        };
        hld.build(g, root);
        hld
    }
    fn build(&mut self, g: &Vec<Vec<usize>>, root: usize) {
        self.dfs(g, root, Self::NULL, 0);
        self.hld(g, root, root, &mut 0);
    }
    fn dfs(&mut self, g: &Vec<Vec<usize>>, u: usize, p: usize, d: usize) {
        self.par[u] = p;
        self.depth[u] = d;
        g[u].iter().filter(|&v| *v != p).for_each(|&v| {
            self.dfs(g, v, u, d + 1);
            self.size[u] += self.size[v];
        });
    }
    fn hld(&mut self, g: &Vec<Vec<usize>>, u: usize, h: usize, t: &mut usize) {
        self.head[u] = h;
        self.visit[u] = *t;
        self.order[*t] = u;
        *t += 1;

        let p = self.par[u];
        let heavy = *g[u]
            .iter()
            .filter(|&v| *v != p)
            .max_by_key(|&v| self.size[*v])
            .unwrap_or(&Self::NULL);
        if heavy != Self::NULL {
            self.hld(g, heavy, self.head[u], t);
        }
        g[u].iter()
            .filter(|&v| *v != p && *v != heavy)
            .for_each(|&v| self.hld(g, v, v, t));
    }

    pub fn lca(&self, mut u: usize, mut v: usize) -> usize {
        loop {
            if self.visit[u] > self.visit[v] {
                swap(&mut u, &mut v);
            }
            if self.head[u] == self.head[v] {
                return u;
            }
            v = self.par[self.head[v]];
        }
    }

    pub fn dist(&self, u: usize, v: usize) -> usize {
        self.depth[u] + self.depth[v] - 2 * self.depth[self.lca(u, v)]
    }
}