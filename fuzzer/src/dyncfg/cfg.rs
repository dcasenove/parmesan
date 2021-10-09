use super::fparse::CfgFile;
use angora_common::tag::TagSeg;
use itertools::Itertools;
use math::mean;
use petgraph::graphmap::DiGraphMap;
use petgraph::visit::{Bfs, Dfs, Reversed};
use petgraph::{Incoming, Outgoing};
use std::collections::{HashMap, HashSet};
use std::f64;

pub type CmpId = u32;
pub type CallSiteId = u32;
pub type Edge = (CmpId, CmpId);
pub type Score = u32;
pub type FixedBytes = Vec<(usize, u8)>;

const TARGET_SCORE: Score = 0;
const UNDEF_SCORE: Score = std::u32::MAX;

#[derive(Clone)]
pub struct ControlFlowGraph {
    graph: DiGraphMap<CmpId, Score>,
    targets: HashSet<CmpId>,
    solved_targets: HashSet<CmpId>,
    indirect_edges: HashSet<Edge>,
    callsite_edges: HashMap<CallSiteId, HashSet<Edge>>,
    callsite_dominators: HashMap<CallSiteId, HashSet<CmpId>>,
    dominator_cmps: HashSet<CmpId>,
    magic_bytes: HashMap<Edge, FixedBytes>,
}

// A CFG of branches (CMPs)
impl ControlFlowGraph {
    //pub fn new(targets: HashSet<CmpId>) -> ControlFlowGraph {
    pub fn new(data: CfgFile) -> ControlFlowGraph {
        let mut dominator_cmps = HashSet::new();
        for s in data.callsite_dominators.values() {
            dominator_cmps.extend(s)
        }
        let mut result = ControlFlowGraph {
            graph: DiGraphMap::new(),
            targets: data.targets,
            solved_targets: HashSet::new(),
            indirect_edges: HashSet::new(),
            callsite_edges: HashMap::new(),
            callsite_dominators: data.callsite_dominators,
            dominator_cmps,
            magic_bytes: HashMap::new(),
        };

        for e in data.edges {
            result.add_edge(e);
        }

        info!("INIT CFG: dominators: {:?}", result.dominator_cmps);

        result
    }

    pub fn add_edge(&mut self, edge: Edge) -> bool {
        let result = !self.has_edge(edge);
        self.handle_new_edge(edge);
        debug!(
            "Added CFG edge {:?} {}",
            edge,
            self.targets.contains(&edge.1)
        );
        result
    }

    pub fn set_edge_indirect(&mut self, edge: Edge, callsite: CallSiteId) {
        self.indirect_edges.insert(edge);
        let entry = self
            .callsite_edges
            .entry(callsite)
            .or_insert(HashSet::new());
        entry.insert(edge);
    }

    pub fn set_magic_bytes(&mut self, edge: Edge, buf: &[u8], offsets: &[TagSeg]) {
        let mut fixed = vec![];
        let mut indices = HashSet::new();
        for tag in offsets {
            for i in tag.begin..tag.end {
                indices.insert(i as usize);
            }
        }
        for i in indices {
            fixed.push((i, buf[i]));
        }
        self.magic_bytes.insert(edge, fixed);
    }

    pub fn get_magic_bytes(&self, edge: Edge) -> impl Iterator<Item = (usize, u8)> + '_ {
        self.magic_bytes
            .get(&edge)
            .into_iter()
            .map(|v| v.iter())
            .flatten()
            .copied()
    }

    pub fn dominates_indirect_call(&self, cmp: CmpId) -> bool {
        self.dominator_cmps.contains(&cmp)
    }

    pub fn get_callsite_dominators(&self, cs: CallSiteId) -> impl Iterator<Item = CmpId> + '_ {
        let res = self.callsite_dominators.get(&cs);
        debug!("GET CALLSITE DOM: {}, {:?}", cs, res);
        res.into_iter().map(|map| map.iter()).flatten().copied()
    }

    pub fn remove_target(&mut self, cmp: CmpId) {
        if self.targets.remove(&cmp) {
            self.propagate_score(cmp);
            self.solved_targets.insert(cmp);
        }
    }

    pub fn is_target(&self, cmp: CmpId) -> bool {
        self.targets.contains(&cmp) || self.solved_targets.contains(&cmp)
    }

    fn handle_new_edge(&mut self, edge: Edge) {
        let (src, dst) = edge;

        // 1) Get score for dst
        let dst_score = self._score_for_cmp(dst);

        // 2) if src_score changed
        let old_src_score = self._score_for_cmp(src);

        // Insert edge in graph
        self.graph.add_edge(src, dst, dst_score);

        let new_src_score = self._score_for_cmp(src);

        if old_src_score == new_src_score {
            // No change in score
            return;
        }

        self.graph.add_edge(src, dst, dst_score);
        self.propagate_score(src);
    }

    fn propagate_score(&mut self, cmp: CmpId) {
        let rev_graph = Reversed(&self.graph);
        let mut visitor = Bfs::new(rev_graph, cmp);

        while let Some(visited) = visitor.next(&self.graph) {
            let new_score = self._score_for_cmp(visited);
            let predecessors = self.graph.neighbors_directed(visited, Incoming).collect_vec();
            for p in predecessors {
                self.graph.add_edge(p, visited, new_score);
            }
        }
    }

    pub fn has_edge(&self, edge: Edge) -> bool {
        let (a, b) = edge;
        self.graph.contains_edge(a, b)
    }

    pub fn has_score(&self, cmp: CmpId) -> bool {
        if self._score_for_cmp(cmp) != UNDEF_SCORE {
            return true;
        }
        false
    }

    fn aggregate_score(ovals: impl Iterator<Item = Score>) -> Score {
        //Self::score_greedy(ovals)
        //Self::score_coverage(ovals)
        Self::score_harmonic_mean(ovals)
    }

    fn score_harmonic_mean(ovals: impl Iterator<Item = Score>) -> Score {
        Self::no_alloc_harmonic_mean(ovals.filter(|v| *v != UNDEF_SCORE).map(|v| v as f64))
            .map(|float| float as u32 + 1)
            .unwrap_or(UNDEF_SCORE)
    }

    /// Calculates harmonic mean without allocation. Returns None if input is empty. Panics if some elements are 0.
    fn no_alloc_harmonic_mean(iter: impl Iterator<Item = f64>) -> Option<f64> {
        let mut count = 0usize;
        let temp = iter.fold(0., |a, b| {
            count += 1;
            a + 1. / b
        });
        if temp != 0. {
            Some(count as f64 / temp)
        } else {
            None
        }
    }

    #[allow(dead_code)]
    fn score_greedy(ovals: impl Iterator<Item = Score>) -> Score {
        ovals
            .filter(|v| *v != UNDEF_SCORE)
            .min()
            .map(|v| v + 1)
            .unwrap_or(UNDEF_SCORE)
    }

    #[allow(dead_code)]
    fn score_coverage(ovals: Vec<Score>) -> Score {
        if ovals.len() == 0 {
            return UNDEF_SCORE;
        }
        let vals = ovals.into_iter().filter(|v| *v != UNDEF_SCORE);
        let vals_norm = vals
            .into_iter()
            .map(|v| if v == TARGET_SCORE { 1 } else { v });
        vals_norm.sum()
    }

    pub fn has_path_to_target(&self, target: CmpId) -> bool {
        let mut dfs = Dfs::new(&self.graph, target);
        while let Some(visited) = dfs.next(&self.graph) {
            if self.targets.contains(&visited) {
                return true;
            }
        }
        false
    }

    pub fn score_for_cmp(&self, cmp: CmpId) -> Score {
        let score = self._score_for_cmp(cmp);
        if score != UNDEF_SCORE {
            debug!("Calculated score: {}", score);
        }
        score
    }

    pub fn score_for_cmp_inp(&self, cmp: CmpId, inp: &[u8]) -> Score {
        let score = self._score_for_cmp_inp(cmp, inp);
        if score != UNDEF_SCORE {
            debug!("Calculated score: {}", score);
        }
        score
    }

    fn _score_for_cmp(&self, cmp: CmpId) -> Score {
        self._score_for_cmp_inp(cmp, &[])
    }

    fn _score_for_cmp_inp(&self, cmp: CmpId, inp: &[u8]) -> Score {
        if self.targets.contains(&cmp) {
            debug!("Calculate score for target: {}", cmp);
            return TARGET_SCORE;
        }
        let mut neighbors = self.graph.neighbors_directed(cmp, Outgoing);

        let scores = neighbors.filter_map(|n| {
            let edge = (cmp, n);
            if !self._should_count_edge(edge, &inp) {
                debug!("Skipping count edge: {:?}", edge);
                return None;
            }
            debug!("Counting edge: {:?}", edge);
            self.graph.edge_weight(cmp, n).copied()
        });

        return Self::aggregate_score(scores);
    }

    fn _should_count_edge(&self, edge: Edge, inp: &[u8]) -> bool {
        if !self.indirect_edges.contains(&edge) {
            return true;
        }

        if let Some(fixed) = self.magic_bytes.get(&edge) {
            let mut equal = true;
            for (i, v) in fixed {
                if let Some(b) = inp.get(*i) {
                    if *b != *v {
                        equal = false;
                        break;
                    }
                }
            }
            return equal;
        }

        true
    }
}

#[cfg(test)]
mod tests {

    use std::path::Path;

    use crate::dyncfg::fparse::parse_targets_file;

    use super::*;

    #[test]
    fn cfg_basic() {
        // Create CFG
        //let targets = HashSet::new();
        let mut cfg = ControlFlowGraph::new(todo!());
        let edges = vec![(10, 20), (20, 30), (10, 40), (40, 50), (20, 30)];

        for e in edges.clone() {
            cfg.add_edge(e);
        }
    }

    #[test]
    fn test_load() {
        let parmesan_info = parse_targets_file(Path::new("test_files/targets.json"))
            .expect("Could not read cfg targets file");
        ControlFlowGraph::new(parmesan_info);
    }
}
