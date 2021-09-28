use std::f64;
use math::mean;
use petgraph::graphmap::DiGraphMap;
use std::collections::{HashSet, HashMap};
use petgraph::visit::{Reversed, Bfs, Dfs};
use petgraph::{Incoming, Outgoing};
use angora_common::tag::TagSeg;
use super::fparse::CfgFile;

pub type CmpId = u32;
pub type BbId = u32;
pub type CallSiteId = u32;
pub type Edge = (BbId, BbId);
pub type Score = u32;
pub type FixedBytes = Vec<(usize, u8)>;

const TARGET_SCORE: Score = 0;
const UNDEF_SCORE: Score = std::u32::MAX;


#[derive(Clone)]
pub struct ControlFlowGraph {
    graph: DiGraphMap<BbId, Score>,
    targets: HashSet<CmpId>,
    id_mapping: HashMap<BbId, CmpId>,
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
            id_mapping: data.id_mapping,
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
        info!("INIT ID mapping: {:?}", result.id_mapping);

        result
    }

    pub fn empty_new() -> ControlFlowGraph {
        let result = ControlFlowGraph {
            graph: DiGraphMap::new(),
            targets: HashSet::new(),
            id_mapping: HashMap::new(),
            solved_targets: HashSet::new(),
            indirect_edges: HashSet::new(),
            callsite_edges: HashMap::new(),
            callsite_dominators: HashMap::new(),
            dominator_cmps: HashSet::new(),
            magic_bytes: HashMap::new(),
        };

        result
    }


    pub fn add_edge(&mut self, edge: Edge) -> bool {
        let result = !self.has_edge(edge);
        #[cfg(test)]
        println!("Handling following edge: {:?}", edge);
        self.handle_new_edge(edge);
        debug!("Added CFG edge {:?} {}", edge, self.targets.contains(&edge.1));
        result
    }

    pub fn set_edge_indirect(&mut self, edge: Edge, callsite: CallSiteId) {
        self.indirect_edges.insert(edge);
        let entry = self.callsite_edges.entry(callsite).or_insert(HashSet::new());
        entry.insert(edge);
    }

    pub fn set_magic_bytes(&mut self, edge: Edge, buf: &Vec<u8>, offsets: &Vec<TagSeg>) {
        let mut fixed = vec![];
        let mut indices = HashSet::new();
        for tag in offsets {
            for i in tag.begin .. tag.end {
                indices.insert(i as usize);
            }
        }
        for i in indices {
            fixed.push((i, buf[i]));
        }
        self.magic_bytes.insert(edge, fixed);
    }

    pub fn get_magic_bytes(&self, edge: Edge) -> FixedBytes {
        if let Some(fixed) = self.magic_bytes.get(&edge) {
            return fixed.clone();
        }
        return vec![];
    }

    pub fn dominates_indirect_call(&self, cmp: CmpId) -> bool{
        self.dominator_cmps.contains(&cmp)
    }

    pub fn get_callsite_dominators(&self, cs: CallSiteId) -> HashSet<CmpId> {
        let res = self.callsite_dominators.get(&cs);
        debug!("GET CALLSITE DOM: {}, {:?}", cs, res);
        if let Some(s) = res {
            return s.clone();
        }
        let result = HashSet::new();
        return result;
    }

    pub fn get_cmp_from_bb(&self, bb: BbId) -> Option<CmpId> {
        if !self.id_mapping.is_empty() {
            if self.id_mapping.contains_key(&bb) {
                return Some(self.id_mapping[&bb]);
            }
        }
        None
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
        // #[cfg(test)]
        // println!("NEW SCORE for {:?}->{:?}: {:?}", src, dst, dst_score);
        self.propagate_score(src);
    }


    fn propagate_score(&mut self, bb: BbId) {

        let rev_graph = Reversed(&self.graph);
        let mut visitor = Bfs::new(rev_graph, bb);

        while let Some(visited) = visitor.next(&self.graph) {
            let new_score = self._score_for_cmp(visited);
            let mut predecessors = vec![];
            {
                let neighbors = self.graph.neighbors_directed(visited, Incoming);
                for n in neighbors {
                    predecessors.push(n);
                }
            }
            for p in predecessors {
                #[cfg(test)]
                println!("PRED (p): {:?}", p);
                #[cfg(test)]
                if p == 0 {
                    println!("NEW SCORE IN EDGE {:?}->{:?}: {:?}", p, visited, new_score);
                }
                // let mut weight = self.graph.edge_weight_mut(p, visited);
                self.graph.add_edge(p, visited, new_score);
            }
        }
        
    }
    

    pub fn has_edge(&self, edge: Edge) -> bool {
        let (a,b) = edge;
        self.graph.contains_edge(a, b)
    }

    pub fn has_score(&self, cmp: CmpId) -> bool {
        if self._score_for_cmp(cmp) != UNDEF_SCORE {
            return true;
        } 
        false
    }

    fn aggregate_score(ovals: Vec<Score>) -> Score {
        //Self::score_greedy(ovals)
        //Self::score_coverage(ovals)
        Self::score_harmonic_mean(ovals)
    }

    fn score_harmonic_mean(ovals: Vec<Score>) -> Score {
        if ovals.len() == 0 {
            return UNDEF_SCORE;
        }
        let vals = ovals.into_iter().filter(|v| *v != UNDEF_SCORE);
        let fvals : Vec<f64> = vals.into_iter().map(|x| x as f64).collect();
        if fvals.is_empty() {
            return UNDEF_SCORE;
        }
        // TODO add 1 if cmp
        return mean::harmonic(fvals.as_slice()) as u32;
    }

    #[allow(dead_code)]
    fn score_greedy(ovals: Vec<Score>) -> Score {
        let vals = ovals.into_iter().filter(|v| *v != UNDEF_SCORE);
        if let Some(v) = vals.min() {
            v + 1
        } else {
            UNDEF_SCORE
        }
    }

    #[allow(dead_code)]
    fn score_coverage(ovals: Vec<Score>) -> Score {
        if ovals.len() == 0 {
            return UNDEF_SCORE;
        }
        let vals = ovals.into_iter().filter(|v| *v != UNDEF_SCORE);
        let vals_norm = vals.into_iter().map(|v| if v == TARGET_SCORE {1} else {v});
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

    pub fn score_for_cmp_inp(&self, cmp: CmpId, inp: Vec<u8>) -> Score {
        let score = self._score_for_cmp_inp(cmp, inp);
        if score != UNDEF_SCORE {
            debug!("Calculated score: {}", score);
        }
        score
    }

    fn _score_for_cmp(&self, bb: BbId) -> Score {
        self._score_for_cmp_inp(bb, vec![])
    }

    fn _score_for_cmp_inp(&self, bb: BbId, inp: Vec<u8>) -> Score {
        // Get the cmpid of the bbid if there is one
        let cmp_opt = self.get_cmp_from_bb(bb);
        if let Some(cmp) = cmp_opt {
            if self.targets.contains(&cmp) {
                debug!("Calculate score for target: {}", cmp);
                return TARGET_SCORE;
            }
        }
        let mut neighbors = self.graph.neighbors_directed(bb, Outgoing);

        let mut scores = vec![];
        while let Some(n) = neighbors.next() {
            let edge = (bb, n);
            if !self._should_count_edge(edge, &inp) {
                debug!("Skipping count edge: {:?}", edge);
                continue;
            }
            debug!("Counting edge: {:?}", edge);
            if let Some(s) = self.graph.edge_weight(bb, n) {
                scores.push(*s);
            }
        }
        let aggregate = Self::aggregate_score(scores.clone());
        // println!("AGGREGATE THESE SCORES ({:?}): {:?}, RESULT: {:?}", bb, scores, aggregate);
        return aggregate;
    }

    fn _should_count_edge(&self, edge: Edge, inp: &Vec<u8>) -> bool {
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
    use super::*;
    use std::iter::FromIterator;

    fn test_new(targets: HashSet<CmpId>, id_mapping: HashMap<BbId, CmpId>) -> ControlFlowGraph {
        let result = ControlFlowGraph {
            graph: DiGraphMap::new(),
            targets: targets,
            id_mapping: id_mapping,
            solved_targets: HashSet::new(),
            indirect_edges: HashSet::new(),
            callsite_edges: HashMap::new(),
            callsite_dominators: HashMap::new(),
            dominator_cmps: HashSet::new(),
            magic_bytes: HashMap::new(),
        };

        result
    }

    #[test]
    fn cfg_basic() {
        // Create CFG
        let mut cfg = ControlFlowGraph::empty_new();
        let edges = vec![(10,20), (20,30), (10,40), (40,50), (20,30)];

        for e in edges.clone() {
            cfg.add_edge(e);
        }
    }
    
    #[test]
    fn cfg_target_mapping() {
        // Create CFG
        let target_vec = vec![1100, 1200];
        let targets = HashSet::from_iter(target_vec.iter().cloned());

        let id_mapping: HashMap<BbId, CmpId> = [(10, 1000), (50, 1100), (80, 1200)].iter().cloned().collect();

        let mut cfg = test_new(targets, id_mapping);
        let edges = vec![(0,10), (10, 20), (20,30), (30,40), (40,50), (10,60), (60,70), (70,80)];
        // let edges = vec![(0,10), (10,20)];

        println!("TARGETS: {:?}", cfg.targets);
        println!("ID_MAPPING: {:?}", cfg.id_mapping);
        // Test adding BBId edges
        for e in edges.clone() {
            cfg.add_edge(e);
        }
        for e in edges.clone() {
            let (from, to) = e;
            println!("weight for ({:?}, {:?}): {:?}", from, to, cfg.graph.edge_weight(from, to))
        }
    }
}

