use crate::{
    Engine, Proof, Witness,
    config::Config,
    gipsat::{SolverStatistic, TransysSolver},
    ic3::frame::FrameLemma,
    transys::{Transys, TransysCtx, TransysIf, frts::FrTs, unroll::TransysUnroll},
};
use activity::Activity;
use frame::{Frame, Frames};
use giputils::{grc::Grc, hash::{GHashMap, GHashSet}, logger::IntervalLogger};
use log::{Level, debug, info, trace};
use logicrs::{Lit, LitOrdVec, LitVec, Var, VarVMap, satif::Satif};
use mic::{DropVarParameter, MicType};
use proofoblig::{ProofObligation, ProofObligationQueue};
use rand::{Rng, SeedableRng, rngs::StdRng, seq::SliceRandom};
use statistic::Statistic;
use std::{collections::BTreeMap, time::Instant};
use var2name;
use secIC3::RelationData;
use std::collections::VecDeque;

mod activity;
mod aux;
mod frame;
mod mic;
mod proofoblig;
mod solver;
mod statistic;
mod verify;

pub struct IC3 {
    cfg: Config,
    ts: Transys,
    tsctx: Grc<TransysCtx>,
    solvers: Vec<TransysSolver>,
    inf_solver: TransysSolver,
    lift: TransysSolver,
    bad_ts: Grc<TransysCtx>,
    bad_solver: cadical::Solver,
    bad_lift: TransysSolver,
    bad_input: GHashMap<Var, Var>,
    frame: Frames,
    obligations: ProofObligationQueue,
    activity: Activity,
    statistic: Statistic,
    pre_lemmas: Vec<LitVec>,
    abs_cst: LitVec,
    bmc_solver: Option<(Box<dyn Satif>, TransysUnroll<Transys>)>,
    ots: Transys,
    rst: VarVMap,
    auxiliary_var: Vec<Var>,
    rng: StdRng,

    filog: IntervalLogger,
}

impl IC3 {
    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
    }

    fn extend(&mut self) {
        debug!("extending IC3 to level {}", self.solvers.len());
        if !self.cfg.ic3.no_pred_prop {
            self.bad_solver = cadical::Solver::new();
            self.bad_ts.load_trans(&mut self.bad_solver, true);
            for lemma in self.frame.inf.iter() {
                self.bad_solver.add_clause(&!lemma.cube());
            }
        }
        let mut solver = TransysSolver::new(&self.tsctx, true, self.rng.random());
        for lemma in self.frame.inf.iter() {
            solver.add_clause(&!lemma.cube());
        }
        for v in self.auxiliary_var.iter() {
            solver.add_domain(*v, true);
        }

        // Add the predicate semantics, i.e. !neq -> equivalence
        let relation = RelationData::get_relation_data();

        for var in self.ts.latch.iter() {
            if let Some(equiv_pred) = relation.get_equiv_predicate_new(var.0 as usize) {
                let predicate_var = Var::new(equiv_pred as usize);
                if relation.get_sym_var_new(var.0 as usize) == None {
                    trace!("No symmetric variable for var: {} {}", var.0, var);
                    continue;
                }
                let sym_var = Var::new(relation.get_sym_var_new(var.0 as usize).unwrap() as usize);

                // add constraint to the solver
                let mut constraint = LitVec::new_with(3);
                            constraint.push(var.lit());
                            constraint.push(!sym_var.lit());
                            constraint.push(!predicate_var.lit());
                            solver.add_clause(&!&constraint);
                            if !self.cfg.ic3.no_pred_prop {
                                self.bad_solver.add_clause(&!&constraint);
                            }
            }
        }

        self.solvers.push(solver);
        self.frame.push(Frame::new());
        if self.level() == 0 {
            for init in self.tsctx.init.clone() {
                self.add_lemma(0, !init, true, None);
            }
            let mut init = LitVec::new();
            for l in self.tsctx.latch.iter() {
                if self.tsctx.init_map[*l].is_none()
                    && let Some(v) = self.solvers[0].sat_value(l.lit())
                {
                    let l = l.lit().not_if(!v);
                    init.push(l);
                }
            }
            for i in init {
                self.ts.add_init(i.var(), Lit::constant(i.polarity()));
                self.tsctx.add_init(i.var(), Lit::constant(i.polarity()));
            }
        } else if self.level() == 1 {
            for cls in self.pre_lemmas.clone().iter() {
                self.add_lemma(1, !cls.clone(), true, None);
            }
        }
    }

    fn push_lemma(&mut self, frame: usize, mut cube: LitVec) -> (usize, LitVec) {
        let start = Instant::now();
        for i in frame + 1..=self.level() {
            if self.solvers[i - 1].inductive(&cube, true) {
                cube = self.solvers[i - 1].inductive_core().unwrap_or(cube);
            } else {
                return (i, cube);
            }
        }
        self.statistic.block.push_time += start.elapsed();
        (self.level() + 1, cube)
    }

    fn equiv_predicate_total_replacement(&mut self, frame: usize, cube: &LitVec) -> Vec<LitVec> {
        let relation = RelationData::get_relation_data();
        let mut predicate_cube = LitVec::new();
        let mut seen = GHashSet::new(); // Track variables already handled
        let mut added = GHashSet::new(); // Track vars added to predicate_cube

        let mut changed = false;
        for lit in cube.iter() {
            let var = lit.var();
            let polarity = lit.polarity();

            // Skip if already processed
            if seen.contains(&var) {
                continue;
            }
            seen.insert(var);

            // Check symmetric
            if relation.get_sym_var_new(var.0 as usize) == None {
                trace!("No symmetric variable for var: {} {}", var.0, var);
                continue; // Skip if no symmetric variable

            }
            let sym_var = Var::new(relation.get_sym_var_new(var.0 as usize).unwrap()); 
            seen.insert(sym_var);
            
            let temp_lit = sym_var.lit();
            let sym_lit = if cube.contains(&temp_lit) {
                Some(temp_lit)
            } else if cube.contains(&!temp_lit) {
                Some(!temp_lit)
            } else {
                None
            }; 
            // Check if symmetric literal is also in litvec
            if sym_lit.is_some(){
                trace!("Found symmetric variable: {} {}", var.0, var);
                let sym_lit = sym_lit.unwrap();
                // Opposite polarity?
                if polarity != sym_lit.polarity() {
                    trace!("Find opposite polarity for symmetric variable: {} {}", var.0, var);
                    // Replace with predicate variable
                    if relation.get_equiv_predicate_new(var.0 as usize) == None{
                        trace!("No equivalence predicate found for var: {} {}", var.0, var);
                        continue; // Skip if no equivalence predicate
                    }
                    if let Some(pred_var) = relation.get_equiv_predicate_new(var.0 as usize).map(Var::new) {
                        if added.insert(pred_var) {
                            predicate_cube.push(pred_var.lit());
                            changed = true;
                        }
                    }
                    continue; // Skip adding original pair
                }
            }

            // Add original literal if not already added
            if added.insert(var) {
                predicate_cube.push(*lit);
            }
        }
        let mut result: Vec<LitVec> = Vec::new();

        if changed{
            let original_lemma = LitOrdVec::new(cube.clone());
            let predicate_lemma = LitOrdVec::new(predicate_cube.clone());
            trace!("trying equivalence predicate replacement frame:{frame}, {original_lemma} -> {predicate_lemma}");
            if self.blocked_with_ordered(frame, &predicate_cube, false, true){
                trace!("Successful Replacement");
                if let Some(core) = self.solvers[frame - 1].inductive_core()
                {
                    result.push(core);
                }
                else {
                    result.push(predicate_cube);
                }
                if (self.statistic.max_predicates == 0) {
                    self.statistic.max_predicates = 1;
                }
            }
            else {
                result.push(cube.clone());
            }
        }

        result
    }

    /// Perform MIC by replacing variables with their equivalence predicates
    fn equiv_predicate_iterative_replacement(&mut self, frame: usize, mut cube: &LitVec) -> Vec<LitVec>{
        let relation = RelationData::get_relation_data();
        let mut seen_predicates = GHashSet::new();
        let mut pred_to_lits: GHashMap<usize, Vec<Lit>> = GHashMap::default();
        let mut cube = cube.clone();

        // Step 1: Group literals in the cube by their equivalence predicate (if any)
        for lit in &cube {
            if let Some(pred_id) = relation.get_equiv_predicate_new(lit.var().0 as usize) {
                pred_to_lits.entry(pred_id).or_default().push(*lit);
            }
        }

        let mut result: Vec<LitVec> = Vec::new();
        let mut pred_num = 0;
        // Step 2: Try one replacement per predicate group
        for (pred_id, lits) in pred_to_lits.into_iter() {
            if seen_predicates.contains(&pred_id) {
                continue;
            }
            seen_predicates.insert(pred_id);

            let mut to_remove = GHashSet::new();
            let mut matched = false;
            

            // Step 2a: Pairwise polarity check between symmetric bits
            for &lit in &lits {
                let var = lit.var();
                if let Some(sym_id) = relation.get_sym_var_new(var.0 as usize) {
                    let sym_var = Var::new(sym_id);
                    let sym_lit = sym_var.lit();

                    // Determine the polarity of the symmetric literal to match
                    let target_lit = if lit.polarity() { !sym_lit } else { sym_lit };

                    if cube.contains(&target_lit) {
                        matched = true;
                        to_remove.insert(var);
                        to_remove.insert(sym_var);
                    }
                }
            }

            // Step 3: Attempt generalization if at least one pair matched
            if matched {
                let pred_lit = Var::new(pred_id).lit();
                let mut new_cube: LitVec = cube.iter()
                    .filter(|l| !to_remove.contains(&l.var()))
                    .cloned()
                    .collect();
                new_cube.push(pred_lit);

                if self.blocked_with_ordered(frame, &new_cube, false, true) {
                    trace!("Successful equiv predicate replacement: {:?} → {:?}", cube, new_cube);
                    if let Some(core) = self.solvers[frame - 1].inductive_core()
                    {
                        cube = core;
                    }
                    else {
                        cube = new_cube;
                    }
                    pred_num += 1;
                    }
            }
        }
        if pred_num > self.statistic.max_predicates{
            self.statistic.max_predicates = pred_num;
        }
        result.push(cube);
        result
    }

    fn equiv_predicate_exhaustive_replacement(
        &mut self, 
        frame: usize, 
        cube: &LitVec
    )-> Vec<LitVec> {
        let relation = RelationData::get_relation_data();
        let mut pred_to_lits: GHashMap<usize, Vec<Lit>> = GHashMap::default();

        // Step 1: Group literals in the cube by their equivalence predicate (if any)
        for &lit in cube {
            if let Some(pred_id) = relation.get_equiv_predicate_new(lit.var().0 as usize) {
                let var = lit.var();
                if let Some(sym_id) = relation.get_sym_var_new(var.0 as usize){
                    let sym_var = Var::new(sym_id);
                    let sym_lit = sym_var.lit();
                    // Determine the polarity of the symmetric literal to match
                    let target_lit = if lit.polarity() { !sym_lit } else { sym_lit };

                    if cube.contains(&target_lit){
                        pred_to_lits.entry(pred_id).or_default().push(lit);
                    }
                }
            }
        }
        // Sort by the number of literals corresponding to every predicate
        // So the resultant cube will be 
        // pred_to_lits = pred_to_lits.into_iter()
        // .sorted_by_key(|(_, lits)| lits.len())
        // .collect();

        let num_preds = pred_to_lits.len();
        if num_preds > self.statistic.max_predicates{
            self.statistic.max_predicates = num_preds;
        }
        let mut replacement_queue: VecDeque<Vec<bool>> = VecDeque::new();
        replacement_queue.push_back(vec! [true; num_preds]);
        let mut replacement_tried: GHashSet<Vec<bool>> = GHashSet::new();


        let mut result: Vec<LitVec> = Vec::new();
        while let Some(replacement) = replacement_queue.pop_front() {
            if replacement.iter().all(|&b| !b) {
                continue;
            }
            let mut new_cube: LitVec = cube.clone();

            // Apply the replacement
            for (i, (pred_id, lits)) in pred_to_lits.iter().enumerate() {
                if replacement[i] {
                    // Remove all lits in this predicate group
                    new_cube.retain(|l| !lits.contains(l));
                    
                    // Add the predicate literal
                    let pred_lit = Var::new(*pred_id).lit();
                    new_cube.push(pred_lit);
                }
            }

            let original_lemma = LitOrdVec::new(cube.clone());
            let predicate_lemma = LitOrdVec::new(new_cube.clone());
            trace!("trying equivalence predicate replacement frame:{frame}, {original_lemma} -> {predicate_lemma}");
            
            if self.blocked_with_ordered(frame, &new_cube, false, true) {
                trace!("Successful Replacement");
                if let Some(core) = self.solvers[frame - 1].inductive_core()
                {
                    result.push(core);
                }
                else {
                    result.push(new_cube);
                }
            }
            else {
                for (i, &val) in replacement.iter().enumerate() {
                    if val {
                        let mut new_replacement = replacement.clone();
                        new_replacement[i] = false;
                        if !replacement_tried.contains(&new_replacement){
                            replacement_queue.push_back(new_replacement);
                        }
                    }
                }
            }

            replacement_tried.insert(replacement);


        }


        result
    }

    fn generalize(&mut self, mut po: ProofObligation, mic_type: MicType) -> bool {
        let Some(mut mic) = self.solvers[po.frame - 1].inductive_core() else {
            assert!(self.tsctx.cube_subsume_init(&po.lemma));
            po.frame += 1;
            self.add_obligation(po.clone());
            return self.add_lemma(po.frame - 1, po.lemma.cube().clone(), false, Some(po));
        };
        mic = self.mic(po.frame, mic, &[], mic_type);
        if self.cfg.equiv_predicate{
            let mut result = Vec::new();
            if self.cfg.iterative_predicate_replacement {
                result = self.equiv_predicate_iterative_replacement(po.frame, &mic);
            }
            else if self.cfg.exhaustive_predicate_replacement {
                result = self.equiv_predicate_exhaustive_replacement(po.frame, &mic);
            }
            else {
                result = self.equiv_predicate_total_replacement(po.frame, &mic);
            }
            let mut max_frame = 0;
            for cube in result {
                let (frame, mic) = self.push_lemma(po.frame, cube);
                if self.add_lemma(frame - 1, mic.clone(), false, Some(po.clone())) {
                return true;
            }
                if (frame > max_frame){
                    max_frame = frame;
                }
            }
            self.statistic.avg_po_cube_len += po.lemma.len();
            po.push_to(max_frame);
            self.add_obligation(po.clone());
        }
        else {
            let (frame, mic) = self.push_lemma(po.frame, mic);
            self.statistic.avg_po_cube_len += po.lemma.len();
            po.push_to(frame);
            self.add_obligation(po.clone());
            if self.add_lemma(frame - 1, mic.clone(), false, Some(po)) {
                return true;
            }
        }
        false
    }

    fn block(&mut self) -> Option<bool> {
        while let Some(mut po) = self.obligations.pop(self.level()) {
            if po.removed {
                continue;
            }
            if self.tsctx.cube_subsume_init(&po.lemma) {
                if self.cfg.ic3.abs_cst {
                    self.add_obligation(po.clone());
                    if let Some(c) = self.check_witness_by_bmc(po.clone()) {
                        for c in c {
                            assert!(!self.abs_cst.contains(&c));
                            self.abs_cst.push(c);
                        }
                        info!("abs cst len: {}", self.abs_cst.len(),);
                        self.obligations.clear();
                        for f in self.frame.iter_mut() {
                            for l in f.iter_mut() {
                                l.po = None;
                            }
                        }
                        continue;
                    } else {
                        return Some(false);
                    }
                } else if po.frame > 0 {
                    debug_assert!(!self.solvers[0].solve(&po.lemma));
                } else {
                    self.add_obligation(po.clone());
                    return Some(false);
                }
            }
            if let Some((bf, _)) = self.frame.trivial_contained(Some(po.frame), &po.lemma) {
                if let Some(bf) = bf {
                    po.push_to(bf + 1);
                    self.add_obligation(po);
                }
                continue;
            }
            debug!("{}", self.frame.statistic(false));
            po.bump_act();
            let blocked_start = Instant::now();
            let blocked = self.blocked_with_ordered(po.frame, &po.lemma, false, false);
            self.statistic.block.blocked_time += blocked_start.elapsed();
            if blocked {
                let mic_type = if self.cfg.ic3.dynamic {
                    if let Some(mut n) = po.next.as_mut() {
                        let mut act = n.act;
                        for _ in 0..2 {
                            if let Some(nn) = n.next.as_mut() {
                                n = nn;
                                act = act.max(n.act);
                            } else {
                                break;
                            }
                        }
                        const CTG_THRESHOLD: f64 = 10.0;
                        const EXCTG_THRESHOLD: f64 = 40.0;
                        let (limit, max, level) = match act {
                            EXCTG_THRESHOLD.. => {
                                let limit = ((act - EXCTG_THRESHOLD).powf(0.3) * 2.0 + 5.0).round()
                                    as usize;
                                (limit, 5, 1)
                            }
                            CTG_THRESHOLD..EXCTG_THRESHOLD => {
                                let max = (act - CTG_THRESHOLD) as usize / 10 + 2;
                                (1, max, 1)
                            }
                            ..CTG_THRESHOLD => (0, 0, 0),
                            _ => panic!(),
                        };
                        let p = DropVarParameter::new(limit, max, level);
                        MicType::DropVar(p)
                    } else {
                        MicType::DropVar(Default::default())
                    }
                } else {
                    MicType::from_config(&self.cfg)
                };
                if self.generalize(po, mic_type) {
                    return None;
                }
            } else {
                let (model, inputs) = self.get_pred(po.frame, true);
                self.add_obligation(ProofObligation::new(
                    po.frame - 1,
                    LitOrdVec::new(model),
                    vec![inputs],
                    po.depth + 1,
                    Some(po.clone()),
                ));
                self.add_obligation(po);
            }
        }
        Some(true)
    }

    #[allow(unused)]
    fn trivial_block_rec(
        &mut self,
        frame: usize,
        lemma: LitOrdVec,
        constraint: &[LitVec],
        limit: &mut usize,
        parameter: DropVarParameter,
    ) -> bool {
        if frame == 0 {
            return false;
        }
        if self.tsctx.cube_subsume_init(&lemma) {
            return false;
        }
        if *limit == 0 {
            return false;
        }
        *limit -= 1;
        loop {
            if self.blocked_with_ordered_with_constrain(
                frame,
                &lemma,
                false,
                true,
                constraint.to_vec(),
            ) {
                let mut mic = self.solvers[frame - 1].inductive_core().unwrap();
                mic = self.mic(frame, mic, constraint, MicType::DropVar(parameter));
                if self.cfg.equiv_predicate {
                    let mut result = Vec::new();
                    if self.cfg.iterative_predicate_replacement {
                        result = self.equiv_predicate_iterative_replacement(frame, &mic);
                    }
                    else if self.cfg.exhaustive_predicate_replacement {
                        result = self.equiv_predicate_exhaustive_replacement(frame, &mic);
                    }
                    else {
                        result = self.equiv_predicate_total_replacement(frame, &mic);
                    }
                    let mut max_frame = 0;
                    for cube in result {
                        let (frame, mic) = self.push_lemma(frame, cube);
                        if self.add_lemma(frame - 1, mic.clone(), false, None) {
                        return true;
                    }
                        if (frame > max_frame) {
                            max_frame = frame;
                        }
                    }
                }    
                else {
                    let (frame, mic) = self.push_lemma(frame, mic);
                    self.add_lemma(frame - 1, mic, false, None);
                }
                return true;
            } else {
                if *limit == 0 {
                    return false;
                }
                let model = LitOrdVec::new(self.get_pred(frame, false).0);
                if !self.trivial_block_rec(frame - 1, model, constraint, limit, parameter) {
                    return false;
                }
            }
        }
    }

    fn trivial_block(
        &mut self,
        frame: usize,
        lemma: LitOrdVec,
        constraint: &[LitVec],
        parameter: DropVarParameter,
    ) -> bool {
        let mut limit = parameter.limit;
        self.trivial_block_rec(frame, lemma, constraint, &mut limit, parameter)
    }

    fn propagate(&mut self, from: Option<usize>) -> bool {
        let level = self.level();
        let from = from.unwrap_or(self.frame.early).max(1);
        for frame_idx in from..level {
            self.frame[frame_idx].sort_by_key(|x| x.len());
            let frame = self.frame[frame_idx].clone();
            for mut lemma in frame {
                if self.frame[frame_idx].iter().all(|l| l.ne(&lemma)) {
                    continue;
                }
                for ctp in 0..3 {
                    if self.blocked_with_ordered(frame_idx + 1, &lemma, false, false) {
                        let core = self.solvers[frame_idx]
                            .inductive_core()
                            .unwrap_or(lemma.cube().clone());
                        if let Some(po) = &mut lemma.po
                            && po.frame < frame_idx + 2
                            && self.obligations.remove(po)
                        {
                            po.push_to(frame_idx + 2);
                            self.obligations.add(po.clone());
                        }
                        self.add_lemma(frame_idx + 1, core, true, lemma.po);
                        self.statistic.ctp.statistic(ctp > 0);
                        break;
                    }
                    if !self.cfg.ic3.ctp {
                        break;
                    }
                    let (ctp, _) = self.get_pred(frame_idx + 1, false);
                    if !self.tsctx.cube_subsume_init(&ctp)
                        && self.solvers[frame_idx - 1].inductive(&ctp, true)
                    {
                        let core = self.solvers[frame_idx - 1].inductive_core().unwrap();
                        let mic =
                            self.mic(frame_idx, core, &[], MicType::DropVar(Default::default()));
                        if self.add_lemma(frame_idx, mic, false, None) {
                            return true;
                        }
                    } else {
                        break;
                    }
                }
            }
            if self.frame[frame_idx].is_empty() {
                return true;
            }
        }
        self.frame.early = self.level();
        false
    }

    fn propagete_to_inf_rec(&mut self, lastf: &mut Vec<FrameLemma>, ctp: LitVec) -> bool {
        let ctp = LitOrdVec::new(ctp);
        let Some(lidx) = lastf.iter().position(|l| l.subsume(&ctp)) else {
            return false;
        };
        let mut lemma = lastf.swap_remove(lidx);
        loop {
            if self.inf_solver.inductive(&lemma, true) {
                if let Some(po) = &mut lemma.po {
                    self.obligations.remove(po);
                }
                self.add_inf_lemma(lemma.cube().clone());
                return true;
            } else {
                let target = self.tsctx.lits_next(lemma.cube());
                let (ctp, _) = self.lift.get_pred(&self.inf_solver, &target, false);
                if !self.propagete_to_inf_rec(lastf, ctp) {
                    return false;
                }
            }
        }
    }

    fn propagete_to_inf(&mut self) {
        let level = self.level();
        self.frame[level].shuffle(&mut self.rng);
        let mut lastf = self.frame[level].clone();
        while let Some(mut lemma) = lastf.pop() {
            loop {
                if self.inf_solver.inductive(&lemma, true) {
                    if let Some(po) = &mut lemma.po {
                        self.obligations.remove(po);
                    }
                    self.add_inf_lemma(lemma.cube().clone());
                    break;
                } else {
                    let target = self.tsctx.lits_next(lemma.cube());
                    let (ctp, _) = self.lift.get_pred(&self.inf_solver, &target, false);
                    if !self.propagete_to_inf_rec(&mut lastf, ctp) {
                        break;
                    }
                }
            }
        }
    }

    fn base(&mut self) -> bool {
        self.extend();
        assert!(self.level() == 0);
        if !self.cfg.ic3.no_pred_prop {
            let bad = self.tsctx.bad;
            if self.solvers[0].solve(&self.tsctx.bad.cube()) {
                let (input, bad) = self.solvers[0].trivial_pred();
                self.add_obligation(ProofObligation::new(
                    0,
                    LitOrdVec::new(bad),
                    vec![input],
                    0,
                    None,
                ));
                info!("counter-example found in base checking");
                return false;
            }
            self.tsctx.constraint.push(!bad);
            self.ts.constraint.push(!bad);
            self.lift = TransysSolver::new(&self.tsctx, false, self.rng.random());
            self.inf_solver = TransysSolver::new(&self.tsctx, true, self.rng.random());
        }
        true
    }
}

impl IC3 {
    pub fn new(mut cfg: Config, mut ts: Transys, pre_lemmas: Vec<LitVec>) -> Self {
        let ots = ts.clone();
        let mut rng = StdRng::seed_from_u64(cfg.rseed);
        let mut rst = VarVMap::new_self_map(ts.max_var());
        ts = ts.check_liveness_and_l2s(&mut rst);
        let statistic = Statistic::default();
        if !cfg.preproc.no_preproc {
            ts.simplify(&mut rst);
            let frts = FrTs::new(ts, rng.random(), rst, vec![]);
            (ts, rst) = frts.fr();

            if cfg.relation_file.is_some() {
                let new_refine_inv = BTreeMap::from_iter(
                    rst.iter().map(|(k, v)| (k.0 as usize, v.0 as usize)),
                );
                var2name::update_var2name_refine_map(&new_refine_inv);
                for (new, old) in rst.iter() {
                    if let Some(origin_id) = var2name::get_origin_id((*new).0 as usize){
                        trace!("Final Updated InvRefine Map: {} {:?} -> {}", (*new).0, new, origin_id);
                    }
                    else {
                        panic!("Final Updated InvRefine Map: {} {:?} -> None", (*new).0, new);
                    }
                }
            }
        }
        info!("simplified ts has {}", ts.statistic());
        let mut uts = TransysUnroll::new(&ts);
        uts.unroll();
        if cfg.ic3.inn {
            cfg.ic3.no_pred_prop = true;
            ts = uts.interal_signals();
        }
        let mut bad_ts = uts.compile();
        bad_ts.constraint.extend(ts.bad.iter().map(|&l| !l));
        let mut bad_input = GHashMap::new();
        for &l in ts.input.iter() {
            let n = uts.var_next(l, 1);
            bad_input.insert(n, l);
        }
        for l in ts.latch_no_next() {
            let n = uts.var_next(l, 1);
            bad_input.insert(n, l);
            bad_ts.input.push(n);
        }
        let tsctx = Grc::new(ts.ctx());
        let bad_ts = Grc::new(bad_ts.ctx());
        let activity = Activity::new(&tsctx);
        let frame = Frames::new(&tsctx);
        let inf_solver = TransysSolver::new(&tsctx, true, rng.random());
        let lift = TransysSolver::new(&tsctx, false, rng.random());
        let bad_lift = TransysSolver::new(&bad_ts, false, rng.random());
        let abs_cst = if cfg.ic3.abs_cst {
            LitVec::new()
        } else {
            ts.constraint.clone()
        };
        Self {
            cfg,
            ts,
            tsctx,
            activity,
            solvers: Vec::new(),
            inf_solver,
            bad_ts,
            bad_solver: cadical::Solver::new(),
            bad_lift,
            bad_input,
            lift,
            statistic,
            obligations: ProofObligationQueue::new(),
            frame,
            abs_cst,
            pre_lemmas,
            auxiliary_var: Vec::new(),
            ots,
            rst,
            bmc_solver: None,
            rng,
            filog: Default::default(),
        }
    }

    pub fn invariant(&self) -> Vec<LitVec> {
        self.frame
            .invariant()
            .iter()
            .map(|l| l.map_var(|l| self.rst[l]))
            .collect()
    }
}

impl Engine for IC3 {
    fn check(&mut self) -> Option<bool> {
        if !self.base() {
            return Some(false);
        }
        loop {
            let start = Instant::now();
            debug!("blocking phase begin");
            loop {
                match self.block() {
                    Some(false) => {
                        self.statistic.block.overall_time += start.elapsed();
                        return Some(false);
                    }
                    None => {
                        self.statistic.block.overall_time += start.elapsed();
                        self.verify();
                        return Some(true);
                    }
                    _ => (),
                }
                if let Some((bad, inputs, depth)) = self.get_bad() {
                    debug!("bad state found in last frame");
                    trace!("bad = {bad}");
                    let bad = LitOrdVec::new(bad);
                    self.add_obligation(ProofObligation::new(
                        self.level(),
                        bad,
                        inputs,
                        depth,
                        None,
                    ))
                } else {
                    break;
                }
            }
            debug!("blocking phase end");
            let blocked_time = start.elapsed();
            self.filog.log(Level::Info, self.frame.statistic(true));
            self.statistic.block.overall_time += blocked_time;
            self.extend();
            let start = Instant::now();
            let propagate = self.propagate(None);
            self.statistic.overall_propagate_time += start.elapsed();
            if propagate {
                self.verify();
                return Some(true);
            }
            self.propagete_to_inf();
        }
    }

    fn proof(&mut self) -> Proof {
        let invariants = self.frame.invariant();
        let invariants = invariants
            .iter()
            .map(|l| LitVec::from_iter(l.iter().filter_map(|l| self.rst.lit_map(*l))));
        let mut proof = self.ots.clone();
        let mut certifaiger_dnf = vec![];
        for cube in invariants {
            certifaiger_dnf.push(proof.rel.new_and(cube));
        }
        let invariants = proof.rel.new_or(certifaiger_dnf);
        let constrains: Vec<_> = proof
            .constraint
            .iter()
            .map(|e| !*e)
            .chain(proof.bad.iter().copied())
            .collect();
        let constrains = proof.rel.new_or(constrains);
        proof.bad = LitVec::from(proof.rel.new_or([invariants, constrains]));
        Proof { proof }
    }

    fn witness(&mut self) -> Witness {
        let mut res = Witness::default();
        if let Some((bmc_solver, uts)) = self.bmc_solver.as_mut() {
            for k in 0..=uts.num_unroll {
                let mut w = LitVec::new();
                for l in uts.ts.input() {
                    let l = l.lit();
                    let kl = uts.lit_next(l, k);
                    if let Some(v) = bmc_solver.sat_value(kl)
                        && let Some(r) = self.rst.lit_map(l.not_if(!v))
                    {
                        w.push(r);
                    }
                }
                res.input.push(w);
                let mut w = LitVec::new();
                for l in uts.ts.latch() {
                    let l = l.lit();
                    let kl = uts.lit_next(l, k);
                    if let Some(v) = bmc_solver.sat_value(kl)
                        && let Some(r) = self.rst.lit_map(l.not_if(!v))
                    {
                        w.push(r);
                    }
                }
                res.state.push(w);
            }
            return res;
        }
        let b = self.obligations.peak().unwrap();
        assert!(b.frame == 0);
        let mut b = Some(b);
        while let Some(bad) = b {
            if bad.frame == 0 {
                let assump: Vec<_> = bad
                    .lemma
                    .iter()
                    .chain(bad.input[0].iter())
                    .filter_map(|l| self.rst.lit_map(*l))
                    .collect();
                let (input, state) = self.ots.exact_init_state(&assump);
                res.state.push(state);
                res.input.push(input);
            } else {
                res.state.push(
                    bad.lemma
                        .iter()
                        .filter_map(|l| self.rst.lit_map(*l))
                        .collect(),
                );
                res.input.push(
                    bad.input[0]
                        .iter()
                        .filter_map(|l| self.rst.lit_map(*l))
                        .collect(),
                );
            }
            for i in bad.input[1..].iter() {
                let mut input = LitVec::new();
                let mut state = LitVec::new();
                for i in i.iter() {
                    if self.bad_ts.is_latch(i.var()) {
                        if let Some(m) = self.rst.lit_map(*i) {
                            state.push(m);
                        }
                    } else if let Some(m) = self.rst.lit_map(*i) {
                        input.push(m);
                    }
                }
                res.input.push(input);
                res.state.push(state);
            }
            b = bad.next.clone();
        }
        res
    }

    fn statistic(&mut self) {
        self.statistic.num_auxiliary_var = self.auxiliary_var.len();
        info!("obligations: {}", self.obligations.statistic());
        info!("{}", self.frame.statistic(false));
        let mut statistic = SolverStatistic::default();
        for s in self.solvers.iter() {
            statistic += *s.statistic();
        }
        info!("{statistic:#?}");
        info!("{:#?}", self.statistic);
    }
}
