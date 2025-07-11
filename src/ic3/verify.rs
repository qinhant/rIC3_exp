use super::{IC3, proofoblig::ProofObligation};
use crate::{options, transys::{unroll::TransysUnroll, Transys, TransysCtx, TransysIf}};
use cadical::Solver;
use log::{error, info};
use logic_form::{Lemma, LitVec, Var};
use satif::Satif;
use std::ops::Deref;
use log::trace;

pub fn verify_invariant(ts: &TransysCtx, invariants: &[Lemma], options: &options::Options) -> bool {
    let mut solver = Solver::new();
    ts.load_trans(&mut solver, true);
    for lemma in invariants {
        let assump: LitVec = ts.init.iter().chain(lemma.iter()).copied().collect();
        if solver.solve(&assump) {
            return false;
        }
    }

    // Add the predicate semantics, i.e. !neq -> equivalence
    let relation = secIC3::RelationData::get_relation_data();

    for var in ts.latchs.iter() {
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
        }
    }

    for lemma in invariants {
        solver.add_clause(&!lemma.deref());
        if options.symmetry {
            let sym_lemma = Lemma::new(secIC3::symmetric_cube(lemma.cube()));
            solver.add_clause(&!sym_lemma.deref());
        }
    }
    if solver.solve(&ts.bad.cube()) {
        return false;
    }
    for lemma in invariants {
        if solver.solve(&ts.lits_next(lemma)) {
            return false;
        }
    }
    true
}

impl IC3 {
    pub fn verify(&mut self) {
        // if !self.options.certify {
        //     return;
        // }
        let invariants = self.frame.invariant();
        if !verify_invariant(&self.ts, &invariants, &self.options) {
            error!("invariant varify failed");
            panic!();
        }
        info!(
            "inductive invariant verified with {} lemmas!",
            invariants.len()
        );
        println!("----------Final Inductive Invariant----------");
        for lemma in invariants.iter() {
            println!("inducive invariant: {}", lemma);
        }
    }

    fn check_witness_with_constrain<S: Satif + ?Sized>(
        &mut self,
        solver: &mut S,
        uts: &TransysUnroll<Transys>,
        constraint: &LitVec,
    ) -> bool {
        let mut assumps = LitVec::new();
        for k in 0..=uts.num_unroll {
            assumps.extend_from_slice(&uts.lits_next(constraint, k));
        }
        assumps.push(uts.lit_next(uts.ts.bad, uts.num_unroll));
        solver.solve(&assumps)
    }

    pub fn check_witness_by_bmc(&mut self, b: ProofObligation) -> Option<LitVec> {
        let mut uts = TransysUnroll::new(&self.origin_ts);
        uts.unroll_to(b.depth);
        let mut solver: Box<dyn satif::Satif> = Box::new(cadical::Solver::new());
        for k in 0..=b.depth {
            uts.load_trans(solver.as_mut(), k, false);
        }
        uts.ts.load_init(solver.as_mut());
        let mut cst: LitVec = uts.ts.constraint().collect();
        if self.check_witness_with_constrain(solver.as_mut(), &uts, &cst) {
            info!("witness checking passed");
            self.bmc_solver = Some((solver, uts));
            None
        } else {
            let mut i = 0;
            while i < cst.len() {
                if self.abs_cst.contains(&cst[i]) {
                    i += 1;
                    continue;
                }
                let mut drop = cst.clone();
                drop.remove(i);
                if self.check_witness_with_constrain(solver.as_mut(), &uts, &drop) {
                    i += 1;
                } else {
                    cst = drop;
                }
            }
            cst.retain(|l| !self.abs_cst.contains(l));
            assert!(!cst.is_empty());
            Some(cst)
        }
    }
}
