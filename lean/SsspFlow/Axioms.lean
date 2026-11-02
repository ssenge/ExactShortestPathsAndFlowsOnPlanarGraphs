import SsspFlow

/-! Prints the axioms of every named theorem of the paper and README.
Expected output for each: `propext`, `Classical.choice`, `Quot.sound` (or a subset). -/

#print axioms SsspFlow.Hierarchy.lemmaV
#print axioms SsspFlow.RHierarchy.lemmaV
#print axioms SsspFlow.RHierarchy.lemmaV_chain
#print axioms SsspFlow.FaceDisjoint.Setup.negCycle_iff
#print axioms SsspFlow.FaceDisjoint.Setup.walks
#print axioms SsspFlow.FaceDisjoint.Setup.lemmaD
#print axioms SsspFlow.FaceDisjoint.rot_pair
#print axioms SsspFlow.FaceDisjoint.rot_lemmaD
#print axioms SsspFlow.Boost.c1_negative
#print axioms SsspFlow.Boost.Run.len_nonneg
#print axioms SsspFlow.Boost.Run.exact
#print axioms SsspFlow.Boost.Run.contract
#print axioms SsspFlow.Boost.Run.decay
#print axioms SsspFlow.Boost.Run.sum_bounds
#print axioms SsspFlow.Tools.glue
#print axioms SsspFlow.Tools.decomp
#print axioms SsspFlow.Tools.rounding
#print axioms SsspFlow.Tools.rnd_bounds
#print axioms SsspFlow.Tools.level_step
#print axioms SsspFlow.Tools.params
#print axioms SsspFlow.labelOut
#print axioms SsspFlow.labelIn
#print axioms SsspFlow.FlowScaling.flow_rev
#print axioms SsspFlow.FlowScaling.residual_sum
#print axioms SsspFlow.FlowScaling.fill_eq
#print axioms SsspFlow.FlowScaling.fill_step
#print axioms SsspFlow.FlowScaling.step_feasible
#print axioms SsspFlow.FlowScaling.system_solvable
#print axioms SsspFlow.FlowScaling.residual_bound
#print axioms SsspFlow.FlowScaling.scaling_bound
#print axioms SsspFlow.FlowScaling.invariant_step
#print axioms SsspFlow.FlowScaling.reduced_nonneg
#print axioms SsspFlow.FlowScaling.reduced_path
#print axioms SsspFlow.FlowScaling.floor_of_min
#print axioms SsspFlow.FlowScaling.exact_feasible
