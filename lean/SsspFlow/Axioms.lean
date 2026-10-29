import SsspFlow

/-! Prints the axioms of every named theorem of the paper and README.
Expected output for each: `propext`, `Classical.choice`, `Quot.sound` (or a subset). -/

#print axioms SsspFlow.Hierarchy.lemmaV
#print axioms SsspFlow.RHierarchy.lemmaV
#print axioms SsspFlow.FaceDisjoint.Setup.negCycle_iff
#print axioms SsspFlow.FaceDisjoint.Setup.walks
#print axioms SsspFlow.FaceDisjoint.Setup.lemmaD
#print axioms SsspFlow.FaceDisjoint.rot_pair
#print axioms SsspFlow.FaceDisjoint.rot_lemmaD
#print axioms SsspFlow.Boost.c1_negative
#print axioms SsspFlow.Boost.Run.len_nonneg
#print axioms SsspFlow.Boost.Run.exact
#print axioms SsspFlow.Tools.glue
#print axioms SsspFlow.Tools.decomp
#print axioms SsspFlow.Tools.rounding
#print axioms SsspFlow.Tools.rnd_bounds
#print axioms SsspFlow.Tools.level_step
#print axioms SsspFlow.Tools.params
#print axioms SsspFlow.labelOut
#print axioms SsspFlow.labelIn
