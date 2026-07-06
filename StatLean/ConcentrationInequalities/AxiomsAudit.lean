import StatLean.ConcentrationInequalities

/-!
# Batch-10 axioms audit (throwaway; NOT registered in the umbrella)

`#print axioms` on the headline theorems. Expected: `propext,
Classical.choice, Quot.sound` everywhere; `sorryAx` only on declarations
transitively touching the open named debts.
-/

open StatLean.ConcentrationInequalities

#print axioms StatLean.ConcentrationInequalities.bernstein_subexponential
#print axioms StatLean.ConcentrationInequalities.symmetrization_upper
#print axioms StatLean.ConcentrationInequalities.symmetrization_lower_pi
#print axioms StatLean.ConcentrationInequalities.contraction_principle
#print axioms StatLean.ConcentrationInequalities.gaussian_symmetrization_upper
#print axioms StatLean.ConcentrationInequalities.gaussian_symmetrization_lower
#print axioms StatLean.ConcentrationInequalities.empirical_symmetrization
#print axioms StatLean.ConcentrationInequalities.empirical_symmetrization_countable
#print axioms StatLean.ConcentrationInequalities.discrete_dudley
#print axioms StatLean.ConcentrationInequalities.dudley_inequality
#print axioms StatLean.ConcentrationInequalities.dudley_inequality_abs
#print axioms StatLean.ConcentrationInequalities.dudley_tail_three_term
#print axioms StatLean.ConcentrationInequalities.generic_chaining
#print axioms StatLean.ConcentrationInequalities.lipschitz_lln
#print axioms StatLean.ConcentrationInequalities.vc_lln_finset
#print axioms StatLean.ConcentrationInequalities.vc_lln_countable
#print axioms StatLean.ConcentrationInequalities.glivenko_cantelli
#print axioms StatLean.ConcentrationInequalities.vc_generalization
#print axioms StatLean.ConcentrationInequalities.vcDim_halfSpaceClass
#print axioms StatLean.ConcentrationInequalities.subGaussianVecNorm_le_of_indep
