import StatLean.HighDimensionalStatistics.MEstimator.Bound
import StatLean.HighDimensionalStatistics.MEstimator.DualBound
import StatLean.HighDimensionalStatistics.MEstimator.GLMCorollaries

/-! Temporary six-check axioms audit for the Batch-6 main theorems. Not in the umbrella; deleted
after the audit. Each should depend ONLY on `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). -/

open StatLean.HighDimensionalStatistics.MEstimator

#print axioms mestimator_l2_bound
#print axioms mestimator_dual_bound
#print axioms glm_lasso_l2_l1_rate
#print axioms glm_lasso_linf_rate
#print axioms glmCost_gradient_eq_scoreVec
