import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Theorem7_21
import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Corollary7_22

/-! Temporary axiom audit for Batch 5 (Wainwright §7.5). NOT part of the library — removed
after the audit. Each `#print axioms` must report only `[propext, Classical.choice, Quot.sound]`
(no `sorryAx`). -/

open StatLean.HighDimensionalStatistics

#print axioms lasso_support_recovery_unique
#print axioms lasso_support_recovery_no_false_inclusion
#print axioms lasso_support_recovery_linf
#print axioms lasso_support_recovery_no_false_exclusion
#print axioms lasso_support_recovery_subgaussian
