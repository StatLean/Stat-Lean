import StatLean.Minimaxity
/-! Temporary verification-gate module: `#print axioms` of the fully-proven (0-sorry) headline
theorems. Expect only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Not in the umbrella. -/
open StatLean.Minimaxity
#print axioms minimax_local_packing
#print axioms klDiv_gaussianReal
#print axioms klDiv_pi_eq_nsmul
#print axioms discreteEntropy_le_log_card
#print axioms density_estimation_hellinger_rate
#print axioms sobolev_regression_rate
