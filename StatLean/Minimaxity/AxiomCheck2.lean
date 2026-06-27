import StatLean.Minimaxity
/-! Temporary verification-gate module: `#print axioms` on the tranche-2 closures.
Expect `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Not in the umbrella. -/
open StatLean.Minimaxity
#print axioms klDiv_map_le
#print axioms pinsker_tv_le_kl
#print axioms minimax_ge_testing_error
#print axioms minimax_functional_modulus
#print axioms minimax_le_cam_convex_hull
