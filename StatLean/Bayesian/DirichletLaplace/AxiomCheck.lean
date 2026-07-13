import StatLean.Bayesian.DirichletLaplace.Theorem31

/-! Temporary axiom audit for the DL closure milestone. Not part of the library umbrella;
built ad hoc via `lean-fasrc-build ...AxiomCheck` to inspect `#print axioms`, then deleted.
Expect ALL SIX headline declarations clean: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. -/

open StatLean.Bayesian

#print axioms dl_theorem34_beta
#print axioms dl_theorem34_recip
#print axioms dl_theorem31
#print axioms dl_theorem31_ball
#print axioms dl_theorem31_paper_rate
#print axioms dl_theorem31_recip
