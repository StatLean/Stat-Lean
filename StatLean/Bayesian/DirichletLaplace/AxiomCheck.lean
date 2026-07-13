import StatLean.Bayesian.DirichletLaplace.Theorem31

/-! Temporary axiom audit for the DL contraction milestone. Not part of the library umbrella;
built ad hoc via `lean-fasrc-build ...AxiomCheck` to inspect `#print axioms` output, then deleted. -/

open StatLean.Bayesian

-- Theorem 3.4 (both regimes) — expect CLEAN (no sorryAx): propext, Classical.choice, Quot.sound only.
#print axioms dl_theorem34_beta
#print axioms dl_theorem34_recip

-- Theorem 3.1 β-regime — expect sorryAx via the single TRUE debt `dl_shellSum_tendsto_zero_beta`.
#print axioms dl_theorem31
#print axioms dl_theorem31_ball
#print axioms dl_theorem31_paper_rate

-- Theorem 3.1 1/n-regime — expect sorryAx (D13 documented open case).
#print axioms dl_theorem31_recip
