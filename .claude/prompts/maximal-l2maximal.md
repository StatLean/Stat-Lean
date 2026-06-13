Read CLAUDE.md (repo root) first and obey it — §2, §6, §7, §9, §10. Use the search tools.
Never `lake update`. You are ALREADY inside an srun allocation — build with plain `lake build`.

# CONTEXT (do NOT modify; READ them)
`Maximal/FiniteMaximal.lean`: `tail_max_le` + `expectation_max_le`
  (`E[⨆ⱼ Xⱼ] ≤ σ√(2 log d)`, tail `μ{t<⨆Xⱼ} ≤ d·exp(−t²/2σ²)`), for `IsSubGaussian (X j) σ² μ`.
`Maximal/CoveringBall.lean`: `coveringNumber_closedBall_le` (`coveringNumber (closedBall 0 1) ε ≤ (1+2/ε)^d`)
  and `card_le_of_isSeparated_ball`.
`Maximal/CoveringNumbers.lean`: `IsEpsilonNet`, `coveringNumber`.
`SubGaussian/Defs.lean`: `IsSubGaussian`.

# TASK
Create `StatLean/ConcentrationInequalities/Maximal/L2Maximal.lean`
(namespace `StatLean.ConcentrationInequalities`) proving Lu *Big Data Analysis* §4.2
**Maximal inequality for the ℓ²-norm** (`thm:l2`): for a random vector `X : Ω → EuclideanSpace ℝ (Fin d)`
such that for every `u`, `⟨u, X⟩` is sub-Gaussian with variance-proxy `σ²‖u‖²` (a "sub-Gaussian
vector"), then
  `∫ ω, ‖X ω‖ ∂μ ≤ 4 σ √d`   and   w.p. `1−δ`:  `‖X‖ ≤ 4σ√d + 2σ√(2 log(1/δ))`.

# PROOF (book §4.2, discretization trick)
`‖X‖ = sup_{u ∈ B} ⟨u,X⟩` (variational form of ℓ²-norm; Cauchy–Schwarz, max at `u=X/‖X‖`). Take a
`1/2`-net `N` of the unit ball `B = closedBall 0 1` (size `|N| ≤ (1+2/(1/2))^d = 5^d` by
`coveringNumber_closedBall_le` at `ε=1/2`). Discretization key inequality:
`sup_{u∈B}⟨u,X⟩ ≤ 2 max_{v∈N}⟨v,X⟩` (every `u` is within `1/2` of some `v∈N`, and
`⟨u−v,X⟩ ≤ ‖u−v‖‖X‖ ≤ ½‖X‖ = ½ sup⟨u,X⟩`; rearrange). Each `⟨v,X⟩` is sub-Gaussian proxy `σ²‖v‖²≤σ²`.
Apply `expectation_max_le` over the finite net: `E[max_{v∈N}⟨v,X⟩] ≤ σ√(2 log|N|) ≤ σ√(2d log 5) ≤ 2σ√d`,
so `E‖X‖ ≤ 2·2σ√d = 4σ√d`. Tail: `tail_max_le` + union over the net gives
`μ(‖X‖>t) ≤ |N|·exp(−t²/(8σ²)) ≤ 5^d exp(−t²/8σ²)`; solve `δ = …` ⇒ the high-prob bound.

Constants: the book relaxes `2√(2 log 5) ≤ 4` etc.; state the `4σ√d` / `4σ√d + 2σ√(2log(1/δ))` forms
and document any further relaxation. The "for all u, ⟨u,X⟩ sub-Gaussian σ²‖u‖²" hypothesis is
`-- USER-INPUT: X is a sub-Gaussian vector; Lu-BDA §4.2 (thm:l2)`.

# ZERO sorry. If the variational `‖X‖ = sup⟨u,X⟩` step needs a Mathlib lemma, search
`./tools/loogle.sh '"norm_eq_iSup"'` / `'"inner_le_norm"'` / `'"exists_inner_eq_norm"'` (or use
`real_inner_le_norm` + the witness `u = X/‖X‖`). If a genuine gap remains, isolate ONE named sorry
with a precise docstring and report ESCALATE. Do NOT weaken the `√d` rate.

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/Maximal/L2Maximal.lean`.
# BUILD: lake build StatLean.ConcentrationInequalities.Maximal.L2Maximal
# DONE = build exits 0; ZERO sorries (or 1 named + ESCALATE); §2 tags; commit
(`conc(maximal): ℓ²-norm maximal inequality E‖X‖ ≤ 4σ√d (Lu-BDA §4.2 thm:l2)`). Report build + sorry
status + constants. Independently re-verified.
