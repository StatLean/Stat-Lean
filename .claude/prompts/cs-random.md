Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use the search tools. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE. Large probabilistic
assembly; prove in named pieces. 0 errors / 0 sorries at the end.

# CONTEXT
`StatLean/HighDimensionalStatistics/CompressedSensing/RandomRIP.lean` (namespace
`StatLean.HighDimensionalStatistics`; `open MeasureTheory ProbabilityTheory Real Matrix`,
`open scoped ENNReal NNReal InnerProductSpace`, `open StatLean.ConcentrationInequalities`;
`variable {n d : ℕ}`) has ONE theorem `prob_rip_of_iid_gaussian` (T3) `:= by sorry`. It imports the
now-PROVED `CompressedSensing/GaussianChiSquared.lean` and `ConcentrationInequalities/Maximal/CoveringBall.lean`.
READ the merged `GaussianChiSquared.lean` for the EXACT conclusion constant of
`gaussian_quadratic_form_tail` (it is `μ {ω | δ < |‖designMap (X ω) β‖²/‖β‖² − 1|} ≤
   ENNReal.ofReal (2 * Real.exp (−(n)·δ²/C))`. The merged file proves the **CONFIRMED constant `C = 32`**
(α=4). Use `C = 32`: the per-net-event tail at `δ/2` is `2·exp(−nδ²/128)`, and the matching `hn` lower
bound is `n ≥ (C'/δ²)·s·log(18d/ε)` with `C' ≈ 384` (derive the exact value; document the deviation
from the book's `96`, which assumed the sharp `/8`).
Available bricks:
* `gaussian_quadratic_form_tail` (fixed `β ≠ 0`, `0<δ≤1`) — the per-vector tail above.
* `Defs.lean`: `IsRIP X s δ = ∀ β, IsSparse s β → (1−δ)‖β‖² ≤ ‖designMap X β‖² ≤ (1+δ)‖β‖²`.
* `ConcentrationInequalities.coveringNumber_closedBall_le` :
   `0<ε<1 → coveringNumber (Metric.closedBall 0 1) ε ≤ ⌊(1+2/ε)^d⌋₊` (on `EuclideanSpace ℝ (Fin m)`,
   `[NeZero m]`), and `card_le_of_isSeparated_ball`, `IsEpsilonNet` (`Maximal/CoveringNumbers.lean`).
* Mathlib: `measure_biUnion_finset_le`/`measure_iUnion_fintype_le`, `prob_compl_eq_one_sub`/
   `measure_compl`, `IsProbabilityMeasure`.

# STRATEGY (book `thm:3s-rip`)
Bound `μ {¬ IsRIP (X ω) (3*s) δ}` then take the complement.
1. **Reduce RIP to a finite net event.** `IsRIP (X ω) (3*s) δ` holds iff for every support `T` with
   `T.card = 3*s` and every unit vector `v` supported on `T`, `|‖X ω v‖²/‖v‖² − 1| ≤ δ`. By a
   `1/4`-net `𝒩_T` of the unit ball of the `3s`-dim coordinate subspace `span(T)` and the standard
   discretisation `sup_{‖u‖≤1, supp⊆T} |uᵀ(AᵀA−I)u| ≤ 2·sup_{v∈𝒩_T} |vᵀ(AᵀA−I)v|`, it SUFFICES that for
   all `T` (card `3s`) and all `v ∈ 𝒩_T`, `|‖X ω v‖² − 1| ≤ δ/2`. Prove the discretisation as a private
   lemma `sup_ball_le_two_sup_net` (expand `uᵀAu − vᵀAv = (u−v)ᵀAu + vᵀA(u−v)`, `‖u−v‖ ≤ 1/4`). So
   `{¬RIP} ⊆ ⋃_{T : card 3s} ⋃_{v ∈ 𝒩_T} {ω | δ/2 < |‖X ω v‖²/‖v‖² − 1|}`  (each net `v` has `‖v‖=1`).
2. **Per-event tail.** Each `{ω | δ/2 < |…|} ` has measure `≤ 2·exp(−n(δ/2)²/C) = 2·exp(−n δ²/(4C))`
   by `gaussian_quadratic_form_tail` at `δ/2` (note `δ/2 ≤ 1`).
3. **Union bound + counts.** `#{T : card 3s} = Nat.choose d (3s) ≤ d^(3s)`; `#𝒩_T ≤ ⌊9^(3s)⌋₊`
   (`coveringNumber_closedBall_le` at `ε = 1/4`, `(1+2/(1/4)) = 9`). So
   `μ{¬RIP} ≤ (d^(3s))·(9^(3s))·2·exp(−nδ²/(4C)) = 2·(9d)^(3s)·exp(−nδ²/(4C))`
   (`measure_biUnion_finset_le` twice).
4. **Sample size.** Show `2·(9d)^(3s)·exp(−nδ²/(4C)) ≤ ε` from `hn`. Take logs:
   need `nδ²/(4C) ≥ log 2 + 3s·log(9d) + log(1/ε)`. Bound the RHS by `3s·log(18d/ε)` (or a constant
   multiple) and pick the matching constant. The stub's `hn` uses `96`; **if the provable constant
   differs, change the `96` (and/or `18`) in the `hn` hypothesis to the value you actually need and
   DOCUMENT the deviation** (CLAUDE.md §1) — `hn` is a USER-INPUT lower bound, so a larger constant only
   strengthens the hypothesis; keep the `O(s log(d/ε))` order.
5. **Complement.** `μ{IsRIP} = 1 − μ{¬RIP} ≥ 1 − ε` via `measure_compl`/`prob_compl_eq_one_sub`
   (needs the `{¬RIP}` event MEASURABLE — it is a finite/countable intersection-union over supports and
   net points of measurable sets `{ω | … |‖X ω v‖² − 1| …}`; build measurability from `hindep`/continuity
   of `ω ↦ X ω i j` — search `'"Measurable"' '"gaussianReal"'`, and reduce the event to the net form
   from step 1 so it is a finite boolean combination).

# REQUIREMENTS
ZERO sorry. Keep T3's name and the hypotheses/tags; you MAY change the `hn` constants (documented) and
add private lemmas in THIS file only. Reuse `gaussian_quadratic_form_tail` and `coveringNumber_closedBall_le`;
do not reprove concentration or covering bounds. If full measurability of the RIP event proves very heavy,
isolate it as a single private lemma and prove it carefully (do NOT leave it as a hypothesis on T3 —
that would launder content; CLAUDE.md §9).

# TOUCH-SET: ONLY  StatLean/HighDimensionalStatistics/CompressedSensing/RandomRIP.lean
# BUILD: lake build StatLean.HighDimensionalStatistics.CompressedSensing.RandomRIP
# DONE = build exits 0; 0 sorries; commit (`cs(random): Gaussian matrix is 3s-RIP whp T3 (Lu-BDA ch7, thm:3s-rip)`).
  Report build status, sorry count, the final `hn` constants used, and the net/union lemmas proved.
