Read CLAUDE.md (repo root) first — §2, §6, §7, §10. Use the search tools. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE.

# CONTEXT (do NOT modify; READ it)
`McDiarmid/DoobDecomposition.lean` (imported) provides the global sub-Gaussian MGF bound for
`g = f(X₁,…,Xₙ) − E[f]` under bounded differences `Dᵢf ≤ cᵢ` and independent `X`:
`mgf_sub_expectation_le` : `mgf (fun ω => f(X ω) − μ[f∘X]) μ λ ≤ exp(λ² (∑ cᵢ²) / 8)` (a
`HasSubgaussianMGF`/sub-Gaussian-MGF statement with proxy `(∑cᵢ²)/4`). (Read the file for the exact
name/shape.)
`SubGaussian/Chernoff.lean` / Mathlib `ProbabilityTheory.measure_ge_le_exp_mul_mgf` give Chernoff.

# TASK
Create `StatLean/ConcentrationInequalities/McDiarmid/McDiarmid.lean`
(namespace `StatLean.ConcentrationInequalities`) proving Lu *Big Data Analysis* §3.1 **McDiarmid's
bounded-differences inequality** (`McDiarmid`): for independent `X`, `f` with `Dᵢf ≤ cᵢ`,
  `μ {ω | t < f(X ω) − E[f∘X]} ≤ ENNReal.ofReal (exp(−2 t² / (∑ᵢ cᵢ²)))`   for `0 ≤ t`,
and (optional, if easy) the two-sided `|f − E f|` version with the `2·exp(...)` factor.

# PROOF
Pure Chernoff on the sub-Gaussian MGF: from `mgf_sub_expectation_le` (proxy `σ² = (∑cᵢ²)/4`), the
standard sub-Gaussian tail gives `μ{t < g} ≤ exp(−t²/(2σ²)) = exp(−t²/(2·(∑cᵢ²)/4)) = exp(−2t²/∑cᵢ²)`.
Mirror the `μ.real`→`ENNReal` bridge in `SubGaussian/TailBounds.lean`
(`rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]; exact ENNReal.ofReal_le_ofReal …`). If
`mgf_sub_expectation_le` is phrased as `HasSubgaussianMGF`, just apply `HasSubgaussianMGF.measure_ge_le`.

ZERO sorry (the file may transitively rest on DoobDecomposition's one open `sorry`
`increment_bounded_of_bounded_differences` — that is fine; do NOT add any NEW sorry here). Bounded
differences `Dᵢf ≤ cᵢ`, independence, `f` measurable are `-- USER-INPUT: …; Lu-BDA §3.1`.

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/McDiarmid/McDiarmid.lean`.
# BUILD: lake build StatLean.ConcentrationInequalities.McDiarmid.McDiarmid
# DONE = build exits 0; ZERO new sorries; §2 tags; commit
(`conc(mcdiarmid): McDiarmid bounded-differences inequality (Lu-BDA §3.1 McDiarmid)`). Report build + sorry count.
