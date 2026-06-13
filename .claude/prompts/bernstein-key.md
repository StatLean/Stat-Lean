Read CLAUDE.md (repo root) first and obey it — §2, §6 (search tools), §7, §10. Use the search tools.
Never `lake update`. HARD ANALYTIC ITEM — search Mathlib's `mgf` / power-series / integrability API
exhaustively; budget generously. This closes a named sorry that a prior session flagged as a real
Mathlib-infrastructure gap.

# CONTEXT
`StatLean/ConcentrationInequalities/Bernstein/MGFBound.lean` builds; its main theorem
`isSubExponential_of_hasBernsteinCondition` rests on ONE `private lemma bernstein_key` whose body is
`sorry` (line ~82). READ the file's module header — it contains the full math sketch. Close
`bernstein_key` to ZERO sorry. Do NOT change any statement; do NOT touch the main theorem.

# DEFS NOW FIXED (laptop just changed it): `Bernstein/Defs.lean`'s `moment_le` field now uses the
# LOWER LEBESGUE integral:
#   `moment_le : ∀ k ≥ 3, ∫⁻ ω, ENNReal.ofReal (|X ω|^k) ∂μ ≤ ENNReal.ofReal ((σ2/2)·k!·b^(k-2))`
# (Bochner `∫|X|^k` returned junk 0 for heavy-tailed X, making bernstein_key false — that is now
# resolved.) Rework MGFBound.lean to consume this `∫⁻` form. A prior session reported: "after this
# change, the `lintegral_tsum` + geometric-series path closes cleanly" — i.e. integrability (A) of
# `exp(l·X)` follows from `∫⁻ exp(|l|·|X|) = ∑ₖ |l|^k/k! ∫⁻|X|^k ≤ ∑ₖ |l|^k/k!·ofReal(...) < ∞`
# (`MeasureTheory.lintegral_tsum`, monotone `∫⁻`, `ENNReal` geometric series), giving
# `HasFiniteIntegral`/`Integrable`; then the MGF bound (B) as before. NOTE the file also already had
# `Measurable X` added to both `bernstein_key` and `isSubExponential_of_hasBernsteinCondition` — keep it.

# IMPORTANT — SIGNATURE FIX (already applied by a prior session — keep it):
`bernstein_key` as currently stated is FALSE without a measurability assumption on `X` (the
`HasBernsteinCondition` moment fields are Bochner integrals that are junk `0` for non-measurable `X`,
so the MGF/integrability conclusions fail). You MUST add `(hX : Measurable X)` (or `AEMeasurable X μ`
if that is all the `mgf`/integrability lemmas need) as a hypothesis to BOTH `bernstein_key` AND the
main theorem `isSubExponential_of_hasBernsteinCondition`, tagged `-- USER-INPUT: X measurable
(random variable); Lu-BDA §4.1` (the book tacitly assumes `X` is a random variable). Propagate it
through the two `where`/proof sites in the main theorem. This is a legitimate regularity hypothesis,
NOT laundering — do NOT instead make it a field of `HasBernsteinCondition` (regularity ⇒ hypothesis,
per CLAUDE.md). Then close the `bernstein_key` proof to ZERO sorry.

# THE LEMMA (already stated, BEFORE the measurability fix)
  `bernstein_key [IsProbabilityMeasure μ] (hB : HasBernsteinCondition X σ2 b μ) {l : ℝ}
     (hl : |l| ≤ 1 / ((2*(NNReal.sqrt σ2 ⊔ b) : ℝ≥0):ℝ)) :
     Integrable (fun ω => Real.exp (l*X ω)) μ ∧ mgf X μ l ≤ Real.exp (l^2 * α^2 / 2)`
where `α = 2*(√σ2 ⊔ b)`, and `HasBernsteinCondition` gives `E X = 0`, `E[X²] = σ2`,
`E|X|^k ≤ (σ2/2)·k!·b^(k-2)` for `k ≥ 3`.

# PROOF PATH (two independent sub-goals)
**(A) Integrability** of `exp(l·X)` for `|l| ≤ 1/α ≤ 1/(2b)` (so `|l|b ≤ 1/2`): bound
`exp(l·X) ≤ exp(|l|·|X|)` and `E[exp(|l|·|X|)] = ∑ₖ |l|^k/k! · E|X|^k ≤ 1 + |l|·E|X| + ∑_{k≥2} |l|^k/k!·E|X|^k`,
and the moment bounds make this a convergent geometric-type series (`∑ (|l|b)^k`). Mathlib route:
`MeasureTheory.integrable_of_…` via `∑' k, ∫ |l·X|^k/k!` (MCT / `lintegral_tsum`,
`Real.exp_eq_tsum`/`NormedSpace.exp_eq_tsum`), or `integrable_exp_mul_of_…`. Search
`./tools/loogle.sh '"integrable_exp"'`, `'"integrableExpSet"'`, `'"mem_integrableExpSet"'`.

**(B) MGF bound:** `mgf X μ l = ∑ₙ lⁿ/n! · moment n` (Mathlib `ProbabilityTheory.mgf` analyticity:
`./tools/check.sh 'ProbabilityTheory.hasFPowerSeriesAt_mgf'` / `'ProbabilityTheory.mgf_eq_tsum'` /
`'ProbabilityTheory.mgf_hasSum'`). Split n=0 (=1), n=1 (=0, mean_zero), n=2 (=l²σ2/2), n≥3 tail
`≤ (σ2/2)·l²·∑_{k≥1}(|l|b)^k = (σ2/2)·l²·(|l|b)/(1−|l|b) ≤ (σ2/2)·l²` (since `|l|b ≤ 1/2`). So
`mgf ≤ 1 + l²σ2 ≤ exp(l²σ2) ≤ exp(l²α²/2)` (as `σ2 ≤ α²/2`, since `α = 2(√σ2∨b) ≥ 2√σ2` ⇒ `α² ≥ 4σ2 ≥ 2σ2`).

The flagged gap was connecting `hasFPowerSeriesAt_mgf`'s `FormalMultilinearSeries.radius ≥ 1/b` to the
moment convergence. If `mgf_eq_tsum`/`mgf_hasSum` (giving the series directly under an integrability/
`mem_integrableExpSet` hypothesis you can supply from (A)) sidesteps the radius bookkeeping, PREFER
that — search for it before fighting `radius`. The tail bound is then `tsum_le_tsum` + geometric series
(`tsum_geometric_of_lt_one`).

# ZERO sorry is the bar. If after a thorough, documented effort a genuine Mathlib gap truly blocks it,
leave `bernstein_key` as the single sorry with an updated docstring (exact remaining goal + every
lemma tried + why) and report PROMINENTLY "ESCALATE: bernstein_key unclosable, <reason>". Do not add
any other sorry.

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/Bernstein/MGFBound.lean`.
# BUILD (you are ALREADY inside an srun allocation — run lake DIRECTLY, do NOT nest srun/sbatch):
#   lake build StatLean.ConcentrationInequalities.Bernstein.MGFBound
# DONE = build exits 0; ZERO sorries (or 1 named bernstein_key + ESCALATE note); commit
(`conc(bernstein): close bernstein_key — MGF power-series bound (Lu-BDA §4.1)`). Report build + exact
sorry status. Independently re-verified.
