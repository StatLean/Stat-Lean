Read CLAUDE.md (repo root) first and obey it — §2, §6, §7, §9, §10. Use the search tools. Never `lake update`.

# CONTEXT (do NOT modify)
`SubExponential/Defs.lean`: `structure IsSubExponential (X) (α : ℝ≥0) (μ)` with
  `mgf_le : ∀ l, |l| ≤ 1/α → mgf (X − E X) μ l ≤ exp(l²α²/2)` and `integrable_exp_mul`.
`SubExponential/TailBounds.lean`: `measure_sub_integral_lt_le_quadratic` / `_linear`
  (single-variable two-regime tail). Read both.

# TASK
Create `StatLean/ConcentrationInequalities/SubExponential/SampleMean.lean`
(namespace `StatLean.ConcentrationInequalities`) proving Lu *Big Data Analysis* §3.2
**sample-mean concentration of sub-exponentials**: for `X : Fin n → Ω → ℝ` independent, each
`IsSubExponential (X i) α μ` with common mean `μ₀` (`∫ X i = μ₀`), the sample mean
`X̄ₙ = (1/n) ∑ᵢ Xᵢ` satisfies, for `0 ≤ t`:
  `P(X̄ₙ − μ₀ > t) ≤ exp(−n t² / (2α²))`   for `0 ≤ t ≤ α`   (quadratic regime)
  `P(X̄ₙ − μ₀ > t) ≤ exp(−n t / (2α))`     for `t ≥ α`       (linear regime)

# PROOF (book §3.2)
Chernoff on `X̄ₙ − μ₀`: for `λ ∈ [0, n/α]` (so each `λ/n ≤ 1/α`),
  `E[exp(λ(X̄ₙ − μ₀))] = ∏ᵢ E[exp((λ/n)(Xᵢ − μ₀))] ≤ ∏ᵢ exp((λ/n)²α²/2) = exp(λ²α²/(2n))`
using independence (`ProbabilityTheory.iIndepFun` ⇒ `mgf` of a sum factorises — search
`./tools/loogle.sh '"iIndepFun"' '"mgf"'`, `'"mgf_sum"'`, `ProbabilityTheory.iIndepFun.mgf_sum` /
`indepFun.mgf_add`) and each factor from `IsSubExponential.mgf_le_of_mem_Icc`. So `X̄ₙ − μ₀` has the
sub-exponential-type MGF bound `exp(λ² (α²/n)/2)` on `|λ| ≤ n/α` — i.e. effectively parameter that
gives the `n`-enhanced regimes. Then optimize `λ` exactly as in the single-variable proof (mirror
`SubExponential/TailBounds.lean`): quadratic `λ = nt/α²` for `t ≤ α`, clamp `λ = n/α` for `t > α`.
Chernoff engine: `measure_ge_le_exp_mul_mgf`. Bridge `μ.real`→`μ` ENNReal as in `SubGaussian/TailBounds.lean`.

You MAY first prove a helper `isSubExponential_sum_…`/`mgf_sampleMean_le` lemma (the MGF bound above)
then reuse the regime-optimization algebra. ZERO sorry. Independence + common mean + `α > 0` are
`-- USER-INPUT: …; Lu-BDA §3.2`; integrability/measurability regularity is `-- LEAN-ONLY`.

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/SubExponential/SampleMean.lean`.
# BUILD (you are ALREADY inside an srun allocation — run lake DIRECTLY, do NOT nest srun/sbatch):
#   lake build StatLean.ConcentrationInequalities.SubExponential.SampleMean
# DONE = build exits 0; ZERO sorries; §2 tags; commit
(`conc(subexp): sample-mean two-regime concentration (Lu-BDA §3.2)`). Report build + sorry count + constants.
