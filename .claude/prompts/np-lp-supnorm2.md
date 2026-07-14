# CONTINUATION: close the 3 sorries in NonparametricStatistics/LocalPolynomial/SupNorm/*.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain `lake build <module>` (no `srun`). Commit after EACH file
builds 0-sorry (a previous session lost work by not committing).

A PREVIOUS session left `SupNorm/Increments.lean` with ~221 lines of `private` helper lemmas
ABOVE the still-`sorry` main theorem `lp_weight_lipschitz_sum`. READ THAT FILE FIRST and build
it; the helpers are yours to use/replace.

## Hard constraints
- **Only edit** the three `SupNorm/*.lean` files. The three PUBLIC theorem signatures/tags/
  docstrings are frozen; private helpers are free. Lines ≤ 100. `import Mathlib.*` allowed.
  Foreground `lake build` only; NEVER background it or poll with pgrep loops. Bounded
  responses (~150 lines); one lemma at a time.
- Escape hatch: NAMED lifted `private` sorries + `-- TODO(np):` + report, last resort only.
- After green: `#print axioms` on `lp_weight_lipschitz_sum`, `lp_supnorm_stochastic_le`,
  `lp_supnorm_rate` → only `propext, Classical.choice, Quot.sound`.

## Available API (all closed): WeightBounds (`lp_weight_abs_le`, `lp_weight_sum_abs_le`,
`lp_weight_eq_zero_of_far`, `lpBasis_normSq_le`), Quadratic (`lpMatrix_posDef`,
`lpMatrix_inv_mulVec_sq_le`, `lpMatrix_isSymm`, `lpMatrix_mulVec_apply`), PointwiseRisk
(`lp_bias_deterministic`), ForMathlib (`hasLaw_sum_mul_gaussianReal`,
`lintegral_exp_mul_sq_gaussianReal_le`, `lintegral_iSup_sq_le_log`,
`lintegral_iSup_normSq_gaussian_le`).

## Plan

### 1. `lp_weight_lipschitz_sum` (Increments.lean) — finish from the existing helpers.
`∃ CL > 0, … ∑ i |Wᵢ(t) − Wᵢ(t')| ≤ CL·|t−t'|/h³`. Key structure (helpers likely cover parts):
- FIRST case-split `1 ≤ |t−t'|/h` (crude: two `lp_weight_sum_abs_le` give
  `∑|ΔW| ≤ 2C* ≤ 2C*·|t−t'|/h ≤ 2C*·|t−t'|/h³` using `h ≤ 1`) vs `|t−t'| < h` (smooth case:
  all active `z`-arguments within distance `1 + 1 = 2` of support).
- Smooth case: telescope the triple product `W = (nh)⁻¹·(B⁻¹U(z))₀·K(z)`:
  K-difference `≤ LK|t−t'|/h`; U-difference per coordinate `≤ 2^ℓ-ish·|t−t'|/h` (monomial MVT
  on `|z| ≤ 2`); B-difference entrywise `≤ (count ≤ 4a₀nh active i)·(nh)⁻¹·(per-i Lipschitz)`;
  resolvent `B_t⁻¹ − B_{t'}⁻¹ = B_t⁻¹(B_{t'} − B_t)B_{t'}⁻¹` (both PosDef via `heig`,
  `Matrix.mul_nonsing_inv`), quadratic-form operator bounds via `lpMatrix_inv_mulVec_sq_le` +
  Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`). Terms lacking a K-difference keep a K
  factor supported in the DOUBLED window; count of active i `≤ 4a₀nh + n·(1/n)`-slack via
  `hdens` on `[min t t' − h, max t t' + h]` (width `≤ 4h` in the smooth case). Total per-i
  scale `|t−t'|/(n h³)`; ≤ `8a₀nh` terms ⇒ `CL·|t−t'|/h²·(a₀…)` — the stated `h³` gives slack.
  Set `CL` to whatever your chain produces (any closed form, `by positivity`-provable).

### 2. `lp_supnorm_stochastic_le` (StochasticTerm.lean):
`∃ C > 0, ∀ n ≥ 2, 1/(2n) ≤ h ≤ 1, design hyps, ξ iid N(0,v):
 ∫⁻ ω ofReal((⨆ t:Icc 0 1, |∑ᵢ ξᵢ(ω)Wᵢ(t)|)²) ≤ ofReal (C·v·log n/(nh))`.
- Case `v = 0` and/or `Kmax = 0` degeneracies: avoid by using always-positive normalizers
  below (or split: `v = 0` ⇒ all `ξᵢ = 0` a.e. via `gaussianReal 0 0 = dirac 0` +
  `HasLaw` ⇒ LHS `= 0`).
- Grid `tⱼ = j/M`, `j : Fin (M+1)`, `M := n^4`. Pointwise per ω (BddAbove from
  `lp_weight_abs_le`: `|Z t| ≤ (∑ᵢ|ξᵢ|)·C*/(nh)`; use `ciSup_le`/`le_ciSup`):
  `(⨆_t |Z t|)² ≤ 2(⨆_j |Z tⱼ|)² + 2((∑ᵢ|ξᵢ|)·CL·n⁻⁴/h³)²` via item 1 with `|t − t_{j(t)}| ≤ n⁻⁴`.
- Grid max: `Z tⱼ ~ gaussianReal 0 ((∑ᵢWᵢ(tⱼ)²).toNNReal·v)` (`hasLaw_sum_mul_gaussianReal`),
  `∑ᵢ Wᵢ(tⱼ)² ≤ (C*)²/(nh)` (sup×ℓ¹). Exponential moments with
  `a := ((4·((C*)²+1)/(nh))·(v+1))⁻¹ > 0`: `a·4v' ≤ 1` for `v' ≤ (C*)²v/(nh)` ✓ ⇒
  `E exp(a Z²) ≤ √2` (transfer through the law: `HasLaw.lintegral_comp`-style map rewrite +
  `lintegral_exp_mul_sq_gaussianReal_le`). Then `lintegral_iSup_sq_le_log` (M+1 vars, `C₀ = √2`):
  `∫⁻ ofReal(⨆ⱼ Z tⱼ²) ≤ ofReal (log (√2(n⁴+1)) · 4((C*)²+1)(v+1)/(nh))`, and
  `log (√2(n⁴+1)) ≤ 6·log n` for `n ≥ 2` (private numeric: `√2(n⁴+1) ≤ n⁶`, `Real.log_le_log`,
  `Real.log_pow`). NOTE `(v+1)` appears — fold `v+1 ≤ 2v`?? NO (v can be < 1). The TARGET has
  `C·v·…` — with `v = 0` handled separately, for `v > 0` use exact `a := (4(C*²+1)v/(nh))⁻¹`
  (drop the `+1` on v) so the bound is `∝ v` ✓.
- Increment: `∫⁻ ofReal((∑|ξᵢ|)²·(CL n⁻⁴/h³)²) ≤ (CL n⁻⁴/h³)²·n·∑ᵢ∫⁻ofReal(ξᵢ²)`
  (Cauchy–Schwarz `(∑|ξᵢ|)² ≤ n∑ξᵢ²`) `= (CL²n⁻⁸h⁻⁶)·n²·v ≤ 64 CL²·v/n ≤ (64CL²/log 2)·v·log n/(nh)`
  (`h⁻⁶ ≤ 64n⁶` from `h ≥ 1/(2n)`; `h ≤ 1`; `log n ≥ log 2`, `n ≥ 2`). Each ξᵢ second moment
  `= v` via the law (`HasLaw` + gaussian variance — or crude `≤` via exp-moment; exact:
  `∫⁻ ofReal(x²) ∂(gaussianReal 0 v) = v` — `gaussianReal` variance lemma
  (`variance_gaussianReal`?/`integral_sq…`; a crude upper `≤ 4v` also suffices — adjust C).
- Assemble `C := 2·6·4((C*)²+1) + 2·64·CL²/Real.log 2 + 1` (or your recomputation).

### 3. `lp_supnorm_rate` (SupNormRate.lean): split `|f̂ − f| ≤ |Z t| + |bias t|`;
bias ≤ `q₁h^β` uniformly (`lp_bias_deterministic`); `(⨆)² ≤ 2(⨆|Z|)² + 2q₁²h^{2β}`;
apply item 2; substitute `h = α(log n/n)^{1/(2β+1)}`:
`log n/(nh) = α⁻¹(log n/n)^{2β/(2β+1)}` and `h^{2β} = α^{2β}(log n/n)^{2β/(2β+1)}`
(rpow algebra exactly as in `lp_pointwise_rate` — mimic `PointwiseRisk.lean`'s hT1/hT2 blocks
with `log n > 0` for `n ≥ 2`). `C := 2C_stoch·(v…)/α + 2q₁²α^{2β} + 1` — note `v : ℝ≥0` is
FIXED before the ∃ in the frozen signature, so it may appear in `C`.

Report final `lake build` status for all three modules + `#print axioms` for the three
public theorems (note any lifted `private` sorry).
