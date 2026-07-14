# Close the 3 sorries in NonparametricStatistics/LocalPolynomial/SupNorm/{StochasticTerm,Increments,SupNormRate}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain
`lake build StatLean.NonparametricStatistics.LocalPolynomial.SupNorm.Increments` (then
`.SupNorm.StochasticTerm`, `.SupNorm.SupNormRate`; no `srun`). THIS IS AN XL ITEM — order:
Increments (deterministic), then StochasticTerm, then the assembly. Commit after EACH file
compiles 0-sorry so work is banked.

## Hard constraints
- **Only edit** the three `SupNorm/*.lean` files. Touch nothing else.
- Goal **0 sorries**, 0 errors. Signatures/tags/docstrings frozen. You MAY add `import
  Mathlib.*` and `private` helpers. Lines ≤ 100. Escape hatch: NAMED lifted `private` sorries
  + TODO + report. Foreground `lake build` only; never background/poll.
- After green: `#print axioms` on `lp_weight_lipschitz_sum`, `lp_supnorm_stochastic_le`,
  `lp_supnorm_rate` → only `propext, Classical.choice, Quot.sound`.
- Do not weaken statements; if false as stated, STOP and report (the ∃-constants give you
  slack — use it).

## Available API (proved, black boxes)
- WeightBounds: `lp_weight_abs_le` (|Wᵢ| ≤ C*/(nh) on Icc), `lp_weight_sum_abs_le`
  (∑|Wᵢ| ≤ C*), `lp_weight_eq_zero_of_far`, `lpBasis_normSq_le` (∑(z^k/k!)² ≤ e on |z| ≤ 1).
- Quadratic: `lpMatrix_posDef`, `lpMatrix_inv_mulVec_sq_le` (∑(B⁻¹v)² ≤ ∑v²/λ₀²),
  `lpMatrix_isSymm`, `lpMatrix_mulVec_apply`.
- PointwiseRisk (D2 item — may still be in flight; if sorried, transitive taint expected,
  report): `lp_bias_deterministic` (|∑f(xᵢ)Wᵢ(t) − f t| ≤ q₁h^β on Icc).
- ForMathlib/GaussianExpSq + MaxExpSquare (C3 item — same caveat):
  `lintegral_exp_mul_sq_gaussianReal_le (v) (ha : a·4v ≤ 1) : ∫⁻ ofReal (exp (a x²))
  ∂(gaussianReal 0 v) ≤ ofReal √2`;
  `hasLaw_sum_mul_gaussianReal (c) (hmeas hindep hlaw) : HasLaw (fun ω => ∑ i, c i * ξ i ω)
  (gaussianReal 0 ((∑ i, (c i)^2).toNNReal * v)) P`;
  `lintegral_iSup_sq_le_log (hM hα hmeas hexp) : ∫⁻ ofReal (⨆ j, (η j ω)^2) ≤
  ofReal (log (C₀ M)/α₀)`;
  `lintegral_iSup_normSq_gaussian_le (hM hd hmeas hgauss) : ∫⁻ ofReal (⨆ j, ∑ k, (η j ω k)^2)
  ≤ ofReal (4 d vmax log (√2 M d))`.
- Defs: `lpWeight xdat K h ℓ t i = ((n:ℝ)h)⁻¹ · ((lpMatrix …)⁻¹.mulVec (lpBasis ℓ zᵢ) 0) ·
  K zᵢ`, `zᵢ = (xdat i − t)/h`; `lpMatrix = ((n:ℝ)h)⁻¹ • ∑ᵢ K zᵢ • vecMulVec (U zᵢ) (U zᵢ)`;
  `DesignEigenvalueLB`, `DesignDensityBound`, `KernelBoxed` as before.

## Proofs

### 1. Increments.lean — `lp_weight_lipschitz_sum`:
`∃ CL > 0, ∀ n>0, h ∈ [1/(2n), 1], design/eig/dens hyps, t t' ∈ Icc 0 1:
 ∑ i, |Wᵢ(t) − Wᵢ(t')| ≤ CL·|t−t'|/h³`.
Pick `CL := (ℓ+1)^2·(Kmax+LK+1)^3·(a₀+1)^2·(1/lam0+1)^2·64` — or ANY closed form that your
chain yields; recompute freely and set it at the end (`refine ⟨_, by positivity, ?_⟩` with a
`let`-style named constant). Chain per `i` (write `W = (nh)⁻¹·(B_t⁻¹ U(zᵢ))₀·K(zᵢ)`):
- Triple product difference: `|a₁b₁c₁ − a₂b₂c₂| ≤ |a₁−a₂||b₁c₁| + |a₂||b₁−b₂||c₁| +
  |a₂b₂||c₁−c₂|`-style telescoping (private lemma).
- `|K(zᵢ(t)) − K(zᵢ(t'))| ≤ LK·|t−t'|/h` (`hKlip`, `abs_div`, algebra `zᵢ(t) − zᵢ(t') =
  (t'−t)/h`).
- `‖U(zᵢ(t)) − U(zᵢ(t'))‖`: per coordinate `|z^k/k! − z'^k/k!| ≤ k·max(|z|,|z'|)^{k−1}|z−z'|/k!`
  (MVT for monomials or telescoping `z^k − z'^k = (z−z')·∑ z^a z'^b`) — on the RELEVANT set
  both |z|,|z'| ≤ ... careful: `U(zᵢ)` appears only multiplied by `K(zᵢ)` (support |z| ≤ 1),
  but in the DIFFERENCE one of the two may be off-support. Handle via the K-factors: the
  product `(B⁻¹U(z))₀·K(z)` vanishes when |z| > 1; case-split on membership of `zᵢ(t)`,
  `zᵢ(t')` in `[−1,1]` (both out ⇒ term 0; one in: bound the whole product by
  `sup ≤ 2Kmax/λ₀`-scale from `lp_weight_abs_le`-internals AND `|t−t'| ≥ h·(gap)`?? — NO:
  one-in-one-out gives `|zᵢ(t)| ≤ 1 < |zᵢ(t')|` ⇒ `|zᵢ(t) − zᵢ(t')| ≥ |zᵢ(t')| − 1 ≥ 0`…
  crude fix: when exactly one is in-support, `|W(t) − W(t')| = |W(t)| ≤ (2Kmax/λ₀)/(nh)`;
  ALSO `|W(t)| ≤ (2Kmax·LK-ish/λ₀)·|t−t'|/(n h²)`?? need |t−t'|-linear bound: use
  `|K(zᵢ(t))| = |K(zᵢ(t)) − K(zᵢ(t'))| ≤ LK|t−t'|/h` (since `K(zᵢ(t')) = 0`!) ✓✓ ELEGANT —
  so in ALL cases the K-difference factor supplies the `|t−t'|` linearity; organize the
  telescoping so every term carries either a K-difference or a `B⁻¹`-difference or a
  U-difference-times-K-factor (the U-difference term keeps a K(z') factor ⇒ z' in-support ⇒
  `|z| ≤ 1 + |z−z'| ≤ 1 + |t−t'|/h ≤ 1 + 2n·1`?? unbounded!! — refine: if `|z − z'| ≥ 1`
  then `|t−t'|/h ≥ 1` and the CRUDE bound `|W(t)−W(t')| ≤ 2·C*/(nh) ≤ 2C*·|t−t'|/(n h²)` ✓
  works; else `|z| ≤ 2` and the monomial-MVT constant is `k·2^{k−1}/k! ≤ 2^ℓ` ✓ bounded.
  So FIRST case-split on `|t−t'|/h ≥ 1` (crude bound via two `lp_weight_abs_le`) vs `< 1`
  (all base points within distance 2 of the support ⇒ smooth bounds). This kills all
  unboundedness.)
- `B_t⁻¹` difference: resolvent `B_t⁻¹ − B_{t'}⁻¹ = B_t⁻¹ (B_{t'} − B_t) B_{t'}⁻¹`
  (`Matrix.inv_sub_inv'`? — likely absent; derive: `B_t⁻¹(B_{t'} − B_t)B_{t'}⁻¹ =
  B_t⁻¹ − B_{t'}⁻¹` by `Matrix.mul_nonsing_inv`/`nonsing_inv_mul` with both dets units
  (PosDef via `heig` at `t, t'` + `lpMatrix_posDef`) — expand and cancel). Operator bounds:
  `∑ ((B⁻¹v))² ≤ ∑v²/λ₀²` (`lpMatrix_inv_mulVec_sq_le`) and entrywise
  `|B_{t'} − B_t|`-bound: each entry is `(nh)⁻¹ ∑ᵢ (K-diff·U·U + K·U-diff·U + …)` — the SAME
  case-split machinery; count of contributing i: `≤ 2·(2a₀·n·h + …)` (both windows,
  `hdens` on `[t−h, t+h] ∪ [t'−h, t'+h]`; in the `< 1` case `|t − t'| < h ≤ 1` so a single
  window of radius `2h` covers: `≤ a₀·n·4h`-ish ✓). Matrix→vector norms: with everything in
  the `∑ k (·)²`-quadratic form language (no operator-norm API needed): for the SCALAR
  `(M v)₀`: `|(Mv)₀| ≤ √(∑ⱼ M₀ⱼ²)·√(∑v²)` (Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq`).
- Sum over i: only `≤ 8a₀nh`-many nonzero terms (support windows; `hdens`), each
  `≤ (stuff)·|t−t'|/(n h³)`-scale ⇒ total `CL·|t−t'|/h³`. (The stated `h³` gives you ~one
  extra `1/h` of slack over the true `h²`-rate — use it to absorb sloppy steps; also `h ≤ 1`
  lets you upgrade any `1/h^a`, `a ≤ 3`.)

### 2. StochasticTerm.lean — `lp_supnorm_stochastic_le`:
`∃ C > 0, ∀ n ≥ 2, h ∈ [1/(2n), 1], design hyps, P ξ v (meas, indep, HasLaw gaussianReal 0 v):
 ∫⁻ ω, ofReal ((⨆ t : Icc 0 1, |∑ᵢ ξᵢ(ω)·Wᵢ(t)|)²) ≤ ofReal (C·v·log n/(n h))`.
- Grid: `M := n^4`, points `tⱼ := (j:ℝ)/M` for `j : Fin (M+1)` (all in Icc ✓ for j ≤ M).
- Pointwise (per ω): `⨆_{t} |Z t| ≤ (⨆_j |Z tⱼ|) + ⨆-increment` where per t pick j(t) with
  `|t − t_{j(t)}| ≤ 1/M`: `|Z t| ≤ |Z tⱼ| + ∑ᵢ|ξᵢ||Wᵢ(t) − Wᵢ(tⱼ)| ≤ |Z tⱼ| +
  (max_i |ξᵢ|)·CL/(M h³)` (Increments + `∑ᵢ|ξᵢ| ≤ n·max`—NO: `∑ᵢ |ξᵢ| |ΔWᵢ| ≤ (max_i |ξᵢ|)·
  ∑ᵢ|ΔWᵢ|` ✓). So `(⨆_t |Z t|)² ≤ 2(⨆_j |Z tⱼ|)² + 2·(CL/(M h³))²·(max_i ξᵢ²)`
  (`sup_le` calculus on reals: prove the pointwise real inequality then `ofReal`-monotone;
  handle `⨆` over the uncountable Icc via `Real.iSup_le` (bounded above: crude
  `|Z t| ≤ ∑|ξᵢ|·C*/(nh)…` — provide a bound for BddAbove; `Real.iSup` needs care: use
  `ciSup_le` and for the reverse `le_ciSup` with a `BddAbove` instance — establish
  `BddAbove (range (fun t : Icc 0 1 => |Z t|))` from `lp_weight_abs_le`: `|Z t| ≤
  (∑ᵢ|ξᵢ|)·C*/(nh)` uniformly ✓).
- Grid maximum: `η j ω k := (√(n h))⁻¹·∑ᵢ ξᵢ(ω)·(U(zᵢ(tⱼ)) k)·K(zᵢ(tⱼ))`?? — SIMPLER
  (avoid the vector detour): apply the SCALAR `lintegral_iSup_sq_le_log` directly to
  `ηⱼ ω := Z tⱼ ω · √(n h/(v·c₀))`-normalized?? The scalar route needs an exp-moment for
  each `Z tⱼ` — via `hasLaw_sum_mul_gaussianReal` (coefficients `cᵢ := Wᵢ(tⱼ)`):
  `Z tⱼ ~ gaussianReal 0 ((∑ᵢWᵢ(tⱼ)²).toNNReal·v)` and
  `∑ᵢ Wᵢ(tⱼ)² ≤ C*²/(n h)` (sup×ℓ¹ as in D2's variance). Then
  `lintegral_exp_mul_sq_gaussianReal_le` with `a := (4·(C*²/(nh))·v)⁻¹` gives
  `E exp(a·Z tⱼ²) ≤ √2` (check `a·4v' ≤ 1` with `v' ≤ (C*²/(nh))·v` — `toNNReal`
  monotonicity + coe care). Feed `lintegral_iSup_sq_le_log` (M+1 variables, `hα : 0 < a` —
  needs `v > 0`?? if `v = 0`: all ξ a.e. 0 ⇒ LHS 0 ✓ case-split; also `C* > 0` — from
  `Kmax`… hmm `Kmax ≥ 0` and could C* = 0? If `Kmax = 0` then K ≡ 0, all weights 0, LHS 0 ✓
  case-split on `Kmax = 0` too — OR keep `a := (4·(C*²+1)/(nh)·(v+1))⁻¹`-style
  always-positive normalizations with slightly larger constants — RECOMMENDED, fewer cases):
  `∫⁻ ofReal (⨆_j (Z tⱼ)²) ≤ ofReal (log (√2 (M+1)) / a) = ofReal (4(C*²+1)(v+1)/(nh)·
  log (√2(n⁴+1)))` and `log (√2(n⁴+1)) ≤ 5·log n + 1 ≤ 6·log n`-ish for `n ≥ 2`
  (`Real.log_le_log`, `log_mul`, `log_pow`, numeric: `√2(n⁴+1) ≤ n⁶` for n ≥ 2 ✓ then
  `≤ 6 log n` ✓ — private numeric lemma with `Real.log_le_log_of_le` + `Real.log_rpow`-free
  `Real.log_pow`).
- Increment second moment: `∫⁻ ofReal (max_i ξᵢ²) ≤ ofReal (4·v·log (√2 n))` — the SCALAR
  max lemma again with `a := 1/(4v)`-style (per-ξ exp-moment from
  `lintegral_exp_mul_sq_gaussianReal_le` at the exact law ✓), OR crude
  `max ≤ ∑`: `∫⁻ ofReal(max ξᵢ²) ≤ ∑ᵢ ∫⁻ ofReal(ξᵢ²) = n·v` — with the prefactor
  `(CL/(M h³))² = CL²/(n⁸ h⁶)` and `h ≥ 1/(2n)`: `h⁻⁶ ≤ 64 n⁶` ⇒ contribution
  `≤ 2·CL²·64·n⁶·n·v/n⁸ = 128 CL² v/n ≤ 128·CL²·v·log n/(n h)` (`h ≤ 1`, `log n ≥ log 2 > 0`
  for n ≥ 2 — mind `log 2 < 1`: use `… ≤ (128 CL²/log 2)·v·log n/(nh)` — fold into C) ✓
  CRUDE SUFFICES — no max-lemma needed for the increment part.
- Assemble `C := 2·[4(C*²+1)·6 + 128·CL²/log 2 + 1]`-shape (recompute freely); `ofReal`
  algebra; `∑ᵢWᵢ(tⱼ)²` bound needs `tⱼ ∈ Icc 0 1` ✓.

### 3. SupNormRate.lean — `lp_supnorm_rate`: split per ω,t:
`|f̂(t) − f t| ≤ |∑ᵢ ξᵢWᵢ(t)| + |∑ᵢ f(xᵢ)Wᵢ(t) − f t|` (Y = f + ξ decomposition of
`lpEstimator` — same expansion as D2). Bias term ≤ `q₁h^β` uniformly (`lp_bias_deterministic`
per t; if D2 hasn't landed, replicate its ≈15-line proof privately — it only uses
WeightBounds + Reproduction + HolderTaylor, all closed). So
`(⨆_t |f̂ − f|)² ≤ 2(⨆_t |Z t|)² + 2 q₁² h^(2β)` (sup-calculus as above);
`∫⁻ ω ofReal(…) ≤ 2·ofReal(C_stoch·v·log n/(nh)) + 2·ofReal(q₁²h^(2β))`.
Substitute `h = α(log n/n)^(1/(2β+1))`:
`h^(2β) = α^(2β)·(log n/n)^(2β/(2β+1))` and `log n/(nh) = α⁻¹·(log n/n)^(2β/(2β+1))`
(same rpow algebra as the pointwise rates: `log n/(n·h) = α⁻¹ (log n/n)·(log n/n)^(−1/(2β+1))
= α⁻¹ (log n/n)^(2β/(2β+1))` ✓ — needs `log n > 0` i.e. `n ≥ 2` ✓). Fold
`C := 2 C_stoch·(v+1)/α + 2 q₁² α^(2β) + 1`?? — v is NOT fixed before ∃C in the statement!
CHECK the stub: `v : ℝ≥0` is bound INSIDE (after ∃C)… re-read: the signature has
`{v : ℝ≥0}` as a theorem-level implicit BEFORE the ∃?? — look: `lp_supnorm_rate {β L α : ℝ}
{K : ℝ → ℝ} {Kmax lam0 a₀ LK : ℝ} {v : ℝ≥0}` — YES v is fixed before ∃C ✓ good, include `v`
in `C`.

Report final `lake build` status for all three modules + `#print axioms` for the three named
theorems (note any lifted `private` sorry and any C3/D2 transitive taint).
