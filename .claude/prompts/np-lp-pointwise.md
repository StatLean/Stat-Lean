# Close the 5 sorries in NonparametricStatistics/LocalPolynomial/{PointwiseRisk,L2Risk}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain
`lake build StatLean.NonparametricStatistics.LocalPolynomial.PointwiseRisk` (then
`.LocalPolynomial.L2Risk`; no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/LocalPolynomial/PointwiseRisk.lean` and
  `.../LocalPolynomial/L2Risk.lean`. Touch nothing else (NOT `Quadratic.lean` even if it still
  carries its two amended sorries — do NOT use `isLPSolution_iff_normal`/`isLPSolution_inv_mulVec`
  anywhere, so your results stay sorry-axiom-clean).
- Goal **0 sorries**, 0 errors. Signatures/tags/docstrings frozen. You MAY add `import
  Mathlib.*` and `private` helpers. Lines ≤ 100. Escape hatch: one lifted `private` sorry +
  TODO + report. Foreground `lake build` only.
- After green: `#print axioms` on `lp_bias_deterministic`, `lp_variance_le`, `lp_mse_le`,
  `lp_pointwise_rate`, `lp_l2_rate` → only `propext, Classical.choice, Quot.sound`
  (NO `sorryAx` — hence the ban on the two amended Quadratic lemmas).
- Do not weaken statements; if false as stated, STOP and report.

## Available API (proved, black boxes)
- WeightBounds.lean (all closed): `lp_weight_abs_le (hn hh hlam ha₀ heig hbox ht i) :
   |lpWeight xdat K h ℓ t i| ≤ lpWeightConst Kmax lam0 a₀ / ((n:ℝ)*h)`;
  `lp_weight_sum_abs_le (hn hhl hlam ha₀ heig hbox hdens ht) : ∑ i, |lpWeight …| ≤ lpWeightConst …`;
  `lp_weight_eq_zero_of_far (hh hbox hfar) : lpWeight … i = 0` when `h < |xdat i − t|`;
  `lpBasis_normSq_le`.
- Reproduction.lean (closed): `lp_weight_reproduce_monomial (hpd) (hh : h ≠ 0) (hk : k ≤ ℓ) :
   ∑ i, (xdat i − t)^k * lpWeight … i = if k = 0 then 1 else 0`;
  `lp_weight_sum_one (hpd) (hh : h ≠ 0)`; `lp_weight_reproduce_poly`.
- Quadratic.lean (closed parts): `lpMatrix_posDef (hlam : 0 < lam0)
   (hLB : ∀ v, lam0 * ∑ k (v k)^2 ≤ ∑ k, v k * (lpMatrix …).mulVec v k) : (lpMatrix …).PosDef`
  — note `DesignEigenvalueLB xdat K h ℓ lam0` gives `hLB` at each `t ∈ Icc 0 1`.
  Also `lpMatrix_isSymm`, `lpMatrix_inv_mulVec_sq_le`, `isLPSolution_unique`,
  `lpEstimator_eq_isLPSolution`, `isLinearEstimator_lpEstimator` — but NOT the two banned ones.
- HolderTaylor.lean (closed): `MemHolderOn.taylor_remainder_abs_le_Icc (hab : a < b)
   (hβ : 0 < β) (hL : 0 ≤ L) (hf : MemHolderOn β L f (Icc a b)) (hx : x ∈ Icc a b)
   (hy : y ∈ Icc a b) : |f y − ∑ j ∈ range (ℓ+1), iteratedDerivWithin j f (Icc a b) x
   * (y−x)^j / j!| ≤ L/ℓ! * |y−x|^β` with `ℓ = holderIndex β`.
- Defs: `lpEstimator xdat Y K h ℓ t = ∑ i, Y i * lpWeight xdat K h ℓ t i`;
  `lpBiasConst β L Kmax lam0 a₀ = lpWeightConst Kmax lam0 a₀ * L / ℓ!`;
  `lpVarConst σmax2 Kmax lam0 a₀ = σmax2 * lpWeightConst²`;
  `lpRateConst β L α σmax2 Kmax lam0 a₀ = lpBiasConst² * α^(2β) + lpVarConst / α`.

## Proofs (PointwiseRisk.lean)

### 1. `lp_bias_deterministic`
`|∑ i, f (xdat i) * W_i(t) − f t| ≤ q₁ h^β` (`W_i := lpWeight xdat K h (holderIndex β) t i`).
- `0 < h` from `hhl` + `hn` (`1/(2n) > 0`).
- `hpd := lpMatrix_posDef hlam (heig t ht)`.
- Insert the within-interval Taylor polynomial `T y := ∑ j ∈ range (ℓ+1),
  iteratedDerivWithin j f (Icc 0 1) t * (y − t)^j / j!`:
  `∑ i, T (xdat i) * W_i = f t`: expand `T`, swap sums (`Finset.sum_comm`), inner sums are
  `∑ i (xdat i − t)^j W_i = if j = 0 then 1 else 0` (`lp_weight_reproduce_monomial hpd hh.ne'
  (Finset.mem_range-bound)`), so only `j = 0` survives: `iteratedDerivWithin 0 f _ t * 1/0!
  = f t` (`iteratedDerivWithin_zero`).
- So `∑ f(xdatᵢ)W_i − f t = ∑ (f (xdat i) − T (xdat i)) * W_i` (algebra with `Finset.sum_sub_distrib`).
- `|∑ …| ≤ ∑ |f (xdat i) − T (xdat i)| * |W_i|` (`Finset.abs_sum_le_sum_abs`, `abs_mul`).
- Per `i`: if `h < |xdat i − t|`: `W_i = 0` (`lp_weight_eq_zero_of_far`) — term drops.
  Else `|xdat i − t| ≤ h`: `|f (xdat i) − T (xdat i)| ≤ L/ℓ! * |xdat i − t|^β ≤ L/ℓ! * h^β`
  (`taylor_remainder_abs_le_Icc` with `hab : (0:ℝ) < 1` `one_pos`, `hx (hx i)`, `ht`;
  `Real.rpow_le_rpow (abs_nonneg _) (le) hβ.le`). So
  `∑ ≤ L/ℓ! h^β * ∑ |W_i| ≤ L/ℓ! h^β * C* = q₁ h^β` (`lp_weight_sum_abs_le`,
  `lpBiasConst` unfold — mind the order `C* * L / ℓ!`: `ring_nf`). Implementation: split the
  sum over the `far`/`near` index sets or bound per-term with the far-case giving `0 ≤ …`.

### 2. `lp_variance_le`
`∫⁻ ω, ofReal ((S ω − ∫ S)²) ∂P ≤ ofReal (q₂/(n h))` with
`S ω := lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t`.
- `S ω = A + Z ω` where `A := ∑ i f (xdat i) W_i` (constant) and `Z ω := ∑ i, ξ i ω * W_i`
  (expand `lpEstimator`, `add_mul`, `Finset.sum_add_distrib`).
- Each `ξ i ∈ L²`: from `hξ2 i` (`∫⁻ ofReal (ξ²) ≤ ofReal σmax2 < ⊤`) + measurability ⇒
  `MemLp (ξ i) 2 P` (`memLp_two_iff_integrable_sq`-route or `eLpNorm` bridge: replicate the
  pattern in `KernelDensity/Variance.lean`'s `kernel_summand_memLp`). Hence `Z` is `MemLp 2`
  (`memLp_finset_sum'`, `MemLp.const_mul` — mind `ξ i ω * W_i` = `W_i • ξ i ω` shape:
  `mul_comm` congruence) and Bochner-integrable; `∫ S = A + ∫ Z` and
  `∫ Z = ∑ W_i ∫ ξ i = 0` (`integral_finset_sum`, `integral_const_mul`… wait the scalar is on
  the right: `integral_mul_const`; `hξ0`). So `S − ∫ S = Z` pointwise-in-ω (funext-level
  rewriting under the lintegral: `lintegral_congr`).
- `∫⁻ ofReal (Z²) = ofReal (variance Z)`… cleaner: `= ofReal (∫ Z²)`
  (`ofReal_integral_eq_lintegral_ofReal` backwards, `Z² integrable` = `MemLp.integrable_sq`).
- `∫ Z² = ∑ i, W_i² * ∫ ξᵢ²`: expand the square of the finite sum
  (`Finset.sum_mul_sum`, `integral_finset_sum` of products); off-diagonal terms vanish:
  `∫ ξ i ξ j = 0` for `i ≠ j` (`IndepFun.integral_mul_eq_mul_integral`?? — check exact name
  `ProbabilityTheory.IndepFun.integral_mul_eq_integral_mul_integral`? — from
  `hξi.indepFun hij` + `hξ0`; each `ξ` is `L²` so products are `L¹` (`MemLp.integrable_mul`)).
  Alternatively reuse `IndepFun.variance_sum` on `fun i ω => ξ i ω * W_i` (variance route as
  in KernelDensity/Variance.lean — pick whichever lands faster).
- Bound: `∑ i W_i² ∫ξᵢ² ≤ σmax2 * ∑ i W_i²` (each `∫ ξᵢ² ≤ σmax2` — from `hξ2` via the
  ofReal bridge `ENNReal.ofReal_le_ofReal_iff` + `ofReal_integral_eq_lintegral_ofReal`;
  needs `∫ξᵢ² ≥ 0` ✓) and `∑ W_i² ≤ (sup |W_i|) * ∑ |W_i| ≤ (C*/(n h)) * C*`
  (`sq = |W|·|W| ≤ sup·|W|`, `Finset.sum_le_sum` + pulls; `lp_weight_abs_le`,
  `lp_weight_sum_abs_le`; `0 < h` derived). Assemble `= q₂/(n h)` (`lpVarConst`, `field_simp`).

### 3. `lp_mse_le`: pointwise MSE = bias² + variance:
`∫⁻ ω ofReal ((S ω − f t)²) = ofReal ((A − f t)²) + ∫⁻ ω ofReal (Z ω²)` — expand
`(A + Z − f t)² = (A − f t)² + 2(A − f t)Z + Z²`, integrate; cross term zero (`∫ Z = 0`);
work via `ofReal_integral_eq_lintegral_ofReal` on the integrable pieces (all L² ✓) and
`ENNReal.ofReal_add` (nonnegs). Then apply (1) and (2):
`≤ ofReal (q₁² h^(2β)) + ofReal (q₂/(nh))` — `(q₁ h^β)² = q₁² h^(2β)`
(`Real.rpow_natCast`, `← Real.rpow_mul hh.le`, `two_mul`); `ENNReal.ofReal_add` reassemble.

### 4. `lp_pointwise_rate`: substitute `hform : h = α * n^(−1/(2β+1))` into (3):
identical rpow arithmetic to the KDE pointwise rate (see np-kde-bias-rate.md §6 if that
landed — else redo): `h^(2β) = α^(2β) n^(−2β/(2β+1))` and `1/(n h) = α⁻¹ n^(−2β/(2β+1))`;
`lpRateConst` unfold; `ENNReal.ofReal_le_ofReal` + `nlinarith`/`gcongr` on reals
(nonnegativity: `lpBiasConst ≥ 0`? — `lpWeightConst ≥ 0` needs `Kmax ≥ 0`: derive from
`hbox.1` at `u := 2` (`K 2 = 0` by support, so `0 ≤ |K 2| ≤ Kmax`) — private lemma;
`hL`, `hσ`, `hα` for the rest).

## Proof (L2Risk.lean)

### 5. `lp_l2_rate`: `∫⁻ ω ∫⁻ t in Icc 0 1, ofReal ((S ω t − f t)²) ≤ ofReal (lpRateConst * n^(−2β/(2β+1)))`.
The signature includes `hKmeas : Measurable K` (LEAN-ONLY) precisely so Tonelli applies.
- Joint measurability of `(ω, t) ↦ lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h ℓ t`:
  it is `∑ i, (f (xdat i) + ξ i ω) * lpWeight xdat K h ℓ t i` — a finite sum of products of
  an ω-measurable factor (`hξm i`, composed with `measurable_fst`) and a t-measurable factor
  composed with `measurable_snd`. `t ↦ lpWeight … t i` is measurable: `lpBasis` continuous in
  `t`-composed-affine; `t ↦ K ((xdat i − t)/h)` measurable (`hKmeas.comp` of the affine map);
  `lpMatrix` entries = `(n h)⁻¹ • ∑ i (K …) • (lpBasis · * lpBasis ·)` measurable; the matrix
  INVERSE is entrywise measurable because `A⁻¹ = Ring.inverse A.det • A.adjugate` — `det` and
  `adjugate` entries are polynomial in the entries (`Matrix.det_apply`,
  `Matrix.adjugate_apply`/`adjugate_fin_succ…` — safest: `Matrix.inv_def` rewrite, then
  `Measurable.const_smul`-style composition; `Ring.inverse x = x⁻¹` on a field
  (`Ring.inverse_eq_inv'`), `measurable_inv` on ℝ, `Finset.measurable_sum`,
  `Measurable.mul`). Package as a `private lemma lpWeight_measurable_in_t`.
- Tonelli: `lintegral_lintegral_swap` (with `ν := volume.restrict (Set.Icc (0:ℝ) 1)`;
  `SigmaFinite` ✓; AEMeasurable of the uncurried `ofReal ((…)²)` from the above via
  `Measurable.ennreal_ofReal`, `.pow`, `.sub` — `f` continuous on the relevant set? `f t` as
  a function of `t`: from `hf.contDiffOn.continuousOn`… careful: `f` is only continuous ON
  `Icc 0 1`; on the restrict-measure that is enough (`ContinuousOn.aemeasurable`
  `measurableSet_Icc` — use `AEMeasurable` throughout the uncurry, with
  `(ContinuousOn.aemeasurable …).comp_aemeasurable`? — the uncurried function restricted to
  `univ ×ˢ Icc 0 1`… if the aemeasurability plumbing on the product gets sticky, use
  `AEMeasurable.prod_mk`-free route: `Measurable.aemeasurable` after replacing `f` by a
  measurable extension: actually simplest — `f` appears only through `f t` and
  `f (xdat i)`: rewrite the integrand as `(A t + Z ω t − f t)²` and note
  `t ↦ A t − f t` (bias) needs f-measurability on Icc: `ContinuousOn.aemeasurable` on the
  restricted measure composed through `measurable_snd`: `AEMeasurable.comp_quasiMeasurePreserving`?
  — if this corner resists, lift exactly the aemeasurability step to a private lemma sorry
  + TODO and report).
- After the swap: `∫⁻ t in Icc, (∫⁻ ω, ofReal ((S ω t − f t)²) ∂P) ≤
  ∫⁻ t in Icc, ofReal (q₁² h^(2β) + q₂/(n h))` by (3) `lp_mse_le` pointwise in `t ∈ Icc`
  (`lintegral_mono_ae`/`setLIntegral_mono` with `ht : t ∈ Icc 0 1` available from the
  restricted measure — `setLIntegral_mono_ae` + `ae_restrict_iff` + `measurableSet_Icc`),
  then `lintegral_const`-on-restrict: `= ofReal (…) * volume (Icc 0 1) = ofReal (…)`
  (`Real.volume_Icc`, `sub_zero`, `ENNReal.ofReal_one`, `mul_one`). Conclude with the same
  rpow arithmetic as (4).

Report final `lake build` status for both modules + `#print axioms` for the five named
theorems (note any lifted `private` sorry).
