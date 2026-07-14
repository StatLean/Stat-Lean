# Close the 5 sorries in NonparametricStatistics/KernelDensity/{Bias,UniformDensityBound,PointwiseRate}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain `lake build StatLean.NonparametricStatistics.KernelDensity.Bias`
(then `.KernelDensity.UniformDensityBound`, `.KernelDensity.PointwiseRate`; no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/KernelDensity/Bias.lean`,
  `.../UniformDensityBound.lean`, `.../PointwiseRate.lean`. Touch nothing else.
- Goal **0 sorries**, 0 errors. Signatures, tags, docstrings frozen. You MAY add `import
  Mathlib.*` and `private` helpers. Lines ≤ 100. Escape hatch: one lifted `private` sorry +
  `-- TODO(np):` + report. Foreground `lake build` only; never background/poll.
- After green: `#print axioms` on `kde_bias_abs_le`, `holder_density_uniform_bound`,
  `kde_pointwise_rate` → only `propext, Classical.choice, Quot.sound`.
- Do not weaken statements; if false as stated, STOP and report.

## Available API (proved, black boxes)
- `MemHolder.taylor_remainder_abs_le (hβ : 0 < β) (hL : 0 ≤ L) (hf : MemHolder β L f) (x₀ t) :
   |f (x₀+t) − ∑ j ∈ Finset.range (holderIndex β + 1), iteratedDeriv j f x₀ * t^j / j!|
   ≤ L / (holderIndex β)! * |t| ^ β` and `MemHolder.abs_le_growth` (same shape, envelope form),
  `MemHolder.iteratedDeriv_holder` — `SmoothnessClasses/HolderTaylor.lean`.
- `kdeMeanAt_eq_integral_kernel (hn : 0 < n) (hh : 0 < h) (hs : IsIIDSample P X (densityMeasure p))
   (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x) (hK : Measurable K)
   (hint : Integrable fun u => K u * p (x + u*h)) : kdeMeanAt P X K h x = ∫ u, K u * p (x + u*h)`
  — `KernelDensity/LawTransfer.lean` (also `integral_comp_law_densityMeasure`,
  `lintegral_comp_law_densityMeasure`, `isProbabilityMeasure_densityMeasure`).
- `exists_bounded_kernel_of_order (ℓ) : ∃ K Kmax, 0 < Kmax ∧ IsKernelOfOrder K ℓ ∧
   (∀ u, |K u| ≤ Kmax) ∧ ∀ u, u ∉ Set.Icc (-1) 1 → K u = 0` — `KernelDensity/AuxiliaryKernel.lean`.
- `kde_memLp_two`, `kdeMseAt_eq_bias_sq_add_variance`, `kde_variance_le` —
  `KernelDensity/Variance.lean`. Study Variance.lean's PRIVATE lemmas
  (`integral_scale_shift'`, `integrable_affine`, `integrable_comp_law'`) — you cannot import
  them; REPLICATE the ones you need as your own `private` lemmas in Bias.lean.
- From `SmoothnessClasses/HolderTaylor.lean` internals: `(holderIndex β : ℝ) < β` for `0 < β`
  may be private there — re-derive privately if needed (`Nat.ceil` facts).

## Facts about the frozen defs
- `IsHolderDensity β L p` fields: `nonneg`, `integral_one : ∫ x, p x = 1`,
  `holder : MemHolderOn β L p Set.univ` (defeq `MemHolder β L p`).
- `p` is continuous: `hp.holder.contDiffOn` on univ + `contDiffOn_univ` →
  `ContDiff ℝ (holderIndex β) p` → `.continuous` → `Measurable p` — derive, never assume.
- `Integrable p`: from `integral_one` (junk-contrapositive via `integral_undef`).
- `kdeBiasConst β L K = L / (holderIndex β)! * ∫ u, |u|^β * |K u|`;
  `kdeVarianceConst K pmax = pmax * ∫ u, (K u)^2`.

## Proofs

### Bias.lean
1. `integrable_kernel_mul_holder`: dominate `|K u * f (x₀ + u*h)|` by
   `∑ j ∈ range (ℓ+1), |iteratedDeriv j f x₀|/j! * h^j * (|u|^j * |K u|) +
    (L/ℓ! * h^β) * (|u|^β * |K u|)` using `MemHolder.abs_le_growth` (`|u*h|^j = |u|^j h^j`,
   `|u*h|^β = |u|^β h^β` — `abs_mul`, `mul_rpow` on nonnegs, `abs_of_pos hh`). The dominant is
   integrable: finite sum of `hK.integrable_pow j (le)`-derived `|u|^j*|K u|`
   (`Integrable.abs`, `abs_mul`, `abs_pow`) plus `hKβ`. AESM of the product: `K` is a.e.
   strongly measurable (`(hK.integrable_pow 0 (by simp)).1` after massaging `u^0 * K u = K u`)
   and `f` continuous. Close with `Integrable.mono'`.
2. `abs_integral_kernel_taylor_le`: write (with `T u := ∑ j ∈ range (ℓ+1),
   iteratedDeriv j f x₀ * (u*h)^j / j!`):
   `∫ K u * f (x₀+u*h) − f x₀ = ∫ K u * (f (x₀+u*h) − T u)` because
   `∫ K u * T u = f x₀`: expand the finite sum through the integral
   (`integral_finset_sum` — each `u ↦ K u * (u*h)^j` integrable from `integrable_pow`),
   `(u*h)^j = u^j * h^j` (`mul_pow`), pull constants (`integral_const_mul`-with `mul_comm`
   massage), then `j = 0` gives `f x₀ * ∫ K = f x₀` (`hK.integral_eq_one`) and `1 ≤ j ≤ ℓ`
   give `0` (`hK.moment_eq_zero`). Integrability of `K·(f∘affine)` is (1); of `K·T` as above;
   difference integrable (`Integrable.sub`). Then
   `|∫ K u * (f (x₀+u*h) − T u)| ≤ ∫ |K u| * (L/ℓ! * |u*h|^β)`
   (`abs_integral_le_integral_abs`?? — `norm_integral_le_integral_norm` + pointwise
   `MemHolder.taylor_remainder_abs_le`, `integral_mono` with (1)-style integrable majorant)
   `= L/ℓ! * h^β * ∫ |u|^β * |K u| = kdeBiasConst β L K * h^β` (rpow algebra as in (1);
   `mul_comm`/`ring_nf`; `abs_mul`, note `∫ |u|^β*|K u|` matches `hKβ`'s integrand via
   `Real.norm_eq_abs` — the integrand is ALREADY `|u|^β * |K u|` ✓).
3. `kde_bias_abs_le`: `kdeBiasAt = kdeMeanAt − p x₀`; rewrite with
   `kdeMeanAt_eq_integral_kernel` (measurability of `p` derived as above; `hint` from (1) with
   `hp.holder`); conclude by (2) with `f := p`.

### UniformDensityBound.lean
4. `holder_density_uniform_bound`: `obtain ⟨K*, Kmax, hKmax, hord, hbd, hsupp⟩ :=
   exists_bounded_kernel_of_order (holderIndex β)`. Set
   `pmax := L / (holderIndex β)! * ∫ u, |u|^β * |K* u| + Kmax` (positive: first term `≥ 0` by
   integrand nonneg + `hL.le`… mind `L/ℓ! ≥ 0` needs `0 < L`; `Kmax > 0`).
   `hKβ* : Integrable fun u => |u|^β * |K* u|`: majorant `Kmax·(Icc (−1) 1).indicator 1`
   (outside: `K* = 0`; inside: `|u|^β ≤ 1` by `Real.rpow_le_one (abs_nonneg) (|u| ≤ 1) hβ.le`);
   indicator integrable (`MeasureTheory.integrable_indicator_iff`, `measurableSet_Icc`,
   finite measure of `Icc`); AESM from `(hord.integrable_pow 0 _).1`.
   For each density `p` and point `x`: by (2) at `h = 1` (`abs_integral_kernel_taylor_le hβ
   hL.le hp.holder hord hKβ* one_pos x`), `p x ≤ ∫ u, K* u * p (x + u*1) + kdeBiasConst β L K* * 1^β`
   (from `|A − p x| ≤ c` ⇒ `p x ≤ A + c`, `abs_sub_le_iff`; `Real.one_rpow`).
   And `∫ u, K* u * p (x+u) ≤ ∫ u, |K* u| * p (x+u) ≤ Kmax * ∫ u, p (x+u) = Kmax`
   (`integral_mono` with integrability from (1) at `h = 1` and its `.abs`-majorant;
   translation invariance `integral_add_left_eq_self` + `hp.integral_one`;
   `Integrable p` from `integral_one` junk-contrapositive; `p ≥ 0`).
5. Positivity `0 < pmax` and packaging `⟨pmax, _, _⟩`.

### PointwiseRate.lean
6. `kde_pointwise_rate`: `obtain ⟨pmax, hpm, hbdd⟩ := holder_density_uniform_bound β L hβ hL`.
   `refine ⟨(kdeBiasConst β L K)^2 * α^(2*β) + kdeVarianceConst K pmax / α + 1, by positivity, ?_⟩`
   — positivity: `kdeBiasConst ≥ 0` (nonneg integrand: `mul_nonneg (abs_nonneg …)`-integral +
   `hL.le`… derive `0 ≤ kdeBiasConst` as a private lemma via `integral_nonneg`), `α^(2β) ≥ 0`
   (`Real.rpow_nonneg`), `kdeVarianceConst ≥ 0` (`hpm.le`, `integral_nonneg (sq_nonneg …)`),
   so `… + 1 > 0` — if `positivity` balks, assemble by hand (`add_pos_of_nonneg_of_pos`).
   Then intro everything; set `h := α * n^(−1/(2β+1))`; `hh : 0 < h`
   (`Real.rpow_pos_of_pos (n > 0)`, `mul_pos hα`). Chain:
   `kdeMseAt = ofReal(bias²) + variance` (`kdeMseAt_eq_bias_sq_add_variance` with
   `kde_memLp_two hh hs hX hp_meas hp0 hbdd' hKmeas hK2` where `hbdd' := hbdd p hpd`, and
   measurability of `p` derived from `IsHolderDensity` as in Bias)
   `≤ ofReal((C₂ h^β)²) + ofReal(C₁/(n h))` (`kde_bias_abs_le` + `sq_le_sq'`/
   `pow_le_pow_left (abs_nonneg)`… bias² ≤ (C₂h^β)² from `|bias| ≤ C₂h^β` via
   `sq_le_sq' (neg_le… ) (abs_le.mp …)` or `mul_self_le_mul_self (abs_nonneg …)`;
   `kde_variance_le`).
   Arithmetic (real, then `ENNReal.ofReal_add` (nonnegs) + `ENNReal.ofReal_le_ofReal`):
   `(C₂ h^β)² = C₂² α^(2β) n^(−2β/(2β+1))`:
   `(h^β)² = h^(2β)` (`← Real.rpow_natCast … 2`, `← Real.rpow_mul hh.le`, `mul_comm β 2`),
   `h^(2β) = α^(2β) * (n^(−1/(2β+1)))^(2β)` (`Real.mul_rpow hα.le (rpow_nonneg …)`),
   `(n^(−1/(2β+1)))^(2β) = n^(−2β/(2β+1))` (`← Real.rpow_mul (n≥0)`, field algebra
   `(−1/(2β+1))*(2β) = −(2β/(2β+1))` — `ring_nf`/`field_simp` with `2β+1 ≠ 0` from `hβ`).
   `C₁/(n h) = (C₁/α) * n^(−2β/(2β+1))`: `n * h = α * n^(1 − 1/(2β+1)) = α * n^(2β/(2β+1))`
   (`Real.rpow_natCast n 1`-style: `(n:ℝ) = n^(1:ℝ)`, `← Real.rpow_add (n>0)`), then
   `1/(n h) = α⁻¹ * n^(−2β/(2β+1))` (`Real.rpow_neg`), `div_eq_mul_inv` juggling.
   Total `≤ (C₂²α^(2β) + C₁/α) * n^(−2β/(2β+1)) ≤ C * n^(−2β/(2β+1))` (the `+1` slack:
   `n^(−2β/(2β+1)) ≥ 0`, `nlinarith`/`gcongr`).

Report final `lake build` status for all three modules + `#print axioms` for the three named
theorems (note any lifted `private` sorry).
