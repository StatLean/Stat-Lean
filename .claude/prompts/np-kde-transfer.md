# Close the 9 sorries in NonparametricStatistics/KernelDensity/{LawTransfer,Variance}.lean + Regression/NWKernelRepresentation.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON the
cluster — iterate with plain `lake build StatLean.NonparametricStatistics.KernelDensity.LawTransfer`
(then `.KernelDensity.Variance`, `StatLean.NonparametricStatistics.Regression.NWKernelRepresentation`;
no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/KernelDensity/LawTransfer.lean`,
  `.../KernelDensity/Variance.lean`, `StatLean/NonparametricStatistics/Regression/NWKernelRepresentation.lean`.
  Touch nothing else (NOT any `Defs.lean`).
- Goal **0 sorries**, 0 errors. Keep theorem signatures, tags, docstrings UNCHANGED. You MAY add
  `import Mathlib.*` lines and `private` helper lemmas. Lines ≤ 100. If a piece resists, lift it
  to a `private lemma` with one `sorry` + `-- TODO(np):` and report.
- After green: `#print axioms` on `kde_variance_le`, `kdeMeanAt_eq_integral_kernel`,
  `nadarayaWatson_eq_kde_ratio` → only `propext, Classical.choice, Quot.sound`.
- Do not weaken statements. If you believe one is false as stated, STOP and report why.

## Key definitions (frozen, in `KernelDensity/Defs.lean` / `SmoothnessClasses/Defs.lean` /
`Regression/Defs.lean`)
- `densityMeasure p = volume.withDensity fun x => ENNReal.ofReal (p x)`.
- `IsIIDSample P X μ`: fields `indep : iIndepFun X P`, `law : ∀ i, HasLaw (X i) μ P`.
- `kdeData xdat K h x = ((n:ℝ)*h)⁻¹ * ∑ i, K ((xdat i - x)/h)`;
  `kde X K h ω x = kdeData (fun i => X i ω) K h x`;
  `kde2Data xdat ydat K h x y = ((n:ℝ)*h^2)⁻¹ * ∑ i, K ((xdat i - x)/h) * K ((ydat i - y)/h)`.
- `kdeMeanAt P X K h x = ∫ ω, kde X K h ω x ∂P`; `kdeBiasAt … = kdeMeanAt … - p x`;
  `kdeVarianceAt P X K h x = ∫⁻ ω, ENNReal.ofReal ((kde X K h ω x - kdeMeanAt P X K h x)^2) ∂P`;
  `kdeMseAt` analogous with `- p x`.
- `kdeVarianceConst K pmax = pmax * ∫ u, (K u)^2`.
- `IsKernelOfOrder K ℓ`: `integrable_pow : ∀ j ≤ ℓ, Integrable fun u => u^j * K u`;
  `integral_eq_one : ∫ u, K u = 1`; `moment_eq_zero : ∀ j, 1 ≤ j → j ≤ ℓ → ∫ u, u^j*K u = 0`.
- `nadarayaWatson xdat Y K h x = if (∑ i, K ((xdat i - x)/h)) = 0 then 0 else (∑ i, Y i * K (…))/(∑ i, K (…))`.

## Useful Mathlib API (verify names with `exact?`/loogle)
- `ProbabilityTheory.HasLaw` (fields `aemeasurable`, `map_eq`; API `HasLaw.integral_comp`,
  `HasLaw.lintegral_comp` or via `map_eq ▸ integral_map`/`lintegral_map`), module
  `Mathlib.Probability.HasLaw`.
- `MeasureTheory.integral_withDensity_eq_integral_toReal_smul` /
  `integral_withDensity_eq_integral_smul` (measurable `f : α → ℝ≥0`),
  `lintegral_withDensity_eq_lintegral_mul`, `ENNReal.toReal_ofReal`.
- `MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hf : Integrable f μ) (h : 0 ≤ᵐ[μ] f)`.
- `MeasureTheory.integral_undef` (junk value on non-integrable) — gives `Integrable p` from
  `∫ p = 1 ≠ 0` by contraposition.
- Affine change of variables on `volume`: `MeasureTheory.integral_comp_mul_left`
  (`Measure.integral_comp_mul_left?`), `integral_comp_add_right`, `Real.map_volume_add_left`,
  `Real.smul_map_volume_mul_left`, `MeasurePreserving.integral_comp`. Target identity:
  `∫ z, g ((z - x)/h) dz = h * ∫ u, g u du` for `h > 0` (compose translate + scale; watch
  `|h|` vs `h`).
- Variance: `ProbabilityTheory.variance`, `variance_def'`/`variance_eq_integral...`,
  `ProbabilityTheory.IndepFun.variance_sum` (pairwise independence via `iIndepFun.indepFun`),
  `MemLp.integrable_sq` (needs `import Mathlib.MeasureTheory.Function.L2Space` — already added),
  `MemLp.const_mul`, `memLp_finset_sum'`, `MemLp.sub`, `memLp_const`,
  `MemLp.integrable` (`2 ≥ 1` on a probability measure).
- `eLpNorm`-side: `MemLp` = `AEStronglyMeasurable ∧ eLpNorm f p μ < ∞`;
  `eLpNorm_eq_lintegral_rpow_enorm`-family to convert a finite `∫⁻ (K …)²` bound into `MemLp 2`.
- `Finset.sum_div`, `Finset.mul_sum`, `intervalIntegral` NOT needed here.

## Proofs

### LawTransfer.lean
1. `isProbabilityMeasure_densityMeasure`: `Integrable p` from `h1` (contrapose `integral_undef`).
   `⟨by rw [densityMeasure]; simp [withDensity_apply, MeasurableSet.univ]; …⟩` — concretely:
   `(densityMeasure p) univ = ∫⁻ x, ofReal (p x) = ofReal (∫ x, p x) = ofReal 1 = 1` using
   `ofReal_integral_eq_lintegral_ofReal` (with `0 ≤ᵐ p` from `h0`) then `h1`.
2. `integral_comp_law_densityMeasure`: `hX.integral_comp`-route: needs
   `AEStronglyMeasurable g (densityMeasure p)` (from `hg.aestronglyMeasurable`); then
   `∫ g ∂(densityMeasure p) = ∫ z, g z * p z`: `integral_withDensity_eq_integral_smul` with the
   ℝ≥0-valued density `fun x => (p x).toNNReal` — reconcile `ofReal (p x) = ((p x).toNNReal : ℝ≥0∞)`
   (`ENNReal.ofReal` is def'd via `toNNReal`; `rfl` or `ENNReal.ofReal_eq_coe_nnreal`) and
   `(p x).toNNReal • g x = p x * g x` for `p x ≥ 0` (`Real.coe_toNNReal`, `smul_eq_mul`,
   `mul_comm`). Alternatively, if `HasLaw.integral_comp` has integrability side conditions that
   are awkward, go through `hX.map_eq ▸ integral_map hX.aemeasurable hg'.aestronglyMeasurable`.
   Integrability transfers: the goal-side `hint` gives Integrable of `g·p` over volume; convert
   to `Integrable g (densityMeasure p)` via `integrable_withDensity_iff_integrable_smul`-family.
3. `lintegral_comp_law_densityMeasure`: `← hX.map_eq`, `lintegral_map hg hX.aemeasurable`
   (or `lintegral_map'` for AEMeasurable), then `lintegral_withDensity_eq_lintegral_mul`
   (measurable density `ENNReal.ofReal ∘ p` from `hp.ennreal_ofReal`; note the multiplication
   ORDER in that lemma — adjust with `mul_comm` inside the lintegral).
4. `kdeMeanAt_eq_integral_kernel`: unfold `kdeMeanAt`, `kde`, `kdeData`;
   `integral_finset_sum`-after-`integral_const_mul`: `∫ ω, (nh)⁻¹ ∑ i, K ((X i ω − x)/h)
   = (nh)⁻¹ ∑ i, ∫ ω, K ((X i ω − x)/h)`. Each `∫ ω, K ((X i ω - x)/h) ∂P
   = ∫ z, K ((z-x)/h) ∂(densityMeasure p)` (by `(hs.law i).integral_comp` with
   `g := fun z => K ((z-x)/h)`, measurable by `hK.comp (measurable stuff)`)
   `= ∫ z, K ((z-x)/h) * p z` (by (2); its `hint` in `z`-form follows from the theorem's `hint`
   in `u`-form by the affine change of variables `z = x + u*h`, `h > 0`) `= h * ∫ u, K u * p (x+u*h)`
   (same change of variables, forward direction). Sum over `i` (all terms equal): `n` copies;
   `(nh)⁻¹ * n * h = 1` (`hn`, `hh`; `field_simp`). NOTE the per-`i` integrability over `P`
   (needed by `integral_finset_sum`): transfer `hint` back through the law — package as a
   `private lemma` `integrable_comp_kernel` first.

### Variance.lean
5. `kde_memLp_two`: `kde X K h · x = (nh)⁻¹ • ∑ i, (K ((X i · - x)/h))`; `MemLp.const_mul` +
   `memLp_finset_sum'`. Per-`i`: `MemLp (fun ω => K ((X i ω - x)/h)) 2 P`:
   AEStronglyMeasurable from `hK.comp ((hX i).sub_const x |>.div_const h)`.
   Second moment: `∫⁻ ω, ‖K (…)‖ₑ^2 = ∫⁻ z, ofReal ((K ((z-x)/h))^2) ∂(densityMeasure p)`
   (lintegral law-transfer, lemma (3) of LawTransfer with `g := fun z => ofReal ((K ((z-x)/h))^2)`;
   mind `‖a‖ₑ^2 = ofReal (a^2)` — `enorm_eq...`/`Real.enorm_eq_ofReal_abs` + `sq_abs`)
   `= ∫⁻ z, ofReal ((K ((z-x)/h))^2) * ofReal (p z) ≤ ofReal (pmax) * ∫⁻ z, ofReal ((K ((z-x)/h))^2)`
   — wait, the density multiplies pointwise: bound `ofReal (p z) ≤ ofReal pmax` (`hbdd`,
   `ENNReal.ofReal_le_ofReal`) THEN change variables in the lintegral
   (`lintegral_map`-free route: `Measure.map` of volume under affine or
   `lintegral_comp_mul_left`-style lemmas; or convert to Bochner via `hK2` and
   `ofReal_integral_eq_lintegral_ofReal`): total `≤ ofReal (pmax * h * ∫ (K u)^2) < ∞`.
   Conclude `eLpNorm < ∞` via `eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top`-style
   (`p = 2`, `toReal 2 = 2`, `rpow_natCast`).
6. `kdeVarianceAt_eq_ofReal_variance`: `kdeVarianceAt = ∫⁻ ofReal ((f - c)^2)` with
   `f := kde X K h · x`, `c := kdeMeanAt P X K h x = ∫ f`. `(f - c)` is `MemLp 2` (`hL2.sub
   (memLp_const c)`), so `(f-c)^2` is Integrable (`MemLp.integrable_sq`), nonneg; hence
   `∫⁻ ofReal ((f-c)^2) = ofReal (∫ (f-c)^2)` (`ofReal_integral_eq_lintegral_ofReal`, symm) and
   `∫ (f-c)^2 = variance f P` (`variance_def'` on probability measures /
   `ProbabilityTheory.variance_eq_integral` with mean `c` — find exact pin name; possibly
   `variance = ∫ x^2 - (∫x)^2` form, then `ring_nf` through `integral_sub`/`integral_pow`…;
   the cleanest is a `variance_eq_integral_sub_sq`-style lemma taking the mean as argument).
7. `kdeMseAt_eq_bias_sq_add_variance`: expand `(f - p x)^2 = (f - c)^2 + 2(c - p x)(f - c) +
   (c - p x)^2` with `c := kdeMeanAt …`; all three integrable (MemLp 2 as in (6)); the cross
   term integrates to `0` (`∫ (f - c) = 0` by `integral_sub hL2.integrable… + integral_const`).
   Both sides through `ofReal_integral_eq_lintegral_ofReal`; assemble with
   `ENNReal.ofReal_add` (both parts nonneg: `sq_nonneg`, `integral_nonneg`).
8. `kde_variance_le`: via (6) reduce to `variance (kde …) P ≤ kdeVarianceConst K pmax / (n*h)`
   — then `kdeVarianceAt = ofReal variance ≤ ofReal bound` (`ENNReal.ofReal_le_ofReal`).
   Degenerate `n = 0`: `kde ≡ 0` (empty sum, `(0*h)⁻¹ * 0`), variance `0`, RHS `≥ 0`?? —
   RHS is `ofReal (C/(0*h)) = ofReal (C/0) = ofReal 0 = 0` and LHS `= 0` ✓ handle separately
   (`Nat.eq_zero_or_pos`). Main case: `kde = (nh)⁻¹ • ∑ Kᵢ`; `variance_smul`-family
   (`variance_const_mul`? exact name) + `IndepFun.variance_sum` (from `hs.indep.indepFun` for
   `i ≠ j`, each summand `MemLp 2` by the per-i part of (5)) + identical laws ⇒ all summand
   variances equal that of `i = 0`-analogue: each
   `variance (fun ω => K ((X i ω - x₀)/h)) P ≤ E K² = ∫ K²((z-x₀)/h) p(z) dz ≤ pmax·h·∫K²`
   (`variance_le_integral_sq`? if absent: `variance = E X² - (E X)² ≤ E X²`; law transfer +
   change of variables as in (5)). Total: `(nh)⁻²·n·(pmax·h·∫K²) = kdeVarianceConst/(nh)`
   (`field_simp`, `ring`).

### NWKernelRepresentation.lean
9. `nadarayaWatson_eq_kde_ratio`: `hden` rules out the `if`-branch: `kdeData xdat K h x =
   ((n:ℝ)*h)⁻¹ * S` with `S := ∑ i, K ((xdat i - x)/h)`; `hden` forces `S ≠ 0` AND
   `((n:ℝ)*h)⁻¹ ≠ 0` (product nonzero), in particular `(n:ℝ) ≠ 0`. Key integral, per `i`:
   `∫ y, y * K ((ydat i - y)/h) dy = h * ydat i` — change of variables `y = ydat i - h*u`
   (reflect + translate + scale; `∫ y, g (c - y) dy = ∫ u, g u du` via
   `integral_comp_sub_left`/`Measure.map` of neg+translate — `Real.volume` invariance under
   `y ↦ c - y`: `MeasureTheory.integral_comp_neg`? + `integral_comp_add_left`; then scale by `h`),
   giving `∫ u, (ydat i - h*u) * K u * h du`-shape `= h*(ydat i * ∫K - h*∫uK) = h * ydat i`
   (`hK.integral_eq_one`, `hK.moment_eq_zero 1` — note `u^1 = u`, `pow_one`). Integrability of
   `y ↦ y * K ((ydat i - y)/h)`: from `hK.integrable_pow 0` and `hK.integrable_pow 1` through
   the same change of variables (the integrand transforms into a combination of `K u` and
   `u*K u`). Then `∫ y, y * kde2Data … x y dy = ((n:ℝ)*h^2)⁻¹ * ∑ i, K ((xdat i - x)/h) * (h * ydat i)`
   (swap `∫`/`∑` by `integral_finset_sum`, pull constants) `= ((n:ℝ)*h)⁻¹ * ∑ i, ydat i * K (…)`.
   Divide by `kdeData … = ((n:ℝ)*h)⁻¹ * S`: the `((n:ℝ)*h)⁻¹` cancels (`mul_div_mul_left`,
   nonzero), leaving exactly the `else`-branch of `nadarayaWatson`. `simp [nadarayaWatson, hS]`,
   `field_simp`.

Report final `lake build` status for all three modules + `#print axioms` for the three named
theorems (note any lifted `private` sorry).
