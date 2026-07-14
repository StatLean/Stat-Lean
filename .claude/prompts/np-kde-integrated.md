# Close the 2 sorries in NonparametricStatistics/KernelDensity/{IntegratedVariance,IntegratedBias}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain
`lake build StatLean.NonparametricStatistics.KernelDensity.IntegratedVariance` (then
`.KernelDensity.IntegratedBias`; no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/KernelDensity/IntegratedVariance.lean` and
  `.../IntegratedBias.lean`. Touch nothing else.
- Goal **0 sorries**, 0 errors. Signatures/tags/docstrings frozen. You MAY add `import
  Mathlib.*` and `private` helpers. Lines ≤ 100. Escape hatch: one lifted `private` sorry +
  TODO + report. Foreground `lake build` only.
- After green: `#print axioms` on `kde_integrated_variance_le`, `kde_integrated_sq_bias_le` →
  only `propext, Classical.choice, Quot.sound`.
- Do not weaken statements; if false as stated, STOP and report.

## Available API (proved, black boxes)
- `lintegral_comp_law_densityMeasure (hX : HasLaw X (densityMeasure p) P) (hp : Measurable p)
   (hg : Measurable g) : ∫⁻ ω, g (X ω) ∂P = ∫⁻ z, g z * ENNReal.ofReal (p z)` — LawTransfer.
- `kdeMeanAt_eq_integral_kernel`, `integral_comp_law_densityMeasure`,
  `isProbabilityMeasure_densityMeasure` — LawTransfer.
- `kde_memLp_two`, `kdeVarianceAt_eq_ofReal_variance`, `kdeMseAt_eq_bias_sq_add_variance`,
  `kde_variance_le` — Variance.lean (its useful PRIVATE lemmas `integral_scale_shift'`,
  `integrable_affine`, `integrable_comp_law'`, `kernel_summand_memLp`, `kernel_summand_sq_le`
  must be REPLICATED if needed — read that file first).
- `lintegral_lintegral_sq_rpow_le (μ ν) [SigmaFinite] [SigmaFinite]
   (hg : Measurable (Function.uncurry g)) : (∫⁻ x, (∫⁻ u, g u x ∂μ)^2 ∂ν)^(1/2:ℝ)
   ≤ ∫⁻ u, (∫⁻ x, (g u x)^2 ∂ν)^(1/2:ℝ) ∂μ` — ForMathlib/MinkowskiIntegral (CLOSED, 0-sorry).
- `MemNikolski.lintegral_sq_remainder_le (hβ : 0 < β) (hL : 0 ≤ L) (hf : MemNikolski β L f)
   (t : ℝ) : ∫⁻ x, ofReal ((f (x+t) − ∑ j ∈ range (ℓ+1), iteratedDeriv j f x * t^j/j!)^2)
   ≤ ofReal ((L/ℓ! * |t|^β)^2)` with `ℓ = holderIndex β` — SmoothnessClasses/NikolskiTaylor
  (CLOSED). Also `taylor_integral_remainder_sub` there.
- `IsNikolskiDensity` fields: `nonneg`, `integral_one`, `nikolski : MemNikolski β L p`;
  `MemNikolski.contDiff : ContDiff ℝ (holderIndex β) p` (so `p` continuous, measurable).
- `IsKernelOfOrder K ℓ` fields as usual; `kdeBiasConst β L K = L/ℓ! * ∫ |u|^β * |K u|`.

## Proofs

### A. `kde_integrated_variance_le` (Prop-1.4 shape):
`∫⁻ x, kdeVarianceAt P X K h x ≤ ofReal ((n·h)⁻¹ * ∫ K²)` for ANY measurable density `p`
(only `hp : Measurable p`, `h0 : p ≥ 0` — NO boundedness).
- `kdeVarianceAt P X K h x = ∫⁻ ω, ofReal ((kde X K h ω x − kdeMeanAt P X K h x)^2) ∂P`.
  Without boundedness you canNOT use `kde_memLp_two`; work directly in `∫⁻`:
  * Center per-summand: `kde X K h ω x − kdeMeanAt P X K h x = (n·h)⁻¹ ∑ i, ηᵢ(ω)` needs
    `kdeMeanAt = (n·h)⁻¹ ∑ i E[Kᵢ]` — but E may be junk if not integrable! SAFER ROUTE
    (recommended): prove the bound for the ℝ≥0∞ second moment about ANY constant instead:
    in fact use the general inequality `variance ≤ second moment about any point` at the
    lintegral level via independence… Concretely, the classical proof:
    `∫⁻ x ∫⁻ ω ofReal((kde − E kde)²)`. Two sub-cases:
    1. If `Integrable p`-summands are fine (they are: `E |K((Xᵢ−x)/h)| = ∫ |K((z−x)/h)| p z dz`
       is finite for A.E. `x` by Tonelli: `∫⁻ x ∫⁻ z ofReal|K((z−x)/h)| ofReal(p z)
       = h·(∫⁻|K|)·(∫⁻ p)` — if `K` is integrable... BUT `hK2` only gives `K² ∈ L¹`, NOT
       `K ∈ L¹`! However on the set where things are infinite the variance integrand is
       still dominated as below. RECOMMENDED CLEAN ROUTE:
    2. Use the iid structure at the lintegral level directly:
       `∫⁻ ω ofReal((∑ᵢ ηᵢ)²) = ∑ᵢ ∫⁻ ω ofReal(ηᵢ²)` for centered independent ηᵢ — this
       NEEDS integrability to even define centering. So instead: prove the statement for
       a.e.-x-good points and handle bad x by showing they form a NULL SET on which
       `kdeVarianceAt` could still be ⊤?? — NO: `∫⁻ x` of ⊤ on a null set is 0 ✓ fine.
       Define `G x := ∫ z, (K ((z−x)/h))^2 * p z` (Bochner) and first prove by Tonelli that
       `∫⁻ x, ofReal (G x)`-shape bound holds; a.e. x, `E Kᵢ²(x) < ∞` (Tonelli:
       `∫⁻ x ∫⁻ z ofReal((K((z−x)/h))²) ofReal(p z) = (∫⁻ swap) = h·ofReal(∫K²)·1` using
       `lintegral_lintegral_swap`, the affine lintegral change of variables — prove a
       private `lintegral_scale_shift` mirroring Variance.lean's Bochner one via
       `lintegral_map`/`Measure.map` of affine maps (`Real.map_volume_add_left`,
       `Real.map_volume_mul_left` — check names; or `MeasurePreserving.lintegral_comp`) —
       and `∫⁻ z ofReal(p z) = 1` from `isProbabilityMeasure_densityMeasure` +
       `withDensity_apply` at `univ`).
       For each such good `x`: all summands are in L² ⇒ replicate `kernel_summand_memLp`
       WITHOUT pmax (integrability now comes from `E Kᵢ² < ∞` directly: `memLp_two_iff…`
       needs exactly finite second moment + AESM ✓), and then the Variance.lean chain
       (`kdeVarianceAt_eq_ofReal_variance` + `IndepFun.variance_sum` + identical laws +
       `variance ≤ E X²`) yields `kdeVarianceAt P X K h x ≤ ofReal ((n·h²)⁻¹·h⁻¹·…)` —
       precisely `kdeVarianceAt ≤ ofReal ((n:ℝ)⁻¹ * (n·h... )` reproduce:
       `Var(kde) = (nh)⁻²·n·Var(K₁) ≤ (nh)⁻²·n·E K₁² = (n h²)⁻¹·(E K₁²/…)` — assemble
       `≤ ofReal ((n·h²)⁻¹ · G x)`-form. Wait — with possibly `n = 0`: kde ≡ 0, variance 0 ✓
       handle `n = 0` separately (LHS 0).
  * Integrate the per-x bound: `∫⁻ x, kdeVarianceAt ≤ (n·h²)⁻¹ᵉ · ∫⁻ x, ofReal (G x)`
    (`lintegral_const_mul'`, `ENNReal.ofReal_mul`) and
    `∫⁻ x, ofReal (G x) ≤ ∫⁻ x ∫⁻ z, ofReal((K((z−x)/h))² · p z)` (`ofReal` of a Bochner ≤
    the lintegral — `ofReal_integral_le_lintegral_ofReal` (exists! no integrability needed))
    `= h · ofReal (∫ K²)` (Tonelli swap + affine change + mass 1, as above; final bridge
    `∫⁻ ofReal(K²) = ofReal (∫ K²)` by `ofReal_integral_eq_lintegral_ofReal hK2 (sq_nonneg)`).
    Total: `(n·h²)⁻¹ · h · ∫K² = (n·h)⁻¹ ∫K²` ✓ (`ENNReal.ofReal` algebra; `h > 0`).
  * On the null set of bad `x` the pointwise bound may fail — use
    `lintegral_mono_ae`/`ae_of_all`-with-a.e. version: get the per-x bound as an
    `∀ᵐ x` statement from the Tonelli finiteness (`ae_lt_top` on the finite double
    lintegral: `MeasureTheory.ae_lt_top` (measurable, finite integral ⇒ a.e. finite)).

### B. `kde_integrated_sq_bias_le` (Prop-1.5 shape):
`∫⁻ x, ofReal ((kdeBiasAt P X K h p x)^2) ≤ ofReal (C₂² · h^(2β))` for
`hp : IsNikolskiDensity β L p`, `hK : IsKernelOfOrder K (holderIndex β)`, `hKβ`, `hn : 0 < n`,
`hh : 0 < h`.
- Fix the a.e.-x identity `kdeBiasAt P X K h p x = ∫ u, K u * (p (x + u*h) − T_x u)` where
  `T_x u := ∑ j ∈ range (ℓ+1), iteratedDeriv j p x * (u*h)^j / j!`:
  * a.e.-x integrability of `u ↦ K u * p (x + u*h)`: Tonelli as in (A):
    `∫⁻ x ∫⁻ u ofReal(|K u| · p (x+u·h)) = (∫⁻ |K|)·(∫ p) = ∫⁻|K| · 1` — hmm `∫⁻ |K|` may be
    ⊤ if K ∉ L¹ — but `IsKernelOfOrder` gives `integrable_pow 0`: `u^0·K = K` IS integrable ✓.
    So the double lintegral is finite ⇒ a.e. x the section is finite ⇒ integrable (AESM ✓).
  * For good x: `kdeMeanAt_eq_integral_kernel` gives `kdeMeanAt = ∫ K u * p (x+u·h)`;
    moment cancellation exactly as in Bias.lean's `abs_integral_kernel_taylor_le`
    (READ `KernelDensity/Bias.lean` — if the C1 work item has landed there, reuse its
    public lemmas; if that file still has sorries, do NOT rely on them — replicate the
    small cancellation steps privately): `∫ K·T_x = p x` needs integrability of `u^j·K` ✓
    and the values `iteratedDeriv j p x` finite ✓; but ALSO integrability of `K·(p∘affine)`
    which holds only a.e. x — fine (a.e. identity suffices; on the bad null set the
    integrand `ofReal(bias²)` is whatever, null sets don't affect `∫⁻`... careful: the bias
    at bad x is `junk-0 − p x` — still a REAL number; the identity fails there but we only
    prove the INEQUALITY a.e. and `lintegral_mono_ae` handles it — actually we need the
    UPPER bound a.e., same thing ✓).
- Now the L² step: `∫⁻ x, ofReal ((∫ u, K u * R x u)²)` with `R x u := p (x+u·h) − T_x u`.
  `(∫ u, K u * R x u)² ≤ (∫ u, |K u| * |R x u|)²` (`norm_integral_le_integral_norm` + square
  monotone on nonnegs). Then `ofReal ((∫ |K|·|R|)²) ≤ (∫⁻ u, ofReal (|K u| · |R x u|))²`
  (`ofReal_integral_le_lintegral_ofReal` + `ENNReal.pow_le_pow_left` — or square the a.e.
  bound). Apply the SQUARED consequence of Minkowski (derive privately from
  `lintegral_lintegral_sq_rpow_le` by `ENNReal.rpow_le_rpow … 2`-style: from
  `A^(1/2) ≤ B` conclude `A ≤ B^2` via `ENNReal.rpow_natCast`, `ENNReal.rpow_mul`,
  monotonicity — spell out: `A = (A^(1/2))^2 ≤ B^2` using `ENNReal.rpow_two`-free pow
  algebra and `(x^(1/2))^2 = x` (`← ENNReal.rpow_natCast`, `← ENNReal.rpow_mul`,
  `(1/2)*2 = 1`)) with `μ := volume` in `u`, `ν := volume` in `x`,
  `g u x := ofReal (|K u| * |R x u|)` (joint measurability: `p` continuous, `T` finite sum of
  continuous-in-x times powers — all continuous in `(u,x)` except `K` measurable in `u`:
  product of `measurable_fst`-composed `|K|` and continuous-|R| ✓ `Measurable.mul`).
  Inner slice: `∫⁻ x, ofReal ((|K u| · |R x u|)²) = ofReal (K u²)… ` factor
  `ofReal (|K u|²)` out (`lintegral_const_mul'`, `ENNReal.ofReal_mul`, `mul_pow`, `sq_abs`)
  and bound `∫⁻ x, ofReal ((R x u)²) ≤ ofReal ((L/ℓ! · |u·h|^β)²)` by
  `MemNikolski.lintegral_sq_remainder_le hβ hL hp.nikolski (u*h)` — NOTE the lemma's shift
  is `t := u*h` and its sum matches `T_x u` ✓ (same shape: `iteratedDeriv j p x * (u*h)^j/j!`).
  Then `(∫⁻ x …)^(1/2) ≤ ofReal (|K u| · (L/ℓ!) · |u·h|^β)` (`ofReal_sq_rpow_half`-style —
  replicate NikolskiTaylor's private helper: `(ofReal (a²))^(1/2) = ofReal a` for `a ≥ 0`).
  Outer: `∫⁻ u, ofReal (|K u| (L/ℓ!) |u|^β h^β) = ofReal ((L/ℓ!) h^β ∫ |u|^β |K u|)
  = ofReal (C₂ h^β)` (`|u·h|^β = |u|^β·h^β` `Real.mul_rpow`/`abs_mul`, `abs_of_pos hh`;
  bridge by `ofReal_integral_eq_lintegral_ofReal hKβ` + const pulls). Square: `(C₂ h^β)²
  = C₂²·h^(2β)` (`Real.rpow_natCast`, `← Real.rpow_mul`, `two_mul` — h > 0).

Report final `lake build` status for both modules + `#print axioms` for the two named theorems
(note any lifted `private` sorry).
