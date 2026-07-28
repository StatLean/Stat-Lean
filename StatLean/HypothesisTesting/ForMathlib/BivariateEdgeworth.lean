import StatLean.HypothesisTesting.ForMathlib.BerryEsseen

/-!
# The damped Edgeworth expansion in an inner product space

`ForMathlib/BerryEsseen.lean` proves the one-dimensional damped one-term Edgeworth expansion
`norm_charFun_pow_sub_edgeworth_le`: for a centred law `μ` on the line with second moment `v`,
third moment `m₃` and a finite fourth moment, and for `s` in the window `v s² ≤ 2`,
`ρ|s| ≤ 3v/2`,

`‖φ_μ(s)ⁿ − e^{−n v s²/2}(1 − n i m₃ s³/6)‖ ≤ e^{−(n−2) v s²/4}(…)`.

The studentized Edgeworth expansion of `Bootstrap/Edgeworth.lean` needs the same estimate for a
law on `ℝ²` — the joint law of `(X − μ, (X − μ)² − σ²)`, whose sample mean carries both the
numerator and the denominator of the studentized root. This file supplies it, and the point of
the file is that **no genuinely two-dimensional argument is required**: the characteristic
function of a measure on an inner product space, evaluated along a ray `s • t`, is the
characteristic function of the *one-dimensional projection* `⟪·, t⟫` evaluated at `s`
(`charFun_smul_eq_charFun_map_inner`). Every hypothesis and every conclusion of the
one-dimensional theorem therefore transfers verbatim, with the moments of `μ` replaced by the
moments of the projected law.

## Main definitions

* `vecRootLaw F Z n` — the law of `n^{-1/2} ∑_{i<n} Z(yᵢ)` under `n` independent draws from `F`,
  a measure on the inner product space `E`. For `E = ℝ` and `Z = id − E_F X` this is
  `Bootstrap/Edgeworth.lean`'s `meanRootLaw`.

## Main statements

* `charFun_smul_eq_charFun_map_inner` — the projection identity
  `φ_μ(s • t) = φ_{μ ∘ ⟪·,t⟫⁻¹}(s)`.
* `norm_charFun_smul_le_exp_neg_sq` — the Gaussian majorant on a window, in `E`.
* `norm_charFun_smul_pow_sub_edgeworth_le` — the damped one-term Edgeworth expansion in `E`.
* `charFun_vecRootLaw` — `φ_{vecRootLaw F Z n}(t) = φ_{F ∘ Z⁻¹}(n^{-1/2} • t)ⁿ`, the
  factorisation that lets the previous item be applied to a sample mean.
* `mixCharFun` — the **mixed** characteristic function `∫ ⟪w,b⟫ e^{i⟪w,t⟫} ∂μ`, together with
  its exact factorisation on a vector root (`mixCharFun_vecRootLaw`), the first-order Taylor
  bound on a single factor (`norm_mixCharFun_sub_mul_I_le`) and the resulting one-term expansion
  `‖mix_{ρ_n}(b,a) − iκ φ(n^{-1/2}a)^{n−1}‖ ≤ 3M/(2√n)`
  (`norm_mixCharFun_vecRootLaw_sub_le`). Up to a factor `i` this is the directional derivative
  of `charFun`; it is estimated directly because the studentized expansion needs an *inequality*
  for it and inequalities cannot be differentiated.
* `multiCharFun` — the **multilinear** extension `∫ (∏_{l<k} ⟪w, b l⟫) e^{i⟪w,t⟫} ∂μ`, with its
  exact factorisation on a vector root (`multiCharFun_vecRootLaw`):
  `multi_{ρ_n}(b,a) = n^{-k/2} ∑_{σ : Fin k → Fin n} ∏_{i<n} slot_{σ⁻¹(i)}(n^{-1/2} • a)`,
  a sum over the `nᵏ` assignments of weight slots to coordinates. `mixCharFun` is the case
  `k = 1` (where all `n` summands coincide and `n · n^{-1/2} = √n`) and `charFun` is `k = 0`.
  The third-order delta-method surrogate of the studentized route is a degree-four polynomial
  in the coordinates of the root, so its characteristic function is a finite combination of
  `multiCharFun`s with `k ≤ 4`, and is *not* reachable from the one-slot theory.

## Proof formalization notes

* The projection identity is `charFun_apply` on both sides plus `real_inner_smul_right`; it is
  the whole content of "the multivariate expansion is the univariate one". Note that it is an
  identity between the value at `s • t` and a *one-dimensional* characteristic function, not a
  statement about `charFun μ` as a function on `E`: what is expanded is the restriction of
  `φ_μ` to each ray through the origin, uniformly in the direction.
* Consequently the moments appearing in the expansion are the **directional** moments
  `∫ ⟪x, t⟫^k ∂μ`. In the classical formulation these are the contractions of the cumulant
  tensors with `t`: `∫⟪x,t⟫² = ⟪Σ t, t⟫` is the covariance form and `∫⟪x,t⟫³` is the third
  cumulant tensor evaluated at `(t,t,t)`. Nothing is lost by carrying them as scalars.
* The window conditions `v s² ≤ 2`, `ρ|s| ≤ 3v/2` are direction-dependent through
  `v = v(t) = ⟪Σt,t⟫`. Turning them into a window *uniform in the direction* is where
  nondegeneracy of `Σ` enters: `v(t) ≥ λ_min ‖t‖²` is what converts a bound on `‖t‖` into the
  window conditions for every direction. That step is a hypothesis of the consumer, not of this
  file.
* `charFun_vecRootLaw` is proved exactly as `charFun_meanRootLaw` is in
  `Bootstrap/Edgeworth.lean`: the root map is a scalar multiple of a sum of one-variable
  functions of the coordinates, `Complex.exp_sum` turns the exponential of the sum into a
  product, and `MeasureTheory.integral_fintype_prod_eq_pow` is Fubini for such a product on
  `Measure.pi`. No transfer through the canonical i.i.d. construction is needed.

**Reference.** P. Hall, *The Bootstrap and Edgeworth Expansion*, Springer, 1992, Chapter 2
(the "smooth function model": the statistic is a smooth function of a vector sample mean, and
the expansion is obtained from the multivariate expansion of that mean).
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace StatLean.HypothesisTesting

/-! ## The projection identity

The characteristic function of a measure on an inner product space, restricted to the ray
`s ↦ s • t`, is the characteristic function of the pushforward under `x ↦ ⟪x, t⟫`. -/

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

/-- The linear form `x ↦ ⟪x, t⟫` is measurable. -/
lemma measurable_inner_right (t : E) : Measurable fun x : E => ⟪x, t⟫ :=
  (continuous_id.inner continuous_const).measurable

/-- The **projected law** in the direction `t`: the pushforward of `μ` under `x ↦ ⟪x, t⟫`. -/
noncomputable def projLaw (μ : Measure E) (t : E) : Measure ℝ :=
  μ.map fun x : E => ⟪x, t⟫

instance isProbabilityMeasure_projLaw (μ : Measure E) [IsProbabilityMeasure μ] (t : E) :
    IsProbabilityMeasure (projLaw μ t) := by
  rw [projLaw]
  exact Measure.isProbabilityMeasure_map (measurable_inner_right t).aemeasurable

/-- Integrals against the projected law are directional integrals against `μ`. -/
lemma integral_projLaw (μ : Measure E) (t : E) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (projLaw μ t)) :
    ∫ y, f y ∂(projLaw μ t) = ∫ x, f ⟪x, t⟫ ∂μ :=
  integral_map (measurable_inner_right t).aemeasurable hf

/-- Integrability against the projected law is directional integrability against `μ`. -/
lemma integrable_projLaw_iff (μ : Measure E) (t : E) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (projLaw μ t)) :
    Integrable f (projLaw μ t) ↔ Integrable (fun x : E => f ⟪x, t⟫) μ :=
  integrable_map_measure hf (measurable_inner_right t).aemeasurable

/-- **The projection identity.** `φ_μ(s • t) = φ_{projLaw μ t}(s)`: along every ray through the
origin, the characteristic function of a measure on an inner product space is the
characteristic function of a measure on the line. -/
theorem charFun_smul_eq_charFun_map_inner (μ : Measure E) (t : E) (s : ℝ) :
    charFun μ (s • t) = charFun (projLaw μ t) s := by
  rw [charFun_apply_real, projLaw,
    integral_map (measurable_inner_right t).aemeasurable (by fun_prop), charFun_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [real_inner_smul_right]
  push_cast
  ring_nf

end Projection

/-! ## The expansion, transferred

Both estimates of `ForMathlib/BerryEsseen.lean` that the Edgeworth remainder consumes — the
Gaussian majorant on a window and the damped one-term expansion of the `n`-th power — hold in
an inner product space along every ray, with the moments replaced by the directional moments
`∫ ⟪x, t⟫^k ∂μ`. Both are corollaries of the projection identity. -/

section Expansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

/-- **Gaussian majorant for a characteristic function on a window, in an inner product space.**
On the window `v s² ≤ 2`, `ρ|s| ≤ 3v/2` built from the directional moments
`v = ∫⟪x,t⟫²`, `ρ = ∫|⟪x,t⟫|³` of a directionally centred law,
`‖φ_μ(s • t)‖ ≤ exp(−v s²/4)`.

This is the two-dimensional analogue of `norm_charFun_le_exp_neg_sq` that
`Bootstrap/Edgeworth.lean` records as missing; it needs no two-dimensional argument. -/
theorem norm_charFun_smul_le_exp_neg_sq (μ : Measure E) [IsProbabilityMeasure μ]
    {t : E} {v : ℝ}
    (hint1 : Integrable (fun x : E => ⟪x, t⟫) μ)
    (hint2 : Integrable (fun x : E => ⟪x, t⟫ ^ 2) μ)
    (hint3 : Integrable (fun x : E => |⟪x, t⟫| ^ 3) μ)
    (hmean : ∫ x, ⟪x, t⟫ ∂μ = 0) (hvar : ∫ x, ⟪x, t⟫ ^ 2 ∂μ = v)
    {s : ℝ} (hs2 : v * s ^ 2 ≤ 2)
    (hs3 : (∫ x, |⟪x, t⟫| ^ 3 ∂μ) * |s| ≤ 3 * v / 2) :
    ‖charFun μ (s • t)‖ ≤ Real.exp (-(v * s ^ 2 / 4)) := by
  have e1 : ∫ y : ℝ, y ∂(projLaw μ t) = ∫ x, ⟪x, t⟫ ∂μ := integral_projLaw μ t (by fun_prop)
  have e2 : ∫ y : ℝ, y ^ 2 ∂(projLaw μ t) = ∫ x, ⟪x, t⟫ ^ 2 ∂μ :=
    integral_projLaw μ t (by fun_prop)
  have e3 : ∫ y : ℝ, |y| ^ 3 ∂(projLaw μ t) = ∫ x, |⟪x, t⟫| ^ 3 ∂μ :=
    integral_projLaw μ t (by fun_prop)
  rw [charFun_smul_eq_charFun_map_inner]
  exact norm_charFun_le_exp_neg_sq _ ((integrable_projLaw_iff μ t (by fun_prop)).2 hint1)
    ((integrable_projLaw_iff μ t (by fun_prop)).2 hint2)
    ((integrable_projLaw_iff μ t (by fun_prop)).2 hint3) (by rw [e1, hmean]) (by rw [e2, hvar])
    hs2 (by rw [e3]; exact hs3)

/-- **Damped one-term Edgeworth expansion in an inner product space.**

For a law `μ` on `E` which is centred in the direction `t`, with directional second moment `v`,
directional third moment `m₃` and a finite directional fourth moment, and for `s` in the window
`v s² ≤ 2`, `ρ|s| ≤ 3v/2`,

`‖φ_μ(s • t)ⁿ − e^{−n v s²/2}(1 − n i m₃ s³/6)‖ ≤ e^{−(n−2) v s²/4}(…)`,

with the same right-hand side as `norm_charFun_pow_sub_edgeworth_le`, written with `n = m + 2`.

**This is step 1 of the studentized route of `Bootstrap/Edgeworth.lean`.** For the pair
`Z = (X − μ, (X − μ)² − σ²)` it is the bivariate expansion recorded there as missing, and the
directional moments are the contractions of the cumulant tensors of `Z` with `t`. -/
theorem norm_charFun_smul_pow_sub_edgeworth_le (μ : Measure E) [IsProbabilityMeasure μ]
    {t : E} {v m₃ : ℝ}
    (hint1 : Integrable (fun x : E => ⟪x, t⟫) μ)
    (hint2 : Integrable (fun x : E => ⟪x, t⟫ ^ 2) μ)
    (hint3 : Integrable (fun x : E => |⟪x, t⟫| ^ 3) μ)
    (hint4 : Integrable (fun x : E => ⟪x, t⟫ ^ 4) μ)
    (hmean : ∫ x, ⟪x, t⟫ ∂μ = 0) (hvar : ∫ x, ⟪x, t⟫ ^ 2 ∂μ = v)
    (hthird : ∫ x, ⟪x, t⟫ ^ 3 ∂μ = m₃)
    {s : ℝ} (hs2 : v * s ^ 2 ≤ 2)
    (hs3 : (∫ x, |⟪x, t⟫| ^ 3 ∂μ) * |s| ≤ 3 * v / 2) (m : ℕ) :
    ‖charFun μ (s • t) ^ (m + 2)
        - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ) ^ (m + 2)
            * (1 - ((m : ℂ) + 2) * Complex.I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6)‖
      ≤ Real.exp (-(v * s ^ 2 / 4)) ^ m *
          (((m : ℝ) + 2) * ((m : ℝ) + 1) / 2
              * ((∫ x, |⟪x, t⟫| ^ 3 ∂μ) * |s| ^ 3 / 6 + (v * s ^ 2 / 2) ^ 2 / 2) ^ 2
            + ((m : ℝ) + 2) * ((v * s ^ 2 / 2) * (|m₃| * |s| ^ 3 / 6)
              + ((∫ x, ⟪x, t⟫ ^ 4 ∂μ) * |s| ^ 4 / 24 + (v * s ^ 2 / 2) ^ 2 / 2))) := by
  have e1 : ∫ y : ℝ, y ∂(projLaw μ t) = ∫ x, ⟪x, t⟫ ∂μ := integral_projLaw μ t (by fun_prop)
  have e2 : ∫ y : ℝ, y ^ 2 ∂(projLaw μ t) = ∫ x, ⟪x, t⟫ ^ 2 ∂μ :=
    integral_projLaw μ t (by fun_prop)
  have e3 : ∫ y : ℝ, |y| ^ 3 ∂(projLaw μ t) = ∫ x, |⟪x, t⟫| ^ 3 ∂μ :=
    integral_projLaw μ t (by fun_prop)
  have e3' : ∫ y : ℝ, y ^ 3 ∂(projLaw μ t) = ∫ x, ⟪x, t⟫ ^ 3 ∂μ :=
    integral_projLaw μ t (by fun_prop)
  have e4 : ∫ y : ℝ, y ^ 4 ∂(projLaw μ t) = ∫ x, ⟪x, t⟫ ^ 4 ∂μ :=
    integral_projLaw μ t (by fun_prop)
  rw [charFun_smul_eq_charFun_map_inner, ← e3, ← e4]
  exact norm_charFun_pow_sub_edgeworth_le _ ((integrable_projLaw_iff μ t (by fun_prop)).2 hint1)
    ((integrable_projLaw_iff μ t (by fun_prop)).2 hint2)
    ((integrable_projLaw_iff μ t (by fun_prop)).2 hint3)
    ((integrable_projLaw_iff μ t (by fun_prop)).2 hint4) (by rw [e1, hmean]) (by rw [e2, hvar])
    (by rw [e3', hthird]) hs2 (by rw [e3]; exact hs3) m

end Expansion

/-! ## The law of a vector root

The expansion above estimates an `n`-th power of a characteristic function; what a statistic
supplies is the law of a normalised sum. `vecRootLaw` is that law, and `charFun_vecRootLaw` is
the factorisation, proved directly on `Measure.pi` exactly as `charFun_meanRootLaw` is. -/

section VecRoot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The root map `y ↦ n^{-1/2} ∑ᵢ Z(yᵢ)` is measurable. -/
lemma measurable_vecRoot {Z : ℝ → E} (hZ : Measurable Z) (n : ℕ) :
    Measurable fun y : Fin n → ℝ => (Real.sqrt n)⁻¹ • ∑ i, Z (y i) :=
  (continuous_const_smul ((Real.sqrt n)⁻¹ : ℝ)).measurable.comp
    (Finset.measurable_sum _ fun i _ => hZ.comp (measurable_pi_apply i))

/-- The **law of the vector root** `n^{-1/2} ∑_{i<n} Z(yᵢ)` under `n` independent draws from
`F`. For `E = ℝ` and `Z = (· − E_F X)` this is `Bootstrap/Edgeworth.lean`'s `meanRootLaw`. -/
noncomputable def vecRootLaw (F : Measure ℝ) (Z : ℝ → E) (n : ℕ) : Measure E :=
  (Measure.pi fun _ : Fin n => F).map fun y : Fin n → ℝ => (Real.sqrt n)⁻¹ • ∑ i, Z (y i)

instance isProbabilityMeasure_vecRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) (n : ℕ) : IsProbabilityMeasure (vecRootLaw F Z n) := by
  rw [vecRootLaw]
  exact Measure.isProbabilityMeasure_map (measurable_vecRoot hZ n).aemeasurable

/-- **The characteristic function of a vector root, as an `n`-th power.**
`φ_{vecRootLaw F Z n}(t) = φ_{F ∘ Z⁻¹}(n^{-1/2} • t)ⁿ`.

Together with `norm_charFun_smul_pow_sub_edgeworth_le` — whose left-hand side is an `n`-th
power of `φ` *along a ray* — this is the whole characteristic-function half of a multivariate
one-term Edgeworth expansion. -/
theorem charFun_vecRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) (n : ℕ) (t : E) :
    charFun (vecRootLaw F Z n) t = charFun (F.map Z) ((Real.sqrt n)⁻¹ • t) ^ n := by
  set c : E := (Real.sqrt n)⁻¹ • t with hc
  have hmeasg : Measurable fun y : Fin n → ℝ => (Real.sqrt n)⁻¹ • ∑ i, Z (y i) :=
    measurable_vecRoot hZ n
  have hstep1 : charFun (vecRootLaw F Z n) t
      = ∫ y : Fin n → ℝ, ∏ i : Fin n, Complex.exp ((⟪Z (y i), c⟫ : ℝ) * Complex.I)
        ∂(Measure.pi fun _ : Fin n => F) := by
    rw [charFun_apply, vecRootLaw, integral_map hmeasg.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have harg : (⟪(Real.sqrt n)⁻¹ • ∑ i, Z (y i), t⟫ : ℝ) = ∑ i : Fin n, (⟪Z (y i), c⟫ : ℝ) :=
      calc (⟪(Real.sqrt n)⁻¹ • ∑ i, Z (y i), t⟫ : ℝ)
          = (Real.sqrt n)⁻¹ * ⟪∑ i, Z (y i), t⟫ := real_inner_smul_left _ _ _
        _ = (Real.sqrt n)⁻¹ * ∑ i : Fin n, (⟪Z (y i), t⟫ : ℝ) := by rw [sum_inner]
        _ = ∑ i : Fin n, (Real.sqrt n)⁻¹ * (⟪Z (y i), t⟫ : ℝ) := Finset.mul_sum _ _ _
        _ = ∑ i : Fin n, (⟪Z (y i), c⟫ : ℝ) := by
            simp only [hc, real_inner_smul_right]
    simp only [harg]
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  have hstep2 : (∫ y : Fin n → ℝ, ∏ i : Fin n, Complex.exp ((⟪Z (y i), c⟫ : ℝ) * Complex.I)
        ∂(Measure.pi fun _ : Fin n => F))
      = (∫ x : ℝ, Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I) ∂F) ^ n := by
    have h := MeasureTheory.integral_fintype_prod_eq_pow (ι := Fin n) (μ := F)
      (fun x : ℝ => Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I))
    simpa using h
  have hstep3 : (∫ x : ℝ, Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I) ∂F)
      = charFun (F.map Z) c := by
    rw [charFun_apply, integral_map hZ.aemeasurable (by fun_prop)]
  rw [hstep1, hstep2, hstep3]

/-- **The one-term Edgeworth expansion of a vector root, at the level of characteristic
functions.** For a directionally centred `Z` with directional second moment `v`, third moment
`m₃` and finite fourth moment, and for `t` in the direction-dependent window,

`‖φ_{vecRootLaw F Z n}(t) − e^{−v/2}(1 − i m₃ n^{-1/2}/6)‖ ≤ (the damped remainder)`,

written with `n = m + 2`. The Gaussian factor and the `n^{-1/2}` correction are exactly the
Fourier transform of the multivariate Edgeworth signed density in the direction `t`.

**This is the bivariate expansion that `Bootstrap/Edgeworth.lean` records as the sole missing
ingredient of the studentized expansion**, specialised to `E = ℝ²` and
`Z = studentPair F = (X − μ, (X − μ)² − σ²)`. It is the composition of `charFun_vecRootLaw`
with `norm_charFun_smul_pow_sub_edgeworth_le`; the scaling `n s² = 1` at `s = n^{-1/2}` turns
`e^{−n v s²/2}` into `e^{−v/2}` and `n s³` into `s`. -/
theorem norm_charFun_vecRootLaw_sub_edgeworth_le (F : Measure ℝ) [IsProbabilityMeasure F]
    {Z : ℝ → E} (hZ : Measurable Z) {t : E} {v m₃ : ℝ} (m : ℕ)
    (hint1 : Integrable (fun x : E => ⟪x, t⟫) (F.map Z))
    (hint2 : Integrable (fun x : E => ⟪x, t⟫ ^ 2) (F.map Z))
    (hint3 : Integrable (fun x : E => |⟪x, t⟫| ^ 3) (F.map Z))
    (hint4 : Integrable (fun x : E => ⟪x, t⟫ ^ 4) (F.map Z))
    (hmean : ∫ x, ⟪x, t⟫ ∂(F.map Z) = 0) (hvar : ∫ x, ⟪x, t⟫ ^ 2 ∂(F.map Z) = v)
    (hthird : ∫ x, ⟪x, t⟫ ^ 3 ∂(F.map Z) = m₃)
    (hs2 : v * (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ ^ 2 ≤ 2)
    (hs3 : (∫ x, |⟪x, t⟫| ^ 3 ∂(F.map Z)) * |(Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹|
      ≤ 3 * v / 2) :
    ‖charFun (vecRootLaw F Z (m + 2)) t
        - ((Real.exp (-(v / 2)) : ℝ) : ℂ)
            * (1 - Complex.I * (m₃ : ℂ) * (((Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) / 6)‖
      ≤ Real.exp (-(v * (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ ^ 2 / 4)) ^ m *
          (((m : ℝ) + 2) * ((m : ℝ) + 1) / 2
              * ((∫ x, |⟪x, t⟫| ^ 3 ∂(F.map Z))
                  * |(Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹| ^ 3 / 6
                + (v * (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ ^ 2 / 2) ^ 2 / 2) ^ 2
            + ((m : ℝ) + 2)
              * ((v * (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ ^ 2 / 2)
                  * (|m₃| * |(Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹| ^ 3 / 6)
                + ((∫ x, ⟪x, t⟫ ^ 4 ∂(F.map Z))
                    * |(Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹| ^ 4 / 24
                  + (v * (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ ^ 2 / 2) ^ 2 / 2))) := by
  haveI : IsProbabilityMeasure (F.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  set s : ℝ := (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ with hs
  have hne : ((m : ℝ) + 2) ≠ 0 := by positivity
  have hN : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by push_cast; positivity
  have hsq : s ^ 2 = (((m + 2 : ℕ) : ℝ))⁻¹ := by
    rw [hs, inv_pow, Real.sq_sqrt hN.le]
  have h2 : ((m : ℝ) + 2) * s ^ 2 = 1 := by
    rw [hsq]; push_cast; field_simp
  have hgauss : ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ) ^ (m + 2)
      = ((Real.exp (-(v / 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul, Complex.ofReal_inj]
    congr 1
    push_cast
    linear_combination (-(v / 2)) * h2
  have hreal : ((m : ℝ) + 2) * s ^ 3 = s := by
    calc ((m : ℝ) + 2) * s ^ 3 = (((m : ℝ) + 2) * s ^ 2) * s := by ring
      _ = s := by rw [h2, one_mul]
  have hcorr : ((m : ℂ) + 2) * Complex.I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6
      = Complex.I * (m₃ : ℂ) * (s : ℂ) / 6 := by
    have hc : ((m : ℂ) + 2) * (s : ℂ) ^ 3 = (s : ℂ) := by exact_mod_cast hreal
    calc ((m : ℂ) + 2) * Complex.I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6
        = Complex.I * (m₃ : ℂ) * (((m : ℂ) + 2) * (s : ℂ) ^ 3) / 6 := by ring
      _ = Complex.I * (m₃ : ℂ) * (s : ℂ) / 6 := by rw [hc]
  rw [charFun_vecRootLaw F hZ, ← hs, ← hgauss, ← hcorr]
  exact norm_charFun_smul_pow_sub_edgeworth_le (F.map Z) hint1 hint2 hint3 hint4 hmean hvar
    hthird hs2 hs3 m

end VecRoot

/-! ## The mixed characteristic function

The studentized route of `Bootstrap/Edgeworth.lean` needs, besides the expansion of
`ψ_n(θ, s) = φ_{ρ_n}(θ e₁/σ + s e₂/σ²)` supplied by
`norm_charFun_vecRootLaw_sub_edgeworth_le`, an expansion of the *`s`-derivative* of `ψ_n` at
`s = 0`. Differentiating an inequality is not legitimate, so that estimate cannot be read off
from the expansion; it is proved here from scratch, for the quantity the derivative is:

`mixCharFun μ b t = ∫ ⟪w, b⟫ e^{i⟪w,t⟫} ∂μ`,

the character in the direction `t` weighted by the coordinate in the direction `b`.

The point of this section is that the mixed quantity is *easier* than the expansion, not
harder. Its value on a vector root factorises **exactly** — one distinguished coordinate
carrying the weight `⟪·, b⟫`, the remaining `n − 1` carrying only the character
(`mixCharFun_vecRootLaw`) — and a first-order Taylor bound on the single distinguished factor
(`norm_mixCharFun_sub_mul_I_le`) then gives the whole estimate, with the covariance
`κ = ∫ ⟪x, b⟫⟪x, a⟫` as the limit and an `O(n^{-1/2})` remainder
(`norm_mixCharFun_vecRootLaw_sub_le`). No smoothing, no window and no Cramér condition enter:
the factorisation is an identity and the Taylor bound is pointwise. -/

section Mixed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The **mixed characteristic function** `∫ ⟪w, b⟫ e^{i⟪w,t⟫} ∂μ`.

Up to the factor `i` this is the derivative of `charFun μ` at `t` in the direction `b`
(Mathlib's `iteratedFDeriv_charFun` at `n = 1` computes exactly this integral), but it is
defined and estimated directly: what the studentized expansion needs is an *inequality* for it,
uniform in `t`, and inequalities cannot be differentiated. -/
noncomputable def mixCharFun (μ : Measure E) (b t : E) : ℂ :=
  ∫ w, ((⟪w, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I) ∂μ

/-- The mixed characteristic function of a pushforward is a directional integral. -/
lemma mixCharFun_map (F : Measure ℝ) {Z : ℝ → E} (hZ : Measurable Z) (b t : E) :
    mixCharFun (F.map Z) b t
      = ∫ x, ((⟪Z x, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪Z x, t⟫ : ℝ) * Complex.I) ∂F := by
  rw [mixCharFun, integral_map hZ.aemeasurable (by fun_prop)]

/-- **The mixed characteristic function of a vector root factorises exactly.**

`∫ ⟪w, b⟫ e^{i⟪w,a⟫} ∂(vecRootLaw F Z n) = √n · (∫ ⟪Z x, b⟫ e^{i⟪Z x, c⟫} ∂F) · φ(c)^{n−1}`,
with `c = n^{-1/2} • a`.

This is the analogue of `charFun_vecRootLaw` for the weighted character, and it is the reason
(M1)(b) is tractable: the weight `⟪·, b⟫` of the root is `n^{-1/2} ∑ᵢ ⟪Z(yᵢ), b⟫`, a *sum*, so
the integrand splits into `n` products over the coordinates, each with exactly one
distinguished factor. Fubini on `Measure.pi` (`integral_fintype_prod_eq_prod`) evaluates each,
and the `n` summands are equal; the surviving `n · n^{-1/2} = √n` is the whole reason the
mixed quantity is of size `n^{-1/2}` larger than a plain characteristic function before the
centring of `⟪·, b⟫` is used. -/
theorem mixCharFun_vecRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) {b : E} (hb : Integrable (fun x : ℝ => (⟪Z x, b⟫ : ℝ)) F)
    (m : ℕ) (a : E) :
    mixCharFun (vecRootLaw F Z (m + 1)) b a
      = (Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ)
          * mixCharFun (F.map Z) b ((Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • a)
          * charFun (F.map Z) ((Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • a) ^ m := by
  classical
  have hNpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hsq : (0 : ℝ) < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hNpos
  set r : ℝ := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ with hrdef
  set c : E := r • a with hcdef
  have hZb : Measurable fun x : ℝ => (⟪Z x, b⟫ : ℝ) := (measurable_inner_right b).comp hZ
  have hZc : Measurable fun x : ℝ => (⟪Z x, c⟫ : ℝ) := (measurable_inner_right c).comp hZ
  set g : ℝ → ℂ := fun x => Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I) with hgdef
  set f : ℝ → ℂ := fun x => ((⟪Z x, b⟫ : ℝ) : ℂ) * g x with hfdef
  have hgnorm : ∀ x, ‖g x‖ = 1 := by
    intro x
    rw [hgdef]
    simp [Complex.norm_exp]
  have hgm : Measurable g := by rw [hgdef]; fun_prop
  have hfm : Measurable f := by rw [hfdef]; fun_prop
  -- the `i`-th summand of the weight, written as a product over the coordinates
  set h : Fin (m + 1) → Fin (m + 1) → ℝ → ℂ :=
    fun i j x => if j = i then f x else g x with hhdef
  have hprod : ∀ (i : Fin (m + 1)) (y : Fin (m + 1) → ℝ),
      ∏ j, h i j (y j) = ((⟪Z (y i), b⟫ : ℝ) : ℂ) * ∏ j, g (y j) := by
    intro i y
    have hfac : ∀ j : Fin (m + 1),
        h i j (y j) = (if j = i then ((⟪Z (y j), b⟫ : ℝ) : ℂ) else 1) * g (y j) := by
      intro j
      by_cases hji : j = i
      · simp [hhdef, hfdef, hji]
      · simp [hhdef, hji]
    simp_rw [hfac]
    rw [Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ i (fun j => ((⟪Z (y j), b⟫ : ℝ) : ℂ))]
    simp
  -- each summand is integrable on the product measure: its modulus is `|⟪Z(yᵢ), b⟫|`
  have hint : ∀ i : Fin (m + 1),
      Integrable (fun y : Fin (m + 1) → ℝ => ∏ j, h i j (y j))
        (Measure.pi fun _ : Fin (m + 1) => F) := by
    intro i
    have hdom : Integrable (fun y : Fin (m + 1) → ℝ => |(⟪Z (y i), b⟫ : ℝ)|)
        (Measure.pi fun _ : Fin (m + 1) => F) := by
      have := (measurePreserving_eval (μ := fun _ : Fin (m + 1) => F)
        i).integrable_comp_of_integrable hb.abs
      simpa [Function.comp] using this
    have hmeas : ∀ j : Fin (m + 1),
        Measurable fun y : Fin (m + 1) → ℝ => h i j (y j) := by
      intro j
      rcases eq_or_ne j i with rfl | hji
      · simpa [hhdef] using hfm.comp (measurable_pi_apply j)
      · simpa [hhdef, hji] using hgm.comp (measurable_pi_apply j)
    refine Integrable.mono' hdom
      ((Finset.measurable_prod _ fun j _ => hmeas j).aestronglyMeasurable) ?_
    filter_upwards with y
    rw [hprod i y, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hone : ‖∏ j, g (y j)‖ = 1 := by
      rw [norm_prod]
      simp [hgnorm]
    rw [hone, mul_one]
  -- step 1: rewrite the mixed integral over the root law as an integral over the product
  have hstep1 : mixCharFun (vecRootLaw F Z (m + 1)) b a
      = ∫ y : Fin (m + 1) → ℝ, ((r : ℂ) * ∑ i, ∏ j, h i j (y j))
        ∂(Measure.pi fun _ : Fin (m + 1) => F) := by
    rw [mixCharFun, vecRootLaw,
      integral_map (measurable_vecRoot hZ (m + 1)).aemeasurable (by fun_prop)]
    simp only [← hrdef]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hbi : (⟪r • ∑ i, Z (y i), b⟫ : ℝ) = r * ∑ i : Fin (m + 1), (⟪Z (y i), b⟫ : ℝ) := by
      rw [real_inner_smul_left, sum_inner]
    have hai : (⟪r • ∑ i, Z (y i), a⟫ : ℝ) = ∑ i : Fin (m + 1), (⟪Z (y i), c⟫ : ℝ) := by
      calc (⟪r • ∑ i, Z (y i), a⟫ : ℝ)
          = r * ⟪∑ i, Z (y i), a⟫ := real_inner_smul_left _ _ _
        _ = r * ∑ i : Fin (m + 1), (⟪Z (y i), a⟫ : ℝ) := by rw [sum_inner]
        _ = ∑ i : Fin (m + 1), r * (⟪Z (y i), a⟫ : ℝ) := Finset.mul_sum _ _ _
        _ = ∑ i : Fin (m + 1), (⟪Z (y i), c⟫ : ℝ) := by
            simp only [hcdef, real_inner_smul_right]
    simp only []
    rw [hbi, hai]
    have hexp : Complex.exp (((∑ i : Fin (m + 1), (⟪Z (y i), c⟫ : ℝ)) : ℝ) * Complex.I)
        = ∏ j, g (y j) := by
      rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    rw [hexp]
    simp_rw [hprod]
    rw [← Finset.sum_mul]
    push_cast
    ring
  rw [hstep1]
  -- step 2: pull out the constant and swap the (finite) sum with the integral
  have hstep2 : ∫ y : Fin (m + 1) → ℝ, ((r : ℂ) * ∑ i, ∏ j, h i j (y j))
        ∂(Measure.pi fun _ : Fin (m + 1) => F)
      = (r : ℂ) * ∫ y : Fin (m + 1) → ℝ, (∑ i, ∏ j, h i j (y j))
        ∂(Measure.pi fun _ : Fin (m + 1) => F) := integral_const_mul _ _
  have hstep3 : ∫ y : Fin (m + 1) → ℝ, (∑ i, ∏ j, h i j (y j))
        ∂(Measure.pi fun _ : Fin (m + 1) => F)
      = ∑ i, ∫ y : Fin (m + 1) → ℝ, ∏ j, h i j (y j)
        ∂(Measure.pi fun _ : Fin (m + 1) => F) :=
    integral_finset_sum _ fun i _ => hint i
  -- step 3: Fubini on each summand, and the `n − 1` undistinguished factors give a power
  have hA : ∫ x, f x ∂F = mixCharFun (F.map Z) b c := by
    rw [mixCharFun_map F hZ]
  have hB : ∫ x, g x ∂F = charFun (F.map Z) c := by
    rw [charFun_apply, integral_map hZ.aemeasurable (by fun_prop)]
  have hterm : ∀ i : Fin (m + 1),
      ∫ y : Fin (m + 1) → ℝ, ∏ j, h i j (y j) ∂(Measure.pi fun _ : Fin (m + 1) => F)
        = mixCharFun (F.map Z) b c * charFun (F.map Z) c ^ m := by
    intro i
    have hfub : ∫ y : Fin (m + 1) → ℝ, ∏ j, h i j (y j)
          ∂(Measure.pi fun _ : Fin (m + 1) => F)
        = ∏ j, ∫ x, h i j x ∂F :=
      MeasureTheory.integral_fintype_prod_eq_prod (fun j : Fin (m + 1) => h i j)
    rw [hfub]
    have hval : ∀ j : Fin (m + 1),
        (∫ x, h i j x ∂F) = if j = i then mixCharFun (F.map Z) b c else charFun (F.map Z) c := by
      intro j
      by_cases hji : j = i
      · simp only [hhdef, hji, if_pos rfl]
        exact hA
      · simp only [hhdef, if_neg hji]
        exact hB
    simp_rw [hval]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl]
    congr 1
    rw [Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj)),
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  rw [hstep2, hstep3]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hrm : (r : ℝ) * ((m + 1 : ℕ) : ℝ) = Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    rw [hrdef, inv_mul_eq_div]
    exact Real.div_sqrt
  have hrmC : (r : ℂ) * ((m + 1 : ℕ) : ℂ) = ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast congrArg (fun z : ℝ => (z : ℂ)) hrm
  calc (r : ℂ) * (((m + 1 : ℕ) : ℂ) * (mixCharFun (F.map Z) b c * charFun (F.map Z) c ^ m))
      = ((r : ℂ) * ((m + 1 : ℕ) : ℂ))
          * (mixCharFun (F.map Z) b c * charFun (F.map Z) c ^ m) := by ring
    _ = (Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ) * mixCharFun (F.map Z) b c
          * charFun (F.map Z) c ^ m := by rw [hrmC]; ring

/-- **First-order Taylor bound for the mixed characteristic function.**

For a law `μ` that is centred in the direction `b`,

`‖∫ ⟪x,b⟫ e^{i⟪x,t⟫} ∂μ − i ∫ ⟪x,b⟫⟪x,t⟫ ∂μ‖ ≤ (3/2) ∫ |⟪x,b⟫| ⟪x,t⟫² ∂μ`.

The centring kills the constant term of `e^{i⟪x,t⟫} = 1 + i⟪x,t⟫ + O(⟪x,t⟫²)` and what survives
at first order is the *covariance* of the two directions. The remainder costs one moment more
than the plain characteristic function would (`|⟪x,b⟫|⟪x,t⟫²` rather than `⟪x,t⟫²`) — this is
the "one extra moment of the summands under the integral" that the studentized route pays. -/
theorem norm_mixCharFun_sub_mul_I_le (μ : Measure E) [IsProbabilityMeasure μ] {b t : E}
    (hb : Integrable (fun x : E => (⟪x, b⟫ : ℝ)) μ)
    (hbt : Integrable (fun x : E => (⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ)) μ)
    (hbt2 : Integrable (fun x : E => |(⟪x, b⟫ : ℝ)| * (⟪x, t⟫ : ℝ) ^ 2) μ)
    (hmean : ∫ x, (⟪x, b⟫ : ℝ) ∂μ = 0) :
    ‖mixCharFun μ b t - Complex.I * ((∫ x, (⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) ∂μ : ℝ) : ℂ)‖
      ≤ 3 / 2 * ∫ x, |(⟪x, b⟫ : ℝ)| * (⟪x, t⟫ : ℝ) ^ 2 ∂μ := by
  have hbm : Measurable fun x : E => (⟪x, b⟫ : ℝ) := measurable_inner_right b
  have htm : Measurable fun x : E => (⟪x, t⟫ : ℝ) := measurable_inner_right t
  -- the three integrable pieces of the expansion of the integrand
  have hA : Integrable
      (fun x : E => ((⟪x, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) μ := by
    refine Integrable.mono' hb.norm (by fun_prop) ?_
    filter_upwards with x
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    simp
  have hB : Integrable (fun x : E => ((⟪x, b⟫ : ℝ) : ℂ)) μ := hb.ofReal
  have hCeq : (fun x : E => ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)))
      = fun x : E => Complex.I * (((⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) : ℝ) : ℂ) := by
    funext x
    push_cast
    ring
  have hC : Integrable
      (fun x : E => ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ))) μ := by
    rw [hCeq]
    exact hbt.ofReal.const_mul Complex.I
  -- the exact identity: the difference is the integral of the second-order remainder
  have hkey : ∫ x, ((⟪x, b⟫ : ℝ) : ℂ)
        * (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1 - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ
      = mixCharFun μ b t - Complex.I * ((∫ x, (⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) ∂μ : ℝ) : ℂ) := by
    have hexp : ∀ x : E, ((⟪x, b⟫ : ℝ) : ℂ)
          * (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1 - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ))
        = ((⟪x, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)
          - ((⟪x, b⟫ : ℝ) : ℂ)
          - ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) := fun x => by ring
    have hIB : ∫ x, ((⟪x, b⟫ : ℝ) : ℂ) ∂μ = 0 := by
      rw [integral_complex_ofReal, hmean, Complex.ofReal_zero]
    have hIC : ∫ x, ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ
        = Complex.I * ((∫ x, (⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) ∂μ : ℝ) : ℂ) := by
      have h1 : ∫ x, Complex.I * (((⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) : ℝ) : ℂ) ∂μ
          = Complex.I * ∫ x, (((⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) : ℝ) : ℂ) ∂μ :=
        integral_const_mul _ _
      rw [hCeq, h1, integral_complex_ofReal]
    calc ∫ x, ((⟪x, b⟫ : ℝ) : ℂ)
            * (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1
              - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ
        = ∫ x, (((⟪x, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)
              - ((⟪x, b⟫ : ℝ) : ℂ)
              - ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ))) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hexp)
      _ = (∫ x, (((⟪x, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)
              - ((⟪x, b⟫ : ℝ) : ℂ)) ∂μ)
            - ∫ x, ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ :=
          integral_sub (hA.sub hB) hC
      _ = ((∫ x, ((⟪x, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) ∂μ)
            - ∫ x, ((⟪x, b⟫ : ℝ) : ℂ) ∂μ)
            - ∫ x, ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ := by
          rw [integral_sub hA hB]
      _ = mixCharFun μ b t - Complex.I * ((∫ x, (⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) ∂μ : ℝ) : ℂ) := by
          rw [hIB, hIC, mixCharFun, sub_zero]
  rw [← hkey]
  have hdom : Integrable (fun x : E => 3 / 2 * (|(⟪x, b⟫ : ℝ)| * (⟪x, t⟫ : ℝ) ^ 2)) μ :=
    hbt2.const_mul (3 / 2)
  have hpt : ∀ x : E, ‖((⟪x, b⟫ : ℝ) : ℂ)
        * (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1 - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ))‖
      ≤ 3 / 2 * (|(⟪x, b⟫ : ℝ)| * (⟪x, t⟫ : ℝ) ^ 2) := by
    intro x
    have hcomm : Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1 - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)
        = Complex.exp (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) - 1
          - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ) := by
      rw [mul_comm ((⟪x, t⟫ : ℝ) : ℂ) Complex.I]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hcomm]
    calc |(⟪x, b⟫ : ℝ)| * ‖Complex.exp (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) - 1
            - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)‖
        ≤ |(⟪x, b⟫ : ℝ)| * (3 * (⟪x, t⟫ : ℝ) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (norm_cexp_sub_one_sub_mul_I_le _) (abs_nonneg _)
      _ = 3 / 2 * (|(⟪x, b⟫ : ℝ)| * (⟪x, t⟫ : ℝ) ^ 2) := by ring
  refine (norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpt)).trans ?_
  exact le_of_eq (integral_const_mul _ _)

/-- **(M1)(b), assembled: the one-term expansion of the mixed characteristic function of a
vector root.**

`‖∫ ⟪w,b⟫ e^{i⟪w,a⟫} ∂ρ_n − i κ φ(n^{-1/2} a)^{n−1}‖ ≤ 3 M /(2√n)`, with
`κ = ∫ ⟪x,b⟫⟪x,a⟫` the covariance of the two directions and
`M = ∫ |⟪x,b⟫|⟪x,a⟫²` the mixed third moment, for a law centred in the direction `b`.

This is the estimate the studentized route of `Bootstrap/Edgeworth.lean` records as (M1)(b) —
the expansion of `∂_s ψ_n(θ, s)|_{s=0}`, equivalently of `E[V e^{iθU}]`, which cannot be
obtained by differentiating the inequality of `norm_charFun_vecRootLaw_sub_edgeworth_le`.

Two features are worth recording. First, the leading term is *not* damped by the extra `n^{-1/2}`
that the naive count suggests: the `√n` produced by the factorisation cancels exactly against
the `n^{-1/2}` of the covariance in the rescaled direction, so the mixed quantity has a
nonvanishing limit `i κ e^{−v/2}`, which is precisely the source of the studentized
`n^{-1/2}` coefficient `(1/6)γ(2t² + 1)` and of its difference from the centred one. Second,
what remains between this statement and the Gaussian limit is only the replacement of
`φ(n^{-1/2} a)^{n−1}` by `e^{−v/2}`, i.e. a Berry–Esseen-level estimate for an `(n−1)`-st power
at the argument `n^{-1/2}` — a mismatch of one factor with
`norm_charFun_smul_pow_sub_edgeworth_le`, not a new analytic difficulty. -/
theorem norm_mixCharFun_vecRootLaw_sub_le (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) {a b : E} (m : ℕ)
    (hb : Integrable (fun x : E => (⟪x, b⟫ : ℝ)) (F.map Z))
    (hba : Integrable (fun x : E => (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ)) (F.map Z))
    (hba2 : Integrable (fun x : E => |(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) (F.map Z))
    (hmean : ∫ x, (⟪x, b⟫ : ℝ) ∂(F.map Z) = 0) :
    ‖mixCharFun (vecRootLaw F Z (m + 1)) b a
        - Complex.I * ((∫ x, (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z) : ℝ) : ℂ)
            * charFun (F.map Z) ((Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • a) ^ m‖
      ≤ 3 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))
          * ∫ x, |(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z) := by
  haveI : IsProbabilityMeasure (F.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hNpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hsq : (0 : ℝ) < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hNpos
  set r : ℝ := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ with hrdef
  set c : E := r • a with hcdef
  set κ : ℝ := ∫ x, (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z) with hκdef
  set M : ℝ := ∫ x, |(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z) with hMdef
  have hc1 : ∀ x : E, (⟪x, c⟫ : ℝ) = r * (⟪x, a⟫ : ℝ) := fun x => by
    rw [hcdef, real_inner_smul_right]
  -- the two directional moments in the rescaled direction `c`
  have hκc : ∫ x, (⟪x, b⟫ : ℝ) * (⟪x, c⟫ : ℝ) ∂(F.map Z) = r * κ := by
    have h1 : ∀ x : E, (⟪x, b⟫ : ℝ) * (⟪x, c⟫ : ℝ)
        = r * ((⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ)) := fun x => by rw [hc1 x]; ring
    simp_rw [h1]
    rw [hκdef]
    exact integral_const_mul _ _
  have hMc : ∫ x, |(⟪x, b⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2 ∂(F.map Z) = r ^ 2 * M := by
    have h1 : ∀ x : E, |(⟪x, b⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2
        = r ^ 2 * (|(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) := fun x => by rw [hc1 x]; ring
    simp_rw [h1]
    rw [hMdef]
    exact integral_const_mul _ _
  have hbtc : Integrable (fun x : E => (⟪x, b⟫ : ℝ) * (⟪x, c⟫ : ℝ)) (F.map Z) := by
    have h1 : (fun x : E => (⟪x, b⟫ : ℝ) * (⟪x, c⟫ : ℝ))
        = fun x : E => r * ((⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ)) := by
      funext x; rw [hc1 x]; ring
    rw [h1]
    exact hba.const_mul r
  have hbt2c : Integrable (fun x : E => |(⟪x, b⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2) (F.map Z) := by
    have h1 : (fun x : E => |(⟪x, b⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2)
        = fun x : E => r ^ 2 * (|(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) := by
      funext x; rw [hc1 x]; ring
    rw [h1]
    exact hba2.const_mul (r ^ 2)
  -- the single-factor estimate, in the rescaled direction
  have hone : ‖mixCharFun (F.map Z) b c - Complex.I * ((r * κ : ℝ) : ℂ)‖
      ≤ 3 / 2 * (r ^ 2 * M) := by
    have h := norm_mixCharFun_sub_mul_I_le (F.map Z) hb hbtc hbt2c hmean
    rwa [hκc, hMc] at h
  -- the factorisation, and the cancellation `√n · n^{-1/2} = 1`
  have hbZ : Integrable (fun x : ℝ => (⟪Z x, b⟫ : ℝ)) F :=
    (integrable_map_measure hb.aestronglyMeasurable hZ.aemeasurable).1 hb
  have hfac := mixCharFun_vecRootLaw F hZ hbZ m a
  rw [← hrdef, ← hcdef] at hfac
  have hsr : (Real.sqrt ((m + 1 : ℕ) : ℝ)) * r = 1 := by
    rw [hrdef]; field_simp
  have hsrC : ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * ((r : ℝ) : ℂ) = 1 := by
    exact_mod_cast congrArg (fun z : ℝ => (z : ℂ)) hsr
  have halg : mixCharFun (vecRootLaw F Z (m + 1)) b a
        - Complex.I * (κ : ℂ) * charFun (F.map Z) c ^ m
      = ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)
          * (mixCharFun (F.map Z) b c - Complex.I * ((r * κ : ℝ) : ℂ))
          * charFun (F.map Z) c ^ m := by
    rw [hfac]
    have hexp : ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * (Complex.I * ((r * κ : ℝ) : ℂ))
        = Complex.I * (κ : ℂ) := by
      rw [Complex.ofReal_mul]
      calc ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)
            * (Complex.I * (((r : ℝ) : ℂ) * ((κ : ℝ) : ℂ)))
          = (((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * ((r : ℝ) : ℂ))
              * (Complex.I * ((κ : ℝ) : ℂ)) := by ring
        _ = Complex.I * (κ : ℂ) := by rw [hsrC, one_mul]
    rw [mul_sub, hexp]
    ring
  rw [halg, norm_mul, norm_mul]
  have hBle : ‖charFun (F.map Z) c ^ m‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one c)
  have hM0 : (0 : ℝ) ≤ M := integral_nonneg fun x => by positivity
  have hnormsq : ‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)‖ = Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsq.le]
  calc ‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)‖
        * ‖mixCharFun (F.map Z) b c - Complex.I * ((r * κ : ℝ) : ℂ)‖
        * ‖charFun (F.map Z) c ^ m‖
      ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * (3 / 2 * (r ^ 2 * M)) * 1 := by
        rw [hnormsq]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hone hsq.le) hBle (norm_nonneg _)
          (mul_nonneg hsq.le (by positivity))
    _ = 3 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ)) * M := by
        have hne : Real.sqrt ((m + 1 : ℕ) : ℝ) ≠ 0 := hsq.ne'
        rw [hrdef]
        field_simp

/-! ### The multilinear extension

`mixCharFun` carries a **linear** weight `⟪·, b⟫`, and that is exactly one slot. The third-order
delta-method surrogate of the studentized route,
`Hₙ = u − uvr/2 + u³r²/2 + 3uv²r²/8` with `r = n^{-1/2}`, is a polynomial of degree four in the
two coordinates, so expanding `E[e^{iθHₙ}]` in powers of `r` produces the weights `uv`, `u³`,
`uv²` and `(uv)²` — bilinear, trilinear and quartic. None of them is a `mixCharFun`, and this
is what makes the surrogate's characteristic function unavailable from the one-slot theory
alone. (It affects the *second*-order surrogate equally: its leading correction already needs
`E[uv e^{iθu}]`.)

The extension is not a wall, and it is carried out here. The exact factorisation of
`mixCharFun_vecRootLaw` rests only on the weight `⟪root, b⟫` being a *sum over the coordinates*;
a product of `k` such sums expands (`Finset.prod_univ_sum`) into a sum over the `nᵏ`
**assignments** `σ : Fin k → Fin n` of weight slots to coordinates. Regrouping an assignment
fiberwise (`Finset.prod_fiberwise`) turns its summand into a genuine product over the
coordinates — coordinate `i` carrying the weights in the fiber `σ⁻¹(i)` — and Fubini on
`Measure.pi` evaluates it as a product of one-dimensional integrals. The result is

`multi_{ρ_n}(b, a) = n^{-k/2} ∑_{σ : Fin k → Fin n} ∏_{i<n} slot_{σ⁻¹(i)}(n^{-1/2} • a)`,

a purely combinatorial identity: no moment assumption enters it beyond what is needed to make
each summand integrable. The one-slot statement is the case `k = 1`, where every `σ` has a
single distinguished coordinate, all `n` summands are equal, and the surviving
`n · n^{-1/2} = √n` is the `√n` of `mixCharFun_vecRootLaw`.

The **diagonal/off-diagonal bookkeeping** the applications need is now visible in the identity
rather than hidden: assignments `σ` that are injective contribute `k` distinct factors each
carrying one slot (these give the "leading" terms), while assignments with collisions
concentrate several slots on one coordinate and are suppressed by the extra powers of
`n^{-1/2}` relative to the number of free coordinates. -/

/-- The **multilinearly weighted characteristic function**
`∫ (∏_{l<k} ⟪w, b l⟫) e^{i⟪w,t⟫} ∂μ`.

For `k = 1` this is `mixCharFun` (`multiCharFun_one`) and for `k = 0` it is `charFun`
(`multiCharFun_zero`). The studentized surrogate needs `k` up to `4`, with repetitions among
the `b l` — the slots are an indexed family, not a set. -/
noncomputable def multiCharFun (μ : Measure E) {k : ℕ} (b : Fin k → E) (t : E) : ℂ :=
  ∫ w, (∏ l : Fin k, ((⟪w, b l⟫ : ℝ) : ℂ)) * Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I) ∂μ

/-- The **single-coordinate factor** of the factorisation: the character in the direction `c`
of one summand, weighted by the inner products in the slots of `T`. `T = ∅` gives `charFun`
and `T = {l}` gives `mixCharFun`, both of the pushforward `F.map Z`. -/
noncomputable def slotCharFun (F : Measure ℝ) (Z : ℝ → E) {k : ℕ} (b : Fin k → E)
    (T : Finset (Fin k)) (c : E) : ℂ :=
  ∫ x, (∏ l ∈ T, ((⟪Z x, b l⟫ : ℝ) : ℂ)) * Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I) ∂F

omit [BorelSpace E] [SecondCountableTopology E] in
@[simp] lemma multiCharFun_zero (μ : Measure E) (b : Fin 0 → E) (t : E) :
    multiCharFun μ b t = charFun μ t := by
  simp [multiCharFun, charFun_apply]

omit [BorelSpace E] [SecondCountableTopology E] in
@[simp] lemma multiCharFun_one (μ : Measure E) (b : E) (t : E) :
    multiCharFun μ (fun _ : Fin 1 => b) t = mixCharFun μ b t := by
  simp [multiCharFun, mixCharFun]

lemma slotCharFun_empty (F : Measure ℝ) {Z : ℝ → E} (hZ : Measurable Z) {k : ℕ}
    (b : Fin k → E) (c : E) :
    slotCharFun F Z b ∅ c = charFun (F.map Z) c := by
  rw [slotCharFun, charFun_apply, integral_map hZ.aemeasurable (by fun_prop)]
  simp

lemma slotCharFun_singleton (F : Measure ℝ) {Z : ℝ → E} (hZ : Measurable Z) {k : ℕ}
    (b : Fin k → E) (l : Fin k) (c : E) :
    slotCharFun F Z b {l} c = mixCharFun (F.map Z) (b l) c := by
  rw [slotCharFun, mixCharFun_map F hZ]
  simp

/-- **The multilinearly weighted characteristic function of a vector root factorises exactly.**

`∫ (∏_{l<k} ⟪w, b l⟫) e^{i⟪w,a⟫} ∂(vecRootLaw F Z n)
   = n^{-k/2} ∑_{σ : Fin k → Fin n} ∏_{i<n} slot_{σ⁻¹(i)}(n^{-1/2} • a)`.

This is the `k`-slot generalisation of `mixCharFun_vecRootLaw`, and it is what the third-order
delta-method surrogate's characteristic function needs: the surrogate is a degree-four
polynomial in the coordinates of the root, so its transform is a finite combination of
`multiCharFun`s with `k ≤ 4`.

The only hypothesis is that every *sub-product* of the weights be `F`-integrable, which is what
makes each of the `nᵏ` assignment summands integrable on `Measure.pi`; for `Z = studentPair F`
and `b` drawn from the two coordinate directions it is a moment condition on `F` of order at
most `2k`. -/
theorem multiCharFun_vecRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) {k n : ℕ} (b : Fin k → E)
    (hint : ∀ T : Finset (Fin k),
      Integrable (fun x : ℝ => ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)|) F)
    (a : E) :
    multiCharFun (vecRootLaw F Z n) b a
      = (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) ^ k *
          ∑ σ : Fin k → Fin n, ∏ i : Fin n,
            slotCharFun F Z b (Finset.univ.filter fun l => σ l = i)
              ((Real.sqrt (n : ℝ))⁻¹ • a) := by
  classical
  set r : ℝ := (Real.sqrt (n : ℝ))⁻¹ with hrdef
  set c : E := r • a with hcdef
  set g : ℝ → ℂ := fun x => Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I) with hgdef
  have hgnorm : ∀ x, ‖g x‖ = 1 := by
    intro x; rw [hgdef]; simp [Complex.norm_exp]
  have hgm : Measurable g := by rw [hgdef]; fun_prop
  have hbm : ∀ l : Fin k, Measurable fun x : ℝ => (⟪Z x, b l⟫ : ℝ) :=
    fun l => (measurable_inner_right (b l)).comp hZ
  -- the single-coordinate factor attached to a set `T` of slots
  set u : Finset (Fin k) → ℝ → ℂ :=
    fun T x => (∏ l ∈ T, ((⟪Z x, b l⟫ : ℝ) : ℂ)) * g x with hudef
  have hum : ∀ T, Measurable (u T) := by
    intro T
    refine Measurable.mul ?_ hgm
    exact Finset.measurable_prod _ fun l _ => (Complex.measurable_ofReal.comp (hbm l))
  have hunorm : ∀ (T : Finset (Fin k)) (x : ℝ), ‖u T x‖ = ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)| := by
    intro T x
    rw [hudef, norm_mul, hgnorm, mul_one, norm_prod]
    exact Finset.prod_congr rfl fun l _ => by
      rw [Complex.norm_real, Real.norm_eq_abs]
  have huint : ∀ T, Integrable (u T) F := by
    intro T
    refine Integrable.mono' (hint T) (hum T).aestronglyMeasurable ?_
    filter_upwards with x
    exact le_of_eq (hunorm T x)
  -- the fibre of an assignment over a coordinate
  set fib : (Fin k → Fin n) → Fin n → Finset (Fin k) :=
    fun σ i => Finset.univ.filter fun l => σ l = i with hfibdef
  -- step 1: the integrand over `Measure.pi`
  have hstep1 : multiCharFun (vecRootLaw F Z n) b a
      = ∫ y : Fin n → ℝ, ((r : ℂ) ^ k * ∑ σ : Fin k → Fin n, ∏ i, u (fib σ i) (y i))
        ∂(Measure.pi fun _ : Fin n => F) := by
    rw [multiCharFun, vecRootLaw,
      integral_map (measurable_vecRoot hZ n).aemeasurable (by fun_prop)]
    simp only [← hrdef]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    -- the character factorises over the coordinates
    have hai : (⟪r • ∑ i, Z (y i), a⟫ : ℝ) = ∑ i : Fin n, (⟪Z (y i), c⟫ : ℝ) := by
      calc (⟪r • ∑ i, Z (y i), a⟫ : ℝ)
          = r * ⟪∑ i, Z (y i), a⟫ := real_inner_smul_left _ _ _
        _ = r * ∑ i : Fin n, (⟪Z (y i), a⟫ : ℝ) := by rw [sum_inner]
        _ = ∑ i : Fin n, r * (⟪Z (y i), a⟫ : ℝ) := Finset.mul_sum _ _ _
        _ = ∑ i : Fin n, (⟪Z (y i), c⟫ : ℝ) := by
            simp only [hcdef, real_inner_smul_right]
    have hexp : Complex.exp (((∑ i : Fin n, (⟪Z (y i), c⟫ : ℝ)) : ℝ) * Complex.I)
        = ∏ i, g (y i) := by
      rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    -- the weight expands into assignments
    have hwt : (∏ l : Fin k, ((⟪r • ∑ i, Z (y i), b l⟫ : ℝ) : ℂ))
        = (r : ℂ) ^ k * ∑ σ : Fin k → Fin n, ∏ l : Fin k,
            ((⟪Z (y (σ l)), b l⟫ : ℝ) : ℂ) := by
      have hbl : ∀ l : Fin k, ((⟪r • ∑ i, Z (y i), b l⟫ : ℝ) : ℂ)
          = (r : ℂ) * ∑ i : Fin n, ((⟪Z (y i), b l⟫ : ℝ) : ℂ) := by
        intro l
        have : (⟪r • ∑ i, Z (y i), b l⟫ : ℝ) = r * ∑ i : Fin n, (⟪Z (y i), b l⟫ : ℝ) := by
          rw [real_inner_smul_left, sum_inner]
        rw [this]
        push_cast
        ring
      simp_rw [hbl]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      have := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin n)))
        (fun (l : Fin k) (i : Fin n) => ((⟪Z (y i), b l⟫ : ℝ) : ℂ))
      rw [this, Fintype.piFinset_univ]
    rw [hai, hexp, hwt]
    -- each assignment summand is the product over coordinates of the slot factors
    have hassign : ∀ σ : Fin k → Fin n,
        (∏ l : Fin k, ((⟪Z (y (σ l)), b l⟫ : ℝ) : ℂ)) * ∏ i, g (y i)
          = ∏ i, u (fib σ i) (y i) := by
      intro σ
      have hsplit : (∏ i, u (fib σ i) (y i))
          = (∏ i : Fin n, ∏ l ∈ fib σ i, ((⟪Z (y i), b l⟫ : ℝ) : ℂ)) * ∏ i, g (y i) := by
        rw [hudef, ← Finset.prod_mul_distrib]
      have hfibre : (∏ i : Fin n, ∏ l ∈ fib σ i, ((⟪Z (y i), b l⟫ : ℝ) : ℂ))
          = ∏ l : Fin k, ((⟪Z (y (σ l)), b l⟫ : ℝ) : ℂ) := by
        have hcongr : ∀ i : Fin n, (∏ l ∈ fib σ i, ((⟪Z (y i), b l⟫ : ℝ) : ℂ))
            = ∏ l ∈ fib σ i, ((⟪Z (y (σ l)), b l⟫ : ℝ) : ℂ) := by
          intro i
          refine Finset.prod_congr rfl fun l hl => ?_
          have : σ l = i := (Finset.mem_filter.1 hl).2
          rw [this]
        simp_rw [hcongr]
        exact Finset.prod_fiberwise Finset.univ σ fun l => ((⟪Z (y (σ l)), b l⟫ : ℝ) : ℂ)
      rw [hsplit, hfibre]
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => hassign σ
  -- step 2: pull out the constant, exchange the finite sum with the integral
  have hint2 : ∀ σ : Fin k → Fin n,
      Integrable (fun y : Fin n → ℝ => ∏ i, u (fib σ i) (y i))
        (Measure.pi fun _ : Fin n => F) :=
    fun σ => Integrable.fintype_prod fun i => huint (fib σ i)
  have hstep2 : (∫ y : Fin n → ℝ, ((r : ℂ) ^ k * ∑ σ : Fin k → Fin n, ∏ i, u (fib σ i) (y i))
        ∂(Measure.pi fun _ : Fin n => F))
      = (r : ℂ) ^ k * ∫ y : Fin n → ℝ, (∑ σ : Fin k → Fin n, ∏ i, u (fib σ i) (y i))
        ∂(Measure.pi fun _ : Fin n => F) := integral_const_mul _ _
  have hstep3 : (∫ y : Fin n → ℝ, (∑ σ : Fin k → Fin n, ∏ i, u (fib σ i) (y i))
        ∂(Measure.pi fun _ : Fin n => F))
      = ∑ σ : Fin k → Fin n, ∫ y : Fin n → ℝ, ∏ i, u (fib σ i) (y i)
        ∂(Measure.pi fun _ : Fin n => F) :=
    integral_finset_sum _ fun σ _ => hint2 σ
  -- step 3: Fubini on each assignment summand
  have hstep4 : ∀ σ : Fin k → Fin n,
      (∫ y : Fin n → ℝ, ∏ i, u (fib σ i) (y i) ∂(Measure.pi fun _ : Fin n => F))
        = ∏ i, slotCharFun F Z b (fib σ i) c :=
    fun σ => MeasureTheory.integral_fintype_prod_eq_prod fun i : Fin n => u (fib σ i)
  rw [hstep1, hstep2, hstep3]
  simp_rw [hstep4]
  rfl

end Mixed

/-! ### The `k = 2` diagonal/off-diagonal split, and why it is not bookkeeping

`multiCharFun_vecRootLaw` is an **identity**, not an estimate: it expresses the multilinearly
weighted characteristic function of a vector root as a sum over the `nᵏ` assignments of weight
slots to coordinates. Turning it into an estimate is what the studentized surrogate's transform
needs, and `norm_mixCharFun_vecRootLaw_sub_le` does it only for `k = 1`.

The `k = 1` case is deceptively simple because there is nothing to split: all `n` assignments
coincide, and the whole content is the surviving `n · n^{-1/2} = √n`. For `k = 2` the sum
genuinely splits, and **both halves contribute at the same order**:

* the `n` *diagonal* assignments give `n^{-1} · n · slot_{\{0,1\}}(c) · φ(c)^{n−1}`, of order `1`;
* the `n(n − 1)` *off-diagonal* ones give
  `n^{-1} · n(n − 1) · slot_{\{0\}}(c) · slot_{\{1\}}(c) · φ(c)^{n−2}`, and each single-slot factor
  is `O(n^{-1/2})` when `Z` is centred — so this block is `n^{-1} · n² · O(n⁻¹) = O(1)` as well.

Discarding the off-diagonal block, as the `k = 1` picture invites, would therefore change the
*limit* and not merely the remainder. That is why `Bootstrap/Edgeworth.lean`'s wave-23 note
records the `k ≥ 2` estimate as a genuine analytic residue rather than as wiring.

`multiCharFun_vecRootLaw_two` is the exact combinatorial half of that estimate: it evaluates the
assignment sum in closed form, leaving only a one-factor Taylor bound on `slot_{\{0\}}`,
`slot_{\{1\}}` and `slot_{\{0,1\}}` — the same kind of estimate
`norm_mixCharFun_vecRootLaw_sub_le` already performs at `k = 1`. The identity holds for every
`N`, including the degenerate `N = 0` and `N = 1` where the coefficient `N(N − 1)` vanishes on
its own. -/

section MultiTwo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

private lemma prod_fiber_diag {N : ℕ} (g : Finset (Fin 2) → ℂ) (j : Fin N) :
    (∏ i : Fin N, g (Finset.univ.filter fun l : Fin 2 => (![j, j] : Fin 2 → Fin N) l = i))
      = g Finset.univ * g ∅ ^ (N - 1) := by
  classical
  set h : Fin N → ℂ :=
    fun i => g (Finset.univ.filter fun l : Fin 2 => (![j, j] : Fin 2 → Fin N) l = i) with hh
  have hj : h j = g Finset.univ := by
    have hset : (Finset.univ.filter fun l : Fin 2 => (![j, j] : Fin 2 → Fin N) l = j)
        = Finset.univ := by
      ext l
      fin_cases l <;> simp
    rw [hh]
    simp only [hset]
  have hother : ∀ i : Fin N, i ≠ j → h i = g ∅ := by
    intro i hi
    have hset : (Finset.univ.filter fun l : Fin 2 => (![j, j] : Fin 2 → Fin N) l = i)
        = ∅ := by
      ext l
      fin_cases l <;> simp [Ne.symm hi]
    rw [hh]
    simp only [hset]
  rw [← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ j), hj]
  congr 1
  have hcard : (Finset.univ.erase j).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  calc (∏ x ∈ Finset.univ.erase j, h x) = ∏ _x ∈ Finset.univ.erase j, g ∅ :=
        Finset.prod_congr rfl fun x hx => hother x (Finset.mem_erase.1 hx).1
    _ = g ∅ ^ (N - 1) := by rw [Finset.prod_const, hcard]

private lemma prod_fiber_offdiag {N : ℕ} (g : Finset (Fin 2) → ℂ) {j k : Fin N} (hjk : j ≠ k) :
    (∏ i : Fin N, g (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = i))
      = g {0} * (g {1} * g ∅ ^ (N - 2)) := by
  classical
  set h : Fin N → ℂ :=
    fun i => g (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = i) with hh
  have hj : h j = g {0} := by
    have hset : (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = j)
        = {0} := by
      ext l
      fin_cases l <;> simp [Ne.symm hjk]
    rw [hh]
    simp only [hset]
  have hk : h k = g {1} := by
    have hset : (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = k)
        = {1} := by
      ext l
      fin_cases l <;> simp [hjk]
    rw [hh]
    simp only [hset]
  have hother : ∀ i : Fin N, i ≠ j → i ≠ k → h i = g ∅ := by
    intro i hij hik
    have hset : (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = i)
        = ∅ := by
      ext l
      fin_cases l <;> simp [Ne.symm hij, Ne.symm hik]
    rw [hh]
    simp only [hset]
  have hkmem : k ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨Ne.symm hjk, Finset.mem_univ k⟩
  rw [← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ j), hj,
    ← Finset.mul_prod_erase (Finset.univ.erase j) h hkmem, hk]
  congr 2
  have hcard : ((Finset.univ.erase j).erase k).card = N - 2 := by
    rw [Finset.card_erase_of_mem hkmem, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
    omega
  calc (∏ x ∈ (Finset.univ.erase j).erase k, h x)
      = ∏ _x ∈ (Finset.univ.erase j).erase k, g ∅ :=
        Finset.prod_congr rfl fun x hx =>
          hother x (Finset.mem_erase.1 (Finset.mem_erase.1 hx).2).1 (Finset.mem_erase.1 hx).1
    _ = g ∅ ^ (N - 2) := by rw [Finset.prod_const, hcard]

private lemma sum_pi_fin_two {N : ℕ} {M : Type*} [AddCommMonoid M] (G : (Fin 2 → Fin N) → M) :
    (∑ σ : Fin 2 → Fin N, G σ) = ∑ j : Fin N, ∑ k : Fin N, G ![j, k] := by
  have hfun : ∀ σ : Fin 2 → Fin N, (![σ 0, σ 1] : Fin 2 → Fin N) = σ := by
    intro σ
    funext l
    fin_cases l <;> rfl
  have h1 : (∑ σ : Fin 2 → Fin N, G σ) = ∑ p : Fin N × Fin N, G ![p.1, p.2] :=
    Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin N) _ _ fun σ => by
      simp only [piFinTwoEquiv_apply]
      exact (congrArg G (hfun σ)).symm
  rw [h1, Fintype.sum_prod_type]

variable (F : Measure ℝ) (Z : ℝ → E) (b : Fin 2 → E) (c : E)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The diagonal fibre computation, in the shape `multiCharFun_vecRootLaw` produces. -/
private lemma prod_fiber_diag' {N : ℕ} (j : Fin N) :
    (∏ i : Fin N, slotCharFun F Z b
        (Finset.univ.filter fun l : Fin 2 => (![j, j] : Fin 2 → Fin N) l = i) c)
      = slotCharFun F Z b Finset.univ c * slotCharFun F Z b ∅ c ^ (N - 1) :=
  prod_fiber_diag (fun T => slotCharFun F Z b T c) j

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The off-diagonal fibre computation, in the shape `multiCharFun_vecRootLaw` produces. -/
private lemma prod_fiber_offdiag' {N : ℕ} {j k : Fin N} (hjk : j ≠ k) :
    (∏ i : Fin N, slotCharFun F Z b
        (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = i) c)
      = slotCharFun F Z b {0} c *
          (slotCharFun F Z b {1} c * slotCharFun F Z b ∅ c ^ (N - 2)) :=
  prod_fiber_offdiag (fun T => slotCharFun F Z b T c) hjk

set_option maxHeartbeats 800000 in
-- The `Finset` rewrites below run over a nested sum whose summand is a product over `Fin N`
-- of `slotCharFun`s; the default heartbeat budget is not enough.
/-- **The `k = 2` assignment sum, in closed form.**

`multi_{ρ_N}(b, a) = N^{-1}(N · slot_{{0,1}}(c) φ(c)^{N−1} + N(N−1) · slot_{{0}}(c) slot_{{1}}(c)
φ(c)^{N−2})` with `c = N^{-1/2} • a`.

This is the exact combinatorial half of the `k = 2` estimate the studentized surrogate's
transform consumes; see the note above for why the second summand cannot be dropped. -/
theorem multiCharFun_vecRootLaw_two (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) {N : ℕ} (b : Fin 2 → E)
    (hint : ∀ T : Finset (Fin 2),
      Integrable (fun x : ℝ => ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)|) F)
    (a : E) :
    multiCharFun (vecRootLaw F Z N) b a
      = (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) ^ 2 *
        ((N : ℂ) * (slotCharFun F Z b Finset.univ ((Real.sqrt (N : ℝ))⁻¹ • a)
              * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 1))
          + (N : ℂ) * ((N : ℂ) - 1)
              * (slotCharFun F Z b {0} ((Real.sqrt (N : ℝ))⁻¹ • a)
                  * (slotCharFun F Z b {1} ((Real.sqrt (N : ℝ))⁻¹ • a)
                      * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 2)))) := by
  classical
  rw [multiCharFun_vecRootLaw F hZ b hint a]
  congr 1
  rw [sum_pi_fin_two]
  have hempty := slotCharFun_empty F hZ b ((Real.sqrt (N : ℝ))⁻¹ • a)
  have hdiag : ∀ j : Fin N,
      (∏ i : Fin N, slotCharFun F Z b
          (Finset.univ.filter fun l : Fin 2 => (![j, j] : Fin 2 → Fin N) l = i)
          ((Real.sqrt (N : ℝ))⁻¹ • a))
        = slotCharFun F Z b Finset.univ ((Real.sqrt (N : ℝ))⁻¹ • a)
            * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 1) := by
    intro j
    rw [prod_fiber_diag' F Z b ((Real.sqrt (N : ℝ))⁻¹ • a) j, hempty]
  have hoff : ∀ j k : Fin N, j ≠ k →
      (∏ i : Fin N, slotCharFun F Z b
          (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = i)
          ((Real.sqrt (N : ℝ))⁻¹ • a))
        = slotCharFun F Z b {0} ((Real.sqrt (N : ℝ))⁻¹ • a)
            * (slotCharFun F Z b {1} ((Real.sqrt (N : ℝ))⁻¹ • a)
                * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 2)) := by
    intro j k hjk
    rw [prod_fiber_offdiag' F Z b ((Real.sqrt (N : ℝ))⁻¹ • a) hjk, hempty]
  have hinner : ∀ j : Fin N,
      (∑ k : Fin N, ∏ i : Fin N, slotCharFun F Z b
          (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = i)
          ((Real.sqrt (N : ℝ))⁻¹ • a))
        = slotCharFun F Z b Finset.univ ((Real.sqrt (N : ℝ))⁻¹ • a)
              * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 1)
          + ((N : ℂ) - 1) * (slotCharFun F Z b {0} ((Real.sqrt (N : ℝ))⁻¹ • a)
              * (slotCharFun F Z b {1} ((Real.sqrt (N : ℝ))⁻¹ • a)
                  * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 2))) := by
    intro j
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
    have hcard : (Finset.univ.erase j).card = N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    have hcast : (((N - 1 : ℕ) : ℂ)) = (N : ℂ) - 1 := by
      have := Nat.cast_sub (R := ℂ) hN
      simpa using this
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j), hdiag j,
      Finset.sum_congr rfl (fun k hk => hoff j k (Ne.symm (Finset.mem_erase.1 hk).1)),
      Finset.sum_const, hcard, nsmul_eq_mul, hcast]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hinner j), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end MultiTwo


/-! ## One-factor bookkeeping: from `φ^{n−1}` to `φ^n`

`norm_mixCharFun_vecRootLaw_sub_le` compares the mixed characteristic function of a vector
root with `iκ φ(n^{-1/2}a)^{n−1}` — an `(n−1)`-st power, while `charFun_vecRootLaw` and the
damped expansion `norm_charFun_smul_pow_sub_edgeworth_le` both speak about the `n`-th power
`φ(n^{-1/2}a)^n = φ_{ρ_n}(a)`. This section supplies the missing factor.

The estimate is elementary and costs `O(n^{-1})`, i.e. it is invisible at the accuracy of a
one-term expansion. Indeed `z^{n−1} − z^n = z^{n−1}(1 − z)`, and `‖z‖ ≤ 1` for a characteristic
function, so the whole difference is bounded by `‖1 − φ(c)‖` at the *rescaled* argument
`c = n^{-1/2} • a`; for a law centred in the direction `a` this is
`‖∫ (e^{i⟪x,c⟫} − 1 − i⟪x,c⟫)‖ ≤ (3/2)∫⟪x,c⟫² = (3/2) v(a)/n`.

The centring is what makes this `O(n^{-1})` rather than `O(n^{-1/2})`: without it the linear
term survives and the bound is only `‖∫⟪x,c⟫‖ = O(n^{-1/2})`, which would swamp the
`n^{-1/2}` coefficient the studentized expansion is trying to produce. -/

section OneFactor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **A characteristic function is quadratically close to `1` in a centred direction.**
`‖φ_μ(t) − 1‖ ≤ (3/2)∫⟪x,t⟫²` whenever `∫⟪x,t⟫ = 0`.

This is `norm_cexp_sub_one_sub_mul_I_le` integrated against `μ`, with the centring used to
delete the linear term of the expansion of `e^{i⟪x,t⟫}`. -/
theorem norm_charFun_sub_one_le (μ : Measure E) [IsProbabilityMeasure μ] {t : E}
    (hint1 : Integrable (fun x : E => (⟪x, t⟫ : ℝ)) μ)
    (hint2 : Integrable (fun x : E => (⟪x, t⟫ : ℝ) ^ 2) μ)
    (hmean : ∫ x, (⟪x, t⟫ : ℝ) ∂μ = 0) :
    ‖charFun μ t - 1‖ ≤ 3 / 2 * ∫ x, (⟪x, t⟫ : ℝ) ^ 2 ∂μ := by
  have htm : Measurable fun x : E => (⟪x, t⟫ : ℝ) := measurable_inner_right t
  have hA : Integrable (fun x : E => Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) ?_
    filter_upwards with x
    rw [Complex.norm_exp]
    simp
  have hC : Integrable (fun x : E => Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) μ :=
    hint1.ofReal.const_mul Complex.I
  have hcf : ∫ x, Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) ∂μ = charFun μ t := by
    rw [charFun_apply]
  have hIC : ∫ x, Complex.I * ((⟪x, t⟫ : ℝ) : ℂ) ∂μ = 0 := by
    have h1 : ∫ x, Complex.I * ((⟪x, t⟫ : ℝ) : ℂ) ∂μ
        = Complex.I * ∫ x, ((⟪x, t⟫ : ℝ) : ℂ) ∂μ := integral_const_mul _ _
    rw [h1, integral_complex_ofReal, hmean, Complex.ofReal_zero, mul_zero]
  have hkey : ∫ x, (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1
        - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ = charFun μ t - 1 := by
    have hs1 : ∫ x, (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1
          - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ
        = (∫ x, (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1) ∂μ)
          - ∫ x, Complex.I * ((⟪x, t⟫ : ℝ) : ℂ) ∂μ :=
      integral_sub (hA.sub (integrable_const 1)) hC
    have hs2 : ∫ x, (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1) ∂μ
        = (∫ x, Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) ∂μ) - ∫ _x : E, (1 : ℂ) ∂μ :=
      integral_sub hA (integrable_const 1)
    rw [hs1, hs2, hIC, hcf]
    simp
  rw [← hkey]
  have hdom : Integrable (fun x : E => 3 / 2 * (⟪x, t⟫ : ℝ) ^ 2) μ := hint2.const_mul (3 / 2)
  have hpt : ∀ x : E, ‖Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1
      - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)‖ ≤ 3 / 2 * (⟪x, t⟫ : ℝ) ^ 2 := by
    intro x
    have hcomm : Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1 - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)
        = Complex.exp (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) - 1
          - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ) := by
      rw [mul_comm ((⟪x, t⟫ : ℝ) : ℂ) Complex.I]
    rw [hcomm]
    have h := norm_cexp_sub_one_sub_mul_I_le (⟪x, t⟫ : ℝ)
    linarith
  refine (norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpt)).trans ?_
  exact le_of_eq (integral_const_mul _ _)

/-- Dropping one factor from a power of a number of modulus at most `1` costs `‖1 − z‖`. -/
lemma norm_pow_sub_pow_succ_le {z : ℂ} (hz : ‖z‖ ≤ 1) (m : ℕ) :
    ‖z ^ m - z ^ (m + 1)‖ ≤ ‖1 - z‖ := by
  have he : z ^ m - z ^ (m + 1) = z ^ m * (1 - z) := by ring
  rw [he, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hz

/-- **The one-factor comparison for the characteristic function of a vector root.**

`‖φ_{F∘Z⁻¹}(n^{-1/2}a)^{n−1} − φ_{ρ_n}(a)‖ ≤ (3/2) v/n`, with `v = ∫⟪x,a⟫²` the directional
variance, for a law centred in the direction `a`.

This is the bookkeeping that lets the `(n−1)`-st power produced by the mixed expansion
(M1)(b) be replaced by the characteristic function of the vector root itself, to which the
damped expansion `norm_charFun_vecRootLaw_sub_edgeworth_le` applies verbatim. -/
theorem norm_charFun_pow_sub_charFun_vecRootLaw_le (F : Measure ℝ) [IsProbabilityMeasure F]
    {Z : ℝ → E} (hZ : Measurable Z) {a : E} (m : ℕ)
    (ha : Integrable (fun x : E => (⟪x, a⟫ : ℝ)) (F.map Z))
    (ha2 : Integrable (fun x : E => (⟪x, a⟫ : ℝ) ^ 2) (F.map Z))
    (hmean : ∫ x, (⟪x, a⟫ : ℝ) ∂(F.map Z) = 0) :
    ‖charFun (F.map Z) ((Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • a) ^ m
        - charFun (vecRootLaw F Z (m + 1)) a‖
      ≤ 3 / 2 * ((∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) / ((m : ℝ) + 1)) := by
  haveI : IsProbabilityMeasure (F.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hNpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  set r : ℝ := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ with hrdef
  set c : E := r • a with hcdef
  have hc1 : ∀ x : E, (⟪x, c⟫ : ℝ) = r * (⟪x, a⟫ : ℝ) := fun x => by
    rw [hcdef, real_inner_smul_right]
  have hrsq : r ^ 2 = (((m : ℝ) + 1))⁻¹ := by
    rw [hrdef, inv_pow, Real.sq_sqrt hNpos.le]
    push_cast
    ring
  -- the directional data in the rescaled direction
  have hac : Integrable (fun x : E => (⟪x, c⟫ : ℝ)) (F.map Z) := by
    have h1 : (fun x : E => (⟪x, c⟫ : ℝ)) = fun x : E => r * (⟪x, a⟫ : ℝ) := by
      funext x; exact hc1 x
    rw [h1]
    exact ha.const_mul r
  have hac2 : Integrable (fun x : E => (⟪x, c⟫ : ℝ) ^ 2) (F.map Z) := by
    have h1 : (fun x : E => (⟪x, c⟫ : ℝ) ^ 2) = fun x : E => r ^ 2 * (⟪x, a⟫ : ℝ) ^ 2 := by
      funext x; rw [hc1 x]; ring
    rw [h1]
    exact ha2.const_mul (r ^ 2)
  have hmeanc : ∫ x, (⟪x, c⟫ : ℝ) ∂(F.map Z) = 0 := by
    have h1 : ∀ x : E, (⟪x, c⟫ : ℝ) = r * (⟪x, a⟫ : ℝ) := hc1
    simp_rw [h1]
    rw [integral_const_mul, hmean, mul_zero]
  have hvarc : ∫ x, (⟪x, c⟫ : ℝ) ^ 2 ∂(F.map Z)
      = r ^ 2 * ∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z) := by
    have h1 : ∀ x : E, (⟪x, c⟫ : ℝ) ^ 2 = r ^ 2 * (⟪x, a⟫ : ℝ) ^ 2 := fun x => by
      rw [hc1 x]; ring
    simp_rw [h1]
    exact integral_const_mul _ _
  -- the two estimates
  have hone : ‖charFun (F.map Z) c - 1‖
      ≤ 3 / 2 * (r ^ 2 * ∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) := by
    have h := norm_charFun_sub_one_le (F.map Z) hac hac2 hmeanc
    rwa [hvarc] at h
  have hpow := norm_pow_sub_pow_succ_le (norm_charFun_le_one (μ := F.map Z) c) m
  have hroot : charFun (vecRootLaw F Z (m + 1)) a = charFun (F.map Z) c ^ (m + 1) := by
    rw [charFun_vecRootLaw F hZ, ← hrdef, ← hcdef]
  rw [hroot]
  calc ‖charFun (F.map Z) c ^ m - charFun (F.map Z) c ^ (m + 1)‖
      ≤ ‖1 - charFun (F.map Z) c‖ := hpow
    _ = ‖charFun (F.map Z) c - 1‖ := norm_sub_rev _ _
    _ ≤ 3 / 2 * (r ^ 2 * ∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) := hone
    _ = 3 / 2 * ((∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) / ((m : ℝ) + 1)) := by
        rw [hrsq]; ring

/-- **(M1)(b), with the one-factor bookkeeping done: the mixed characteristic function of a
vector root against the characteristic function of that same root.**

`‖mix_{ρ_n}(b,a) − i κ φ_{ρ_n}(a)‖ ≤ 3M/(2√n) + (3/2)|κ| v/n`, with `κ = ∫⟪x,b⟫⟪x,a⟫`,
`M = ∫|⟪x,b⟫|⟪x,a⟫²` and `v = ∫⟪x,a⟫²`, for a law centred in the directions `a` and `b`.

This is the form the studentized route consumes: the right-hand factor is now
`φ_{ρ_n}(a) = charFun (vecRootLaw F Z n) a` itself, so the damped expansion
`norm_charFun_vecRootLaw_sub_edgeworth_le` — which estimates exactly that quantity — applies to
it verbatim, and the two expansions can be added. The extra cost `(3/2)|κ|v/n` is `O(n^{-1})`,
invisible at the accuracy of a one-term expansion. -/
theorem norm_mixCharFun_vecRootLaw_sub_charFun_le (F : Measure ℝ) [IsProbabilityMeasure F]
    {Z : ℝ → E} (hZ : Measurable Z) {a b : E} (m : ℕ)
    (hb : Integrable (fun x : E => (⟪x, b⟫ : ℝ)) (F.map Z))
    (ha : Integrable (fun x : E => (⟪x, a⟫ : ℝ)) (F.map Z))
    (ha2 : Integrable (fun x : E => (⟪x, a⟫ : ℝ) ^ 2) (F.map Z))
    (hba : Integrable (fun x : E => (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ)) (F.map Z))
    (hba2 : Integrable (fun x : E => |(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) (F.map Z))
    (hmeanb : ∫ x, (⟪x, b⟫ : ℝ) ∂(F.map Z) = 0)
    (hmeana : ∫ x, (⟪x, a⟫ : ℝ) ∂(F.map Z) = 0) :
    ‖mixCharFun (vecRootLaw F Z (m + 1)) b a
        - Complex.I * ((∫ x, (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z) : ℝ) : ℂ)
            * charFun (vecRootLaw F Z (m + 1)) a‖
      ≤ 3 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))
            * ∫ x, |(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)
          + 3 / 2 * ((∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) / ((m : ℝ) + 1))
              * |∫ x, (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z)| := by
  haveI : IsProbabilityMeasure (F.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  set κ : ℝ := ∫ x, (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z) with hκdef
  set c : E := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • a with hcdef
  have h1 := norm_mixCharFun_vecRootLaw_sub_le F hZ m hb hba hba2 hmeanb
  rw [← hκdef, ← hcdef] at h1
  have h2 := norm_charFun_pow_sub_charFun_vecRootLaw_le F hZ m ha ha2 hmeana
  rw [← hcdef] at h2
  have hsplit : mixCharFun (vecRootLaw F Z (m + 1)) b a
        - Complex.I * (κ : ℂ) * charFun (vecRootLaw F Z (m + 1)) a
      = (mixCharFun (vecRootLaw F Z (m + 1)) b a
          - Complex.I * (κ : ℂ) * charFun (F.map Z) c ^ m)
        + Complex.I * (κ : ℂ)
            * (charFun (F.map Z) c ^ m - charFun (vecRootLaw F Z (m + 1)) a) := by
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hsecond : ‖Complex.I * (κ : ℂ)
      * (charFun (F.map Z) c ^ m - charFun (vecRootLaw F Z (m + 1)) a)‖
      ≤ 3 / 2 * ((∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) / ((m : ℝ) + 1)) * |κ| := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  linarith

/-- **The Cramér tail transfers to a vector root for free.**

If `‖φ_{F∘Z⁻¹}(t)‖ ≤ c` on the whole region `ε ≤ ‖t‖`, then `‖φ_{ρ_n}(t)‖ ≤ cⁿ` on the region
`ε√n ≤ ‖t‖`. This is `charFun_vecRootLaw` and nothing else: the law of the vector root *is* a
normalised sum, so its characteristic function *is* an `n`-th power, and the rescaling by
`n^{-1/2}` converts the region `ε ≤ ‖·‖` into `ε√n ≤ ‖·‖`.

It is the exact analogue, for the bivariate law, of what `edgeworthGap_tail_le` does for the
centred root, and it shows that **no conditioning device is needed at the level of `ρ_n`**: the
transfer that wave 13 attributed to Hall's trick of conditioning on `n − k` of the coordinates
is free here. Conditioning would be needed only for the law of a *nonlinear* functional of the
root, which the (M1)(b) route never forms. -/
theorem norm_charFun_vecRootLaw_le_pow (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) {c ε : ℝ} (hε : 0 < ε)
    (hc : ∀ t : E, ε ≤ ‖t‖ → ‖charFun (F.map Z) t‖ ≤ c)
    {n : ℕ} (hn : 0 < n) {t : E} (ht : ε * Real.sqrt (n : ℝ) ≤ ‖t‖) :
    ‖charFun (vecRootLaw F Z n) t‖ ≤ c ^ n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hscale : ‖((Real.sqrt (n : ℝ))⁻¹ : ℝ) • t‖ = ‖t‖ / Real.sqrt (n : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hsn, inv_mul_eq_div]
  have hge : ε ≤ ‖((Real.sqrt (n : ℝ))⁻¹ : ℝ) • t‖ := by
    rw [hscale, le_div_iff₀ hsn]
    linarith
  rw [charFun_vecRootLaw F hZ, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hc _ hge) n

end OneFactor

end StatLean.HypothesisTesting
