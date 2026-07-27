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
private lemma measurable_vecRoot {Z : ℝ → E} (hZ : Measurable Z) (n : ℕ) :
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

end VecRoot

end StatLean.HypothesisTesting
