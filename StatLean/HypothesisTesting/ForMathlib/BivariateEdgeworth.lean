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

end Mixed

end StatLean.HypothesisTesting
