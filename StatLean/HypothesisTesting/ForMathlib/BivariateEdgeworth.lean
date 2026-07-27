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

end StatLean.HypothesisTesting
