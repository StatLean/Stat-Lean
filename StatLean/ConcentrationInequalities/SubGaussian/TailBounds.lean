import StatLean.ConcentrationInequalities.SubGaussian.Defs

/-!
# Sub-Gaussian tail bounds — Lu-BDA §2.2 (`thm:two-sided`)

We formalize Lu, *Big Data Analysis* §2.2 "Two-Sided Tail Probability":

* `IsSubGaussian.measure_sub_integral_lt_le` — one-sided Chernoff tail
  `μ {t < X − ∫ X dμ} ≤ exp(−t² / (2σ²))` (the right-tail step used in the
  book's proof of the two-sided form).
* `IsSubGaussian.measure_abs_sub_integral_lt_le` — the book theorem
  `μ {t < |X − ∫ X dμ|} ≤ 2 · exp(−t² / (2σ²))`.

Both consume `IsSubGaussian X σ² μ` from
`StatLean/ConcentrationInequalities/SubGaussian/Defs.lean` and reduce to
Mathlib's `ProbabilityTheory.HasSubgaussianMGF.measure_ge_le` applied to the
centered variable `X − ∫ X dμ`, and (for the left tail) to its negation via
`ProbabilityTheory.HasSubgaussianMGF.neg`. The book uses strict `>`; we mirror
that with `μ {ω | t < ·}`, packaging the right-hand side as `ENNReal.ofReal`
to bridge from Mathlib's `μ.real`-form bound to the ENNReal-valued measure.

No `IsFiniteMeasure μ` typeclass is assumed at the user surface: the
`HasSubgaussianMGF` predicate embedded in `IsSubGaussian` already forces it,
since integrability of `exp(0 · (X − ∫ X dμ)) = 1` is equivalent to
`IsFiniteMeasure μ`. We derive it as a private lemma and use it internally to
obtain `μ S ≠ ∞` for the `μ.real → μ` conversion.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `IsSubGaussian` forces the underlying measure to be finite: the
integrability of `exp(0 · (X − ∫ X dμ)) = 1` packaged inside
`HasSubgaussianMGF` is equivalent to `IsFiniteMeasure μ`. -/
private lemma IsSubGaussian.isFiniteMeasure
    {X : Ω → ℝ} {σ2 : ℝ≥0} {μ : Measure Ω} (hX : IsSubGaussian X σ2 μ) :
    IsFiniteMeasure μ := by
  have h := (isSubGaussian_iff.mp hX).integrable_exp_mul 0
  simp only [zero_mul, Real.exp_zero] at h
  exact (integrable_const_iff_isFiniteMeasure (one_ne_zero)).mp h

/-- **One-sided sub-Gaussian Chernoff tail** (Lu-BDA §2.2, the right-tail step
used inside the proof of `thm:two-sided`).

If `X` is sub-Gaussian with variance proxy `σ²` under `μ`, then for `0 ≤ t`,
`μ {ω | t < X ω − ∫ X dμ} ≤ exp(−t² / (2σ²))`.

Deviation from the book: Lu states the bound for `t > 0`; we use the weaker
`0 ≤ t` to match Mathlib's `HasSubgaussianMGF.measure_ge_le`, yielding a
strictly stronger statement (the `t = 0` case is trivial). The strict
inequality `<` on the event is faithful to the book; the brick gives `≤`, and
the slack is absorbed via the inclusion `{t < y} ⊆ {t ≤ y}`. -/
theorem IsSubGaussian.measure_sub_integral_lt_le
    {X : Ω → ℝ} {σ2 : ℝ≥0} {μ : Measure Ω}
    (hX : IsSubGaussian X σ2 μ)
    -- USER-INPUT: 0 ≤ t (book: t > 0); Lu-BDA §2.2 (thm:two-sided)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < X ω - ∫ x, X x ∂μ}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * σ2))) := by
  haveI := hX.isFiniteMeasure
  have hsg : HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂μ) σ2 μ :=
    isSubGaussian_iff.mp hX
  have hbrick :
      μ.real {ω | t ≤ X ω - ∫ x, X x ∂μ} ≤ Real.exp (-t ^ 2 / (2 * σ2)) :=
    hsg.measure_ge_le ht
  have hsub : {ω | t < X ω - ∫ x, X x ∂μ}
      ⊆ {ω | t ≤ X ω - ∫ x, X x ∂μ} := by
    intro ω hω
    have hω' : t < X ω - ∫ x, X x ∂μ := hω
    exact hω'.le
  calc μ {ω | t < X ω - ∫ x, X x ∂μ}
      ≤ μ {ω | t ≤ X ω - ∫ x, X x ∂μ} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * σ2))) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal hbrick

/-- **Two-Sided Tail Probability** for sub-Gaussian variables
(Lu-BDA §2.2, `thm:two-sided`).

If `X` is sub-Gaussian with variance proxy `σ²` under `μ`, then for `0 ≤ t`,
`μ {ω | t < |X ω − ∫ X dμ|} ≤ 2 · exp(−t² / (2σ²))`.

Proof (book): `t < |Y|` decomposes as `t < Y ∨ t < −Y` (`lt_abs`); apply the
one-sided Chernoff bound `HasSubgaussianMGF.measure_ge_le` to `Y := X − ∫ X dμ`
for the right tail and to `-Y` (via `HasSubgaussianMGF.neg`) for the left
tail; combine with `measure_union_le`.

Deviation from the book: Lu states the bound for `t > 0`; we use the weaker
`0 ≤ t` to match Mathlib's brick. -/
theorem IsSubGaussian.measure_abs_sub_integral_lt_le
    {X : Ω → ℝ} {σ2 : ℝ≥0} {μ : Measure Ω}
    (hX : IsSubGaussian X σ2 μ)
    -- USER-INPUT: 0 ≤ t (book: t > 0); Lu-BDA §2.2 (thm:two-sided)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < |X ω - ∫ x, X x ∂μ|}
      ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ2))) := by
  haveI := hX.isFiniteMeasure
  have hsg : HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂μ) σ2 μ :=
    isSubGaussian_iff.mp hX
  have hbrickR :
      μ.real {ω | t ≤ X ω - ∫ x, X x ∂μ} ≤ Real.exp (-t ^ 2 / (2 * σ2)) :=
    hsg.measure_ge_le ht
  have hbrickL :
      μ.real {ω | t ≤ -(X ω - ∫ x, X x ∂μ)} ≤ Real.exp (-t ^ 2 / (2 * σ2)) := by
    have h := hsg.neg.measure_ge_le ht
    simpa [Pi.neg_apply] using h
  have hR : μ {ω | t ≤ X ω - ∫ x, X x ∂μ}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * σ2))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hbrickR
  have hL : μ {ω | t ≤ -(X ω - ∫ x, X x ∂μ)}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * σ2))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hbrickL
  have hexp_nn : 0 ≤ Real.exp (-t ^ 2 / (2 * σ2)) := (Real.exp_pos _).le
  have hsub : {ω | t < |X ω - ∫ x, X x ∂μ|}
      ⊆ {ω | t ≤ X ω - ∫ x, X x ∂μ} ∪ {ω | t ≤ -(X ω - ∫ x, X x ∂μ)} := by
    intro ω hω
    have hω' : t < |X ω - ∫ x, X x ∂μ| := hω
    rcases lt_abs.mp hω' with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  calc μ {ω | t < |X ω - ∫ x, X x ∂μ|}
      ≤ μ ({ω | t ≤ X ω - ∫ x, X x ∂μ}
            ∪ {ω | t ≤ -(X ω - ∫ x, X x ∂μ)}) := measure_mono hsub
    _ ≤ μ {ω | t ≤ X ω - ∫ x, X x ∂μ}
          + μ {ω | t ≤ -(X ω - ∫ x, X x ∂μ)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * σ2)))
          + ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * σ2))) := add_le_add hR hL
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * σ2))) := by
        rw [← ENNReal.ofReal_add hexp_nn hexp_nn]
        ring_nf

end StatLean.ConcentrationInequalities
