import StatLean.ConcentrationInequalities.Chaining.DiscreteDudley
import StatLean.ConcentrationInequalities.Chaining.CountableSupLift
import StatLean.ConcentrationInequalities.Chaining.SeparableProcess

/-!
# Discrete Dudley inequality with a genuine supremum

Honest `sup_{t ∈ T}` forms of the discrete Dudley inequality
(HDP Theorem 8.1.4, Eq. (8.2), and its absolute Remark 8.1.5 twin) over an
arbitrary — possibly uncountable — index set, against the dyadic entropy
series `dudleyLSum T`: the per-finite-subset anchored form, countable-subset
cores, countable displays, and separable-supremum forms. Companion of
`Chaining/DudleySup.lean` (integral RHS) at the series RHS; constants `6√3`
(anchored/mean-zero) and `20` (absolute) frozen as in `discrete_dudley` /
`discrete_dudley_abs`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Theorem 8.1.4, Eq. (8.2), Remark 8.1.5;
uncountable forms per the p. 227 footnote through separable versions
(`Chaining/SeparableProcess.lean`).

**Proof formalization notes.** Same engine recipe as `DudleySup.lean` with
`discrete_dudley` / `discrete_dudley_abs` as the per-finite-subset inputs
and `dudleyLSum T` as the `ℝ≥0∞` carrier (divergent series = honest `⊤`).
The anchored family contains `0` (anchor in the subset / `t₀ ∈ T`), so the
`ENNReal.ofReal` carrier is junk-free; a bare mean-zero `⨆ t ∈ T, X t ω`
statement would be FALSE at `|T| = 1`. Named-sorry fallback of this work
item: `discrete_dudley_anchored` (the sup'-shift algebra).

**Bibliographic comments.** R. M. Dudley, *J. Funct. Anal.* 1 (1967),
290–330; the dyadic-series form is HDP's Theorem 8.1.4 route to the
entropy integral.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **Discrete Dudley inequality, anchored mean-zero form, per finite
subset** (HDP §8.1, Theorem 8.1.4, Eq. (8.2)): for a finite `F ⊆ T`
containing the anchor,
`E max_{t∈F} (X_t − X_{t₀}) ≤ 6√3 · K · dudleyLSum T` in `ℝ≥0∞`. Under
`hmean` the anchor's mean cancels, so this equals `E max_{t∈F} X_t`.
Constant `6√3` as in `discrete_dudley`. -/
theorem discrete_dudley_anchored {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- USER-INPUT: the anchor point, inside the subset; HDP §8.1
    {t₀ : E} (ht₀F : t₀ ∈ F) :
    ENNReal.ofReal (∫ ω, F.sup' ⟨t₀, ht₀F⟩ (fun t => X t ω - X t₀ ω) ∂μ)
      ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * dudleyLSum T := by
  sorry

/-- **Discrete Dudley inequality, absolute form, countable-subset supremum
core** (HDP §8.1, Remark 8.1.5 discrete):
`∫⁻ sup_{t∈C} |X_t − X_{t₀}| ≤ 20·K·dudleyLSum T` for any countable
`C ⊆ T`, entropy of the FULL `T`. -/
theorem discrete_dudley_abs_countable_subset {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Remark 8.1.5
    {t₀ : E} (ht₀ : t₀ ∈ T)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 20 * K * dudleyLSum T := by
  sorry

/-- **Discrete Dudley inequality, anchored mean-zero form, countable-subset
supremum core** (HDP §8.1, Theorem 8.1.4):
`∫⁻ sup_{t∈C} (X_t − X_{t₀})⁺ ≤ 6√3·K·dudleyLSum T` for countable `C ⊆ T`;
the anchor is required in `T`, not in `C`. -/
theorem discrete_dudley_anchored_countable_subset {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * dudleyLSum T := by
  sorry

/-- **Discrete Dudley inequality, absolute form, separable supremum**
(HDP §8.1, Remark 8.1.5 discrete, general `T`):
`∫⁻ sup_{t∈T} |X_t − X_{t₀}| ≤ 20·K·dudleyLSum T` in `ℝ≥0∞` for a
separable version of the process. -/
theorem discrete_dudley_abs_separable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Remark 8.1.5
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 20 * K * dudleyLSum T := by
  sorry

/-- **Discrete Dudley inequality (Theorem 8.1.4), separable supremum**
(HDP §8.1, Eq. (8.2), general `T`): for a separable version of a mean-zero
process, `∫⁻ sup_{t∈T} (X_t − X_{t₀})⁺ ≤ 6√3·K·dudleyLSum T` in `ℝ≥0∞` —
the junk-free rendering of `E sup_{t∈T} X_t ≤ CK Σ_k 2^{−k}√log 𝒩`. -/
theorem discrete_dudley_anchored_separable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * dudleyLSum T := by
  sorry

/-- **Discrete Dudley inequality, absolute form, countable supremum**
(HDP §8.1, Remark 8.1.5 discrete): the `C := T` display of the
countable-subset core. -/
theorem discrete_dudley_abs_countable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Remark 8.1.5
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 20 * K * dudleyLSum T := by
  sorry

/-- **Discrete Dudley inequality (Theorem 8.1.4), countable supremum**
(HDP §8.1, Eq. (8.2)): the `C := T` display of the anchored
countable-subset core. -/
theorem discrete_dudley_anchored_countable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * dudleyLSum T := by
  sorry

end StatLean.ConcentrationInequalities
