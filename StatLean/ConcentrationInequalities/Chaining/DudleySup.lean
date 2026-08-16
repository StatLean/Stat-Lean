import StatLean.ConcentrationInequalities.Chaining.Dudley
import StatLean.ConcentrationInequalities.Chaining.CountableSupLift
import StatLean.ConcentrationInequalities.Chaining.SeparableProcess

/-!
# Dudley's inequality with a genuine supremum over the index set

Honest `sup_{t ∈ T}` forms of Dudley's integral inequality
(Theorem 8.1.3 / Eqs. (8.13), (8.14), (8.16)) over an arbitrary — possibly
uncountable — metric-space index set `T`, in three grades:

* `*_countable_subset` — the cores: supremum over a countable `C ⊆ T`,
  entropy of the FULL `T` (so no subset-covering constant loss), via the
  `CountableSupLift` engines fed by the per-finite-subset theorems;
* `*_countable` — `C := T` displays for countable `T`;
* `*_separable` — supremum over `T` itself under
  `hsep : IsSeparableProcess X T μ`, via the value-closure transports.

Carriers: mean-zero content is stated in the **anchored** form
`ENNReal.ofReal (X t ω − X t₀ ω)` with `t₀ ∈ T` (the family contains `0`,
so neither the `Real.sSup` junk nor the positive-part inflation can fire;
a bare `⨆ t ∈ T, X t ω` mean-zero statement is FALSE already at `|T| = 1`);
under `hmean`, `E sup_{t∈T} X_t = E sup_{t∈T} (X_t − X_{t₀})`, so the
anchored form IS Theorem 8.1.3. Absolute forms use
`ENNReal.ofReal |X t ω − X t₀ ω|` (Eq. (8.13)) and the pair double-sup
(Eq. (8.14)). Real Bochner displays carry the `≠ ⊤` junk-guard `hDL`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Theorem 8.1.3, Eqs. (8.13), (8.14),
(8.16); the uncountable forms realize the p. 227 footnote ("the general
case typically follows by approximation") through separable versions
(`Chaining/SeparableProcess.lean`).

**Proof formalization notes.** Frozen constants unchanged from the
per-finite-subset family: `12√3` (anchored/mean-zero), `40` (absolute),
`80 = 2 × 40` (pair, triangle through the anchor). The cores measure the
entropy of `T` directly (`F ⊆ C ⊆ T` composes into `dudley_inequality*`),
so the historical `ε/2` subset-covering loss does not reappear. The anchor
`t₀` is required in `T`, NOT in `C` — separable assemblies instantiate
`C := insert t₀ T₀` against the witness `T₀` of `hsep`, and all transports
run pointwise under `filter_upwards` (the shape `φ` captures `X t₀ ω`).
The published `dudley_inequality_countable` (pairwise-distance cap, fused
`ENNReal.ofReal (40 * K)` constant) is unchanged; the forms here
standardize on `Metric.diam T ≤ D` and the per-`F` constant shape
`ENNReal.ofReal 40 * ↑K`. Named-sorry fallback of this work item:
`dudley_inequality_abs_pair_separable` (the pair transport composition).

**Bibliographic comments.** R. M. Dudley, *J. Funct. Anal.* 1 (1967),
290–330; separable versions per J. L. Doob, *Stochastic Processes*, Wiley
1953, Ch. II, and R. van Handel, *Probability in High Dimension*, §5.3.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **Dudley's inequality, anchored mean-zero form, per finite subset**
(HDP §8.1, Theorem 8.1.3 + Eq. (8.16)): for a finite `F ⊆ T` containing the
anchor, `E max_{t∈F} (X_t − X_{t₀}) ≤ 12√3 · K · ∫₀^D √(log 𝒩(T,d,ε)) dε`
in `ℝ≥0∞`. Under `hmean` the anchor's mean cancels, so this equals
`E max_{t∈F} X_t` — the Remark 7.2.1 finite stage of the anchored supremum
forms below. Constant `12√3` as in `dudley_inequality`. -/
theorem dudley_inequality_anchored {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
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
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the cap dominates the diameter (Eq (8.16)); HDP §8.1
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- USER-INPUT: the anchor point, inside the subset; HDP §8.1
    {t₀ : E} (ht₀F : t₀ ∈ F) :
    ENNReal.ofReal (∫ ω, F.sup' ⟨t₀, ht₀F⟩ (fun t => X t ω - X t₀ ω) ∂μ)
      ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K * dudleyLIntegral T D := by
  sorry

/-- **Dudley's inequality, absolute form, countable-subset supremum core**
(HDP §8.1, Eq. (8.13)): `∫⁻ sup_{t∈C} |X_t − X_{t₀}| ≤ 40·K·∫₀^D √log 𝒩(T)`
for any countable `C ⊆ T`, entropy of the FULL `T`. The engine stage of the
countable and separable displays. -/
theorem dudley_inequality_abs_countable_subset {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 40 * K * dudleyLIntegral T D := by
  sorry

/-- **Dudley's inequality, anchored mean-zero form, countable-subset
supremum core** (HDP §8.1, Theorem 8.1.3 + Eq. (8.16)):
`∫⁻ sup_{t∈C} (X_t − X_{t₀})⁺ ≤ 12√3·K·∫₀^D √log 𝒩(T)` for countable
`C ⊆ T`. The anchor is required in `T`, not in `C`. -/
theorem dudley_inequality_anchored_countable_subset {X : E → Ω → ℝ}
    {K : ℝ≥0} {T : Set E}
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
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter (Eq (8.16)); HDP §8.1
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K * dudleyLIntegral T D := by
  sorry

/-- **Dudley's inequality, absolute form, separable supremum** (HDP §8.1,
Eq. (8.13), general `T`): for a separable version of the process,
`∫⁻ sup_{t∈T} |X_t − X_{t₀}| ≤ 40·K·∫₀^D √(log 𝒩(T,d,ε)) dε` in `ℝ≥0∞`,
NO mean-zero. `T` may be uncountable; `hsep` is the version-selection input
this requires (see `IsSeparableProcess`). Constant `40` as in
`dudley_inequality_abs`; cf. the published countable form
`dudley_inequality_countable` (pairwise cap, fused constant shape). -/
theorem dudley_inequality_abs_separable {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 40 * K * dudleyLIntegral T D := by
  sorry

/-- **Dudley's integral inequality, separable supremum** (HDP §8.1,
Theorem 8.1.3 + Eq. (8.16), general `T`): for a separable version of a
mean-zero process,
`∫⁻ sup_{t∈T} (X_t − X_{t₀})⁺ ≤ 12√3·K·∫₀^D √(log 𝒩(T,d,ε)) dε` in
`ℝ≥0∞`. Under `hmean`, `E sup_{t∈T} X_t = E sup_{t∈T} (X_t − X_{t₀})` and
the anchored family contains `0`, so this is the junk-free rendering of
Theorem 8.1.3 (the bare `⨆ t ∈ T, X t ω` form is FALSE at `|T| = 1`).
Constant `12√3` as in `dudley_inequality`. -/
theorem dudley_inequality_anchored_separable {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter (Eq (8.16)); HDP §8.1
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K * dudleyLIntegral T D := by
  sorry

/-- **Dudley's inequality, absolute form, countable supremum**
(HDP §8.1, Eq. (8.13)): the `C := T` display of the countable-subset core,
with the diameter-shaped cap (cf. `dudley_inequality_countable`, the
published pairwise-cap twin). -/
theorem dudley_inequality_abs_countable {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 40 * K * dudleyLIntegral T D := by
  sorry

/-- **Dudley's integral inequality, anchored mean-zero form, countable
supremum** (HDP §8.1, Theorem 8.1.3 + Eq. (8.16)): the `C := T` display of
the anchored countable-subset core. -/
theorem dudley_inequality_anchored_countable {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter (Eq (8.16)); HDP §8.1
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K * dudleyLIntegral T D := by
  sorry

/-- **Dudley's inequality, absolute form, separable supremum, real display**
(HDP §8.1, Eq. (8.13)): under the finite-entropy junk-guard,
`∫ sup_{t∈T} |X_t − X_{t₀}| ≤ 40·K·(∫₀^D √log 𝒩)` as real numbers. The
supremum is a.e. finite and a.e. measurable under `hsep`, so the Bochner
integral is honest. -/
theorem dudley_inequality_abs_separable_real {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- LEAN-ONLY: finite entropy integral (real-display junk-guard)
    {D : ℝ} (hDL : dudleyLIntegral T D ≠ ⊤)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 40 * K * (dudleyLIntegral T D).toReal := by
  sorry

/-- **Dudley's inequality, absolute form, countable supremum, real display**
(HDP §8.1, Eq. (8.13)): the countable-`T` real display under the
finite-entropy junk-guard. -/
theorem dudley_inequality_abs_countable_real {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- LEAN-ONLY: finite entropy integral (real-display junk-guard)
    {D : ℝ} (hDL : dudleyLIntegral T D ≠ ⊤)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 40 * K * (dudleyLIntegral T D).toReal := by
  sorry

/-- **Theorem 8.1.3, `∫₀^∞` display, separable supremum** (HDP §8.1): the
uncapped entropy integral form of the anchored mean-zero separable
supremum. The cap `D := diam T + 1` is instantiated internally (a divergent
integral makes the RHS an honest `⊤`). -/
theorem dudley_inequality_anchored_separable_Ioi {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K
          * ∫⁻ ε in Set.Ioi (0 : ℝ), ENNReal.ofReal (sqrtLogCov T ε) := by
  sorry

/-- **Dudley's inequality, pair form, countable-subset supremum core**
(HDP §8.1, Eq. (8.14)): the two-sided oscillation over a countable `C ⊆ T`,
`∫⁻ sup_{t,s∈C} |X_t − X_s| ≤ 80·K·∫₀^D √log 𝒩(T)`. Constant `80 = 2 × 40`
by the triangle inequality through an anchor. -/
theorem dudley_inequality_abs_pair_countable_subset {X : E → Ω → ℝ}
    {K : ℝ≥0} {T : Set E}
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
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ⨆ s ∈ C, ENNReal.ofReal |X t ω - X s ω| ∂μ
      ≤ ENNReal.ofReal 80 * K * dudleyLIntegral T D := by
  sorry

/-- **Dudley's inequality, pair form, separable supremum** (HDP §8.1,
Eq. (8.14), general `T`): `∫⁻ sup_{t,s∈T} |X_t − X_s| ≤ 80·K·∫₀^D √log 𝒩`
in `ℝ≥0∞` for a separable version of the process. Constant `80` as in
`dudley_inequality_abs_pair`. -/
theorem dudley_inequality_abs_pair_separable {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ⨆ s ∈ T, ENNReal.ofReal |X t ω - X s ω| ∂μ
      ≤ ENNReal.ofReal 80 * K * dudleyLIntegral T D := by
  sorry

end StatLean.ConcentrationInequalities
