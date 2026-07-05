import StatLean.ConcentrationInequalities.Chaining.DiscreteDudley

/-!
# Dudley's integral inequality (Theorem 8.1.3 / Eqs. (8.13)–(8.16))

Integral-form Dudley from the discrete core via the comparison
$\Sigma \le 2 I$: for a process with sub-gaussian increments on a finite
index set $T$ with $\operatorname{diam} T \le D$,
$$ \mathbb{E}\Bigl[\sup_{t \in T} X_t\Bigr] \;\le\;
     12\sqrt{3}\; K \int_0^{D} \sqrt{\log \mathcal{N}(T,d,\varepsilon)}\,
     d\varepsilon \quad (\text{mean-zero}), $$
$$ \mathbb{E}\Bigl[\sup_{t \in T} |X_t - X_{t_0}|\Bigr]
     \le 40\, K \int_0^{D}\!\sqrt{\log \mathcal{N}}, \qquad
   \mathbb{E}\Bigl[\sup_{s,t \in T} |X_t - X_s|\Bigr]
     \le 80\, K \int_0^{D}\!\sqrt{\log \mathcal{N}}, $$
plus the $\int_0^\infty$ display of Theorem 8.1.3 and the ONE countable lift
mandated by the sup policy. Assembly file.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Theorem 8.1.3, Eqs. (8.13), (8.14), and
Eq. (8.16) / Remark 8.1.7; the countable form realizes the p. 227 footnote
("the general case follows by approximation").

**Proof formalization notes.** Frozen constants: `12√3 = 2 × 6√3` (mean-zero,
via `dudleySum_le_two_mul_dudleyIntegral`), `40 = 2 × 20` (abs form),
`80 = 2 × 40` (pair form, triangle through a fixed `t₀`), countable lift
`80 = 40 × 2` (the `coveringNumber_subset_le` `ε/2` loss after the `u = ε/2`
change of variables). The diameter-capped Eq. (8.16) is the PRIMARY
statement; the `∫_0^∞` shape of Theorem 8.1.3 is a display corollary via
`dudleyIntegral_Ioi_eq` (the `diam = 0` corner handled separately). The
mean-zero forms carry the LEAN-ONLY hypothesis
`hint : ∀ t ∈ T, Integrable (X t) μ` ruling out Bochner-junk means. The
countable lift is stated wholly in `ℝ≥0∞` (`∫⁻` of
`⨆ ENNReal.ofReal |X_t − X_{t₀}|` against `dudleyLIntegral`) so neither side
can be junk; it goes by monotone convergence (`lintegral_iSup`) over a finite
exhaustion `S_n ↑ T`, with the subset step costing exactly the factor `2`
above. Uncountable-sup statements are left to consumers per the sup policy
(ℚ-grid + right-continuity for Glivenko–Cantelli; `L^∞`-dense subfamilies for
Lipschitz classes). Named-sorry fallback of this work item:
`dudley_inequality_countable` (all finite-`T` integral forms proved; the
MCT/change-of-variables lift is the isolated hard part).

**Bibliographic comments.** R. M. Dudley, "The sizes of compact subsets of
Hilbert space and continuity of Gaussian processes," *J. Funct. Anal.* 1
(1967), 290–330. The entropy-integral formulation for sub-gaussian processes
is the standard textbook synthesis (HDP §8.1; Talagrand 2014, §2.3;
Ledoux–Talagrand, *Probability in Banach Spaces*, Springer 1991, Ch. 11).
See the HDP Chapter 8 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **Dudley's inequality, mean-zero capped form** (HDP §8.1, Theorem 8.1.3
+ Eq. (8.16)): `E sup X ≤ 12√3 · K · ∫_0^D √(log 𝒩)`. Book constant frozen
to `12√3 = 2 × 6√3`. -/
theorem dudley_inequality {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
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
    -- LEAN-ONLY: positive cap; the D = 0 corner degenerates to a point
    (hD0 : 0 < D) :
    ∫ ω, ⨆ t ∈ T, X t ω ∂μ
      ≤ 12 * Real.sqrt 3 * K * dudleyIntegral T D := by sorry

/-- **Dudley's inequality, absolute form** (HDP §8.1, Eq. (8.13), capped):
`E sup |X_t − X_{t₀}| ≤ 40 · K · ∫_0^D √(log 𝒩)`, NO mean-zero — THE
consumer-facing form. Book constant frozen to `40 = 2 × 20`. -/
theorem dudley_inequality_abs {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
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
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 40 * K * dudleyIntegral T D := by sorry

/-- **Dudley's inequality, pair form** (HDP §8.1, Eq. (8.14), capped):
`E sup_{s,t} |X_t − X_s| ≤ 80 · K · ∫_0^D √(log 𝒩)` via the triangle
inequality through a fixed `t₀`. Book constant frozen to `80 = 2 × 40`. -/
theorem dudley_inequality_abs_pair {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫ ω, ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω| ∂μ
      ≤ 80 * K * dudleyIntegral T D := by sorry

/-- **Dudley's inequality, `∫_0^∞` display** (HDP §8.1, Theorem 8.1.3
verbatim shape): via `dudleyIntegral_Ioi_eq`; the `diam = 0` corner is
handled separately in the proof. -/
theorem dudley_inequality_Ioi {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ) :
    ∫ ω, ⨆ t ∈ T, X t ω ∂μ
      ≤ 12 * Real.sqrt 3 * K * ∫ ε in Set.Ioi (0 : ℝ), sqrtLogCov T ε := by sorry

/-- **Dudley's inequality, countable lift** (HDP §8.1, Eq. (8.13), countable
form; p. 227 footnote "general case by approximation"): stated wholly in
`ℝ≥0∞` so neither side can be junk; monotone convergence over a finite
exhaustion + the `coveringNumber_subset_le` `ε/2` loss (frozen constant
`80 = 40 × 2`). -/
theorem dudley_inequality_countable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy (uncountable sups are left
    -- to consumers)
    (hcnt : T.Countable)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: T totally bounded, as finite covering numbers; HDP p.227
    -- footnote
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: uniform diameter bound (T bounded); HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : ∀ s ∈ T, ∀ t ∈ T, dist s t ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal (80 * K) * dudleyLIntegral T D := by sorry

end StatLean.ConcentrationInequalities
