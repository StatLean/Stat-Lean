import StatLean.ConcentrationInequalities.Chaining.Dudley

/-!
# Dudley plug-in corollaries — exponential entropy branch

Evaluated plug-in corollaries of Dudley's inequality for classes with
exponential-type entropy: if
$\mathcal{N}(T, d, \varepsilon) \le e^{C/\varepsilon}$ on $(0, D]$, then
$$ \int_0^{D} \sqrt{\log \mathcal{N}(T,d,\varepsilon)}\, d\varepsilon
     \;\le\; \int_0^{D} \sqrt{C/\varepsilon}\, d\varepsilon
     \;=\; 2\sqrt{C D}, $$
so a process with sub-gaussian increments satisfies
$\mathbb{E} \sup_{t} |X_t - X_{t_0}| \le 80\, K \sqrt{C D}$. This is the
shape consumed by the Lipschitz-class law of large numbers.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2 (application arithmetic; Exercise 8.9-
flavored entropy bound for Lipschitz classes) and the Exercise 8.9/8.10
pipeline.

**Proof formalization notes.** Per the batch's consumer-ownership rule, this
file keeps ONLY the exponential branch: the polynomial (`(2/ε)^m`, VC-type)
branch and its integral evaluation are OWNED by the VC cluster
(`VC/EntropyIntegral.lean`), which plugs `dudley_inequality_abs` (frozen
constant `40`) directly. The integral evaluation
`∫_0^D √(C/ε) dε = 2√(CD)` is exact (via `integral_rpow`), deliberately
avoiding the `Γ(3/2)` change-of-variables. Headline constant frozen to
`80·K·√(C·D)` (= `40` from `dudley_inequality_abs` × `2` from the integral
evaluation). The covering hypothesis shape
`hcov : ∀ ε ∈ Ioc 0 D, coveringNumber T ε ≠ ⊤ ∧ (toNat 𝒩 : ℝ) ≤ exp (C/ε)`
is frozen for the gaussian-lln cluster. Named-sorry fallback of this work
item: `integral_sqrt_div_le` (the `integral_rpow` arithmetic), with the two
corollary skeletons standing on it.

**Bibliographic comments.** Entropy bounds of order $e^{C/\varepsilon}$ for
Lipschitz function classes go back to Kolmogorov–Tikhomirov (1959, §2); the
plug-in route through Dudley's integral is the standard empirical-process
argument (Dudley 1967; van der Vaart–Wellner 1996, §2.7). See the HDP
Chapter 8 Notes.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- Exact evaluation `∫_0^D √(C/ε) dε = 2√(CD)`, stated as an inequality
(via `integral_rpow` on `ε^{-1/2}`). -/
lemma integral_sqrt_div_le {C D : ℝ}
    -- LEAN-ONLY: nonnegative entropy constant
    (hC : 0 ≤ C)
    -- LEAN-ONLY: positive cap
    (hD : 0 < D) :
    ∫ ε in Set.Ioc (0 : ℝ) D, Real.sqrt (C / ε)
      ≤ 2 * Real.sqrt (C * D) := by sorry

/-- **Entropy-integral evaluation, exponential branch** (HDP §8.2 /
Exercise 8.9 shape): `𝒩 ≤ e^{C/ε}` on `(0, D]` gives
`dudleyIntegral T D ≤ 2√(CD)`. -/
theorem dudleyIntegral_le_of_cov_le_exp_div {T : Set E}
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {C D : ℝ}
    -- LEAN-ONLY: nonnegative entropy constant
    (hC : 0 ≤ C)
    -- LEAN-ONLY: positive cap
    (hD : 0 < D)
    -- USER-INPUT: Lipschitz-type entropy bound 𝒩 ≤ e^{C/ε} with finite
    -- covering numbers; HDP §8.2 / Exercise 8.9
    (hcov : ∀ ε ∈ Set.Ioc (0 : ℝ) D, coveringNumber T ε ≠ ⊤ ∧
      ((coveringNumber T ε).toNat : ℝ) ≤ Real.exp (C / ε)) :
    dudleyIntegral T D ≤ 2 * Real.sqrt (C * D) := by sorry

/-- **Dudley plug-in, exponential branch** (HDP §8.2, Exercise 8.9/8.10
pipeline): sub-gaussian increments + entropy `𝒩 ≤ e^{C/ε}` give the fully
evaluated bound `E sup |X_t − X_{t₀}| ≤ 80·K·√(CD)`. Frozen headline
constant `80 = 40 × 2`. -/
theorem dudley_abs_of_cov_le_exp_div {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
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
    {t₀ : E} (ht₀ : t₀ ∈ T) {C D : ℝ}
    -- LEAN-ONLY: nonnegative entropy constant
    (hC : 0 ≤ C)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hdiam : Metric.diam T ≤ D)
    -- USER-INPUT: Lipschitz-type entropy bound 𝒩 ≤ e^{C/ε}; HDP §8.2 /
    -- Exercise 8.9
    (hcov : ∀ ε ∈ Set.Ioc (0 : ℝ) D, coveringNumber T ε ≠ ⊤ ∧
      ((coveringNumber T ε).toNat : ℝ) ≤ Real.exp (C / ε)) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 80 * K * Real.sqrt (C * D) := by sorry

end StatLean.ConcentrationInequalities
