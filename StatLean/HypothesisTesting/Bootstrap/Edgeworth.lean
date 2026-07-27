import StatLean.HypothesisTesting.Bootstrap.NonparametricMean
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# One-term Edgeworth expansions for the mean, and their uniform form

Consistency says the bootstrap approximation is asymptotically correct; it says nothing about
how fast. The comparison of competing confidence intervals for a mean is decided at the next
order, and the tool is the Edgeworth expansion: the sampling distribution function of the root
differs from the normal approximation by an explicit term of order `n^{-1/2}` carrying the
skewness of the sampling law, plus a remainder of order `n^{-1}`. Two expansions are needed —
one for the centred root and one for the studentized root — and their `n^{-1/2}` terms differ,
which is the analytic reason the studentized (bootstrap-t) construction is preferable.

This file contains **statements only**:

* `skewness`, `stdNormalPDF`, `CramerCondition` — the carriers;
* `edgeworth_mean_uniform` — the expansion for the centred root, with a uniform `O(n^{-1})`
  remainder, under a finite fourth moment and Cramér's condition;
* `edgeworth_studentized_uniform` — the expansion for the studentized root, uniform in the
  argument, under a finite fourth moment and absolute continuity;
* `cornishFisher_studentized_quantile` — the attached expansion of the quantile function with
  its `O(n^{-1})` accuracy, uniform over levels bounded away from `0` and `1`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 18 (Bootstrap and
Subsampling Methods), §18.4 (Higher Order Asymptotic Comparisons), Theorems 18.4.1 and 18.4.2
(the one-term Edgeworth expansion for the studentized mean and its uniform form, giving the
`O(n⁻¹)` bootstrap accuracy). (`TSH4 §18.4 Thm 18.4.1, Thm 18.4.2`.)

**Proof formalization notes.**
* Cramér's condition `limsup_{|s| → ∞} |ψ_F(s)| < 1` is rendered as: some constant below `1`
  eventually dominates `‖charFun F s‖` along the cocompact filter on the line. This is
  equivalent to the limsup form and avoids introducing a limsup over an unbounded argument.
* The expansions are stated in their **uniform** form throughout — an explicit constant `C`
  depending on the sampling law, with the remainder bounded by `C / n` for every argument and
  every positive sample size. The uniform form implies the pointwise `O(n^{-1})` statements and
  is what the downstream coverage-error comparisons consume, so nothing is lost by stating only
  it.
* `n^{-1/2}` is written `(Real.sqrt n)⁻¹` rather than as a real power, to keep the statements
  inside the square-root API.
* The quantile expansion is the Cornish–Fisher inversion of the studentized expansion; it is
  stated as its own result because the coverage-error computations use the quantile form
  directly.

**Bibliographic comments.** Edgeworth expansions for the bootstrap and the resulting theory of
higher-order accuracy are due to K. Singh ("On the asymptotic accuracy of Efron's bootstrap,"
*Ann. Statist.* **9** (1981), 1187–1195) and are developed systematically in P. Hall, *The
Bootstrap and Edgeworth Expansion*, Springer, 1992. The bootstrap itself is due to B. Efron
("Bootstrap methods: another look at the jackknife," *Ann. Statist.* **7** (1979), 1–26), and
its first-order consistency theory to P. J. Bickel and D. A. Freedman ("Some asymptotic theory
for the bootstrap," *Ann. Statist.* **9** (1981), 1196–1217). Prepivoting, which uses these
expansions to improve accuracy, is due to R. Beran ("Bootstrap methods in statistics,"
*Jahresber. Deutsch. Math.-Verein.* **86** (1984), 14–30).
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace StatLean.HypothesisTesting

/-! ## Carriers -/

/-- The **standard normal density** `φ`. -/
noncomputable def stdNormalPDF (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi)

/-- The **skewness** of a law on the line: the third central moment divided by the cube of the
standard deviation. Returns `0` for a degenerate law by the junk convention on division. -/
noncomputable def skewness (F : Measure ℝ) : ℝ :=
  (∫ t, (t - ∫ s, s ∂F) ^ 3 ∂F) / Real.sqrt Var[fun t : ℝ => t; F] ^ 3

/-- **Cramér's condition** on a law on the line: the modulus of its characteristic function is
eventually bounded by a constant strictly below `1` at infinity. This is the standard
non-lattice requirement that makes a one-term Edgeworth expansion valid. -/
def CramerCondition (F : Measure ℝ) : Prop :=
  ∃ c : ℝ, c < 1 ∧ ∀ᶠ s in Filter.cocompact ℝ, ‖charFun F s‖ ≤ c

/-! ## The expansions -/

section Edgeworth

variable {F : Measure ℝ}

/-- **One-term Edgeworth expansion for the centred sample mean, uniform remainder.**

Under a finite fourth moment and Cramér's condition, the sampling distribution function of the
centred and scaled sample mean equals the normal approximation `Φ(t/σ)` corrected by the
skewness term `−(1/6) γ φ(t/σ) (t²/σ² − 1) n^{-1/2}`, with a remainder bounded by `C/n`
uniformly in the argument, for a constant `C` depending only on the sampling law.

DEFERRAL-ELIGIBLE (planned debt). The statement is correct as written (it is Hall (1992),
Thm 2.2 with `j = 1`: under `E X⁴ < ∞` and Cramér's condition the two-term expansion has
remainder `o(n⁻¹)`, so truncating after the `n^{-1/2}` term leaves `O(n⁻¹)`, and enlarging `C`
absorbs the finitely many small `n`). It is not proved here. See the status note at the head of
`ForMathlib/EsseenSmoothing.lean`: the analytic route needs (a) an expansion of `(charFun F)ⁿ`
to order `n⁻¹` valid on a Cramér window plus a tail estimate off it, and (b) a CDF-level
Lévy/Esseen inversion to turn that into a bound on the distribution function. Ingredient (b) is
the one gap that survives this session's work — the sinc integral, the Fejér normalisation and
the compactly supported Fejér/triangle Fourier pair are now proved
(`integral_sin_div_sq`, `integral_fejerKernel`, `fourier_tentC`, `fourier_sqSincC`), as is the
smoothing inequality in test-function form (`norm_integral_fourier_sub_le`).

**Re-derivation of the obstruction (attempted from the test-function form; which estimate
fails).** `norm_integral_fourier_sub_le` bounds `‖∫ 𝓕g dP − ∫ 𝓕g dQ‖` by
`∫ ‖φ_P(−2πξ) − φ_Q(−2πξ)‖ · ‖g ξ‖ dξ` for `g ∈ L¹`. Reaching `|F_P(x) − F_Q(x)|` would need
`𝓕g` to approximate `1_{(−∞, x]}`, which no `L¹` `g` does, so one must go through the smoothed
difference `Δ_T(x) := ((F_P − F_Q) ∗ K_T)(x)`. Two steps are then required.

* (E1) The **Stieltjes/Lévy inversion with the division by `t`**:
  `Δ_T(x) = (2π)⁻¹ ∫_{|t| ≤ T} ((φ_P t − φ_Q t) / (−i t)) e^{−i t x} (1 − |t|/T) dt`. This is
  *not* an instance of Mathlib's `Real.fourierIntegralInv` inversion: the integrand is integrable
  at `t = 0` only because of the cancellation `φ_P 0 = φ_Q 0 = 1`, and `F_P − F_Q` is not itself
  `L¹` without a prior `O(|x|⁻¹)` tail bound. Mathlib v4.29.1 has no Stieltjes-level inversion,
  and the tent/Fejér pair proved in `EsseenSmoothing` supplies the kernel but not this identity.
  **This is the estimate that fails.**
* (E2) The **de-smoothing** `sup |F_P − F_Q| ≤ 2 sup |Δ_T| + C · (sup density of the comparison
  law) / T`. This is the step that monotonicity of `F_P` plus the smoothed bound at a mesh of
  continuity points *does* deliver, and it is **not** the obstruction — but it consumes (E1) as
  its input, so it cannot be run first.

Even with (E1) in hand the two expansions need, in addition, the pointwise estimate
`(charFun F (t/(σ√n)))ⁿ = e^{−t²/2}(1 + (γ/6)(i t)³ n^{-1/2}) + O(t⁴/n)` on a window
`|t| ≤ c√n`, together with the Cramér tail `∫_{c√n ≤ |t| ≤ T_n} |·| dt = o(n⁻¹)` at `T_n ≍ n`;
neither is present at this pin, and `ForMathlib/BerryEsseen`'s
`norm_charFun_pow_sub_gaussian_le` gives only the leading (`Berry–Esseen`) order. -/
theorem edgeworth_mean_uniform [IsProbabilityMeasure F]
    -- USER-INPUT: finite fourth moment of the sampling law
    (hF4 : MemLp (fun t : ℝ => t) 4 F)
    -- USER-INPUT: nonzero variance, so the normalisation is meaningful
    (hFvar : 0 < Var[fun t : ℝ => t; F])
    -- USER-INPUT: Cramér's condition; the non-lattice requirement behind the expansion
    (hCramer : CramerCondition F) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ t : ℝ,
      |meanRootCDF F n t -
        (stdNormalCDF (t / Real.sqrt Var[fun t : ℝ => t; F]) -
          (1 / 6) * skewness F * stdNormalPDF (t / Real.sqrt Var[fun t : ℝ => t; F]) *
            (t ^ 2 / Var[fun t : ℝ => t; F] - 1) * (Real.sqrt n)⁻¹)|
      ≤ C / n := by
  sorry

/-- **One-term Edgeworth expansion for the studentized sample mean, uniform in the argument.**

Under a finite fourth moment and absolute continuity of the sampling law, the sampling
distribution function of the studentized sample mean equals the standard normal distribution
function corrected by `+(1/6) γ φ(t) (2t² + 1) n^{-1/2}`, with a remainder bounded by `C/n`
uniformly in the argument. The `n^{-1/2}` term differs from the one for the centred root — this
is where the advantage of studentizing is located — and vanishes exactly when the sampling law
is unskewed.

DEFERRAL-ELIGIBLE (planned debt). The statement is correct as written (TSH4 Thm 18.4.1; the
studentized root is a smooth function of the pair of means `(X̄, X̄₂)`, absolute continuity of
`F` supplies the joint Cramér condition, and `E X⁴ < ∞` gives the `O(n⁻¹)` remainder). It is
not proved here, and it is strictly harder than `edgeworth_mean_uniform`: beyond the
CDF-level Lévy/Esseen inversion recorded there, it needs the **bivariate** Edgeworth expansion
for `(X̄, X̄₂)` together with the delta-method transfer to the smooth function
`(u, v) ↦ u/√(v − u²)`. Neither is available at this pin; see the status note at the head of
`ForMathlib/EsseenSmoothing.lean` for exactly which Fourier foundations now exist. -/
theorem edgeworth_studentized_uniform [IsProbabilityMeasure F]
    -- USER-INPUT: finite fourth moment of the sampling law
    (hF4 : MemLp (fun t : ℝ => t) 4 F)
    -- USER-INPUT: nonzero variance
    (hFvar : 0 < Var[fun t : ℝ => t; F])
    -- USER-INPUT: the sampling law is absolutely continuous; the smoothness requirement under
    -- which the studentized expansion is stated
    (hFac : F ≪ volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ t : ℝ,
      |studentizedRootCDF F n t -
        (stdNormalCDF t +
          (1 / 6) * skewness F * stdNormalPDF t * (2 * t ^ 2 + 1) * (Real.sqrt n)⁻¹)|
      ≤ C / n := by
  sorry

/-- **Cornish–Fisher expansion of the studentized quantile, with `O(n^{-1})` accuracy.**

Inverting the studentized expansion gives the corresponding expansion of the quantile function:
the `1 − α` quantile of the studentized root equals the standard normal quantile corrected by
`−(1/6) γ (2 z²_{1−α} + 1) n^{-1/2}`, with an `O(n^{-1})` error holding uniformly over levels
bounded away from `0` and `1`.

DEFERRAL-ELIGIBLE (planned debt). This is a *corollary* of
`edgeworth_studentized_uniform`, not an independent analytic fact: given the studentized
expansion, the quantile version follows by inverting it (the Cornish–Fisher step is the implicit
function theorem applied to `x ↦ Φ(x) + (γ/6)φ(x)(2x² + 1) n^{-1/2}`, using that `φ` is bounded
below on the compact `z`-range corresponding to `α ∈ [ε, 1 − ε]`, which is where the hypothesis
`0 < ε < 1/2` is used). It therefore inherits, and adds nothing to, the obstruction recorded on
`edgeworth_studentized_uniform`. -/
theorem cornishFisher_studentized_quantile [IsProbabilityMeasure F]
    -- USER-INPUT: finite fourth moment of the sampling law
    (hF4 : MemLp (fun t : ℝ => t) 4 F)
    -- USER-INPUT: nonzero variance
    (hFvar : 0 < Var[fun t : ℝ => t; F])
    -- USER-INPUT: absolute continuity of the sampling law
    (hFac : F ≪ volume)
    -- USER-INPUT: the levels are bounded away from `0` and `1`; the expansion is not uniform
    -- over the whole range of levels
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ α ∈ Set.Icc ε (1 - ε),
      |cdfPseudoInverse (studentizedRootCDF F n) (1 - α) -
        (stdNormalQuantile (1 - α) -
          (1 / 6) * skewness F * (2 * stdNormalQuantile (1 - α) ^ 2 + 1) * (Real.sqrt n)⁻¹)|
      ≤ C / n := by
  sorry

end Edgeworth

end StatLean.HypothesisTesting
