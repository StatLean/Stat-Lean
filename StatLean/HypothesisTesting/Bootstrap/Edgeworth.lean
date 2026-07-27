import StatLean.HypothesisTesting.Bootstrap.NonparametricMean
import StatLean.HypothesisTesting.ForMathlib.EsseenSmoothing
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
* The three expansions are **statements only** at this pin, but both analytic halves of the
  route now exist. `ForMathlib/EsseenSmoothing.lean` proves Esseen's smoothing inequality at the
  level of distribution functions (`abs_measure_Iic_sub_le_charFun`), with `normalCDF_sub_le`
  below supplying its Lipschitz input; and `ForMathlib/BerryEsseen.lean` now proves the damped
  expansion of `(charFun F)ⁿ` to order `n⁻¹` (`norm_charFun_pow_sub_edgeworth_le`), which is
  what the weighted Esseen integral needs in order to converge to a *rate* rather than to a
  constant. What is left is the signed-density restatement of the smoothing chain, the Fourier
  transform of the Edgeworth density, the Cramér tail, and the assembly. See the re-derived
  status note (E1)–(E4) on `edgeworth_mean_uniform`.
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

/-! ## The Lipschitz modulus of the normal distribution function

`abs_measure_Iic_sub_le_charFun` (Esseen's smoothing inequality, proved in
`ForMathlib/EsseenSmoothing.lean`) compares a law with an `A`-Lipschitz comparison
distribution function. For the Gaussian comparison that Edgeworth expansions use, `A` is the
supremum of the normal density; the two results below supply it. -/

/-- **The normal distribution function is Lipschitz with constant `(2πv)^{-1/2}`**, the
supremum of the normal density. This is the constant `A` that Esseen's smoothing inequality
`abs_measure_Iic_sub_le_charFun` consumes when the comparison law is normal. -/
theorem normalCDF_sub_le {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    normalCDF m v b - normalCDF m v a ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * (b - a) := by
  have hdisj : gaussianReal m v (Set.Iic b)
      = gaussianReal m v (Set.Iic a) + gaussianReal m v (Set.Ioc a b) := by
    rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hab]
  have hnn : 0 ≤ ∫ x in Set.Ioc a b, gaussianPDFReal m v x :=
    integral_nonneg fun x => gaussianPDFReal_nonneg m v x
  have hstep : normalCDF m v b - normalCDF m v a = ∫ x in Set.Ioc a b, gaussianPDFReal m v x := by
    unfold normalCDF
    rw [hdisj, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      gaussianReal_apply_eq_integral m hv (Set.Ioc a b), ENNReal.toReal_ofReal hnn]
    ring
  have hbound : ∀ x : ℝ, gaussianPDFReal m v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
    intro x
    have hexp : Real.exp (-(x - m) ^ 2 / (2 * v)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have h : (0 : ℝ) ≤ (x - m) ^ 2 / (2 * v) := by positivity
      rw [neg_div]
      linarith
    calc gaussianPDFReal m v x
        = (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(x - m) ^ 2 / (2 * v)) := rfl
      _ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (Real.sqrt (2 * Real.pi * v))⁻¹ := mul_one _
  rw [hstep]
  calc (∫ x in Set.Ioc a b, gaussianPDFReal m v x)
      ≤ ∫ _x in Set.Ioc a b, (Real.sqrt (2 * Real.pi * v))⁻¹ :=
        setIntegral_mono_on (integrable_gaussianPDFReal m v).integrableOn
          (continuous_const.integrableOn_Ioc) measurableSet_Ioc fun x _ => hbound x
    _ = (Real.sqrt (2 * Real.pi * v))⁻¹ * (b - a) := by
        rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_comm]

/-- The standard normal distribution function is `(2π)^{-1/2}`-Lipschitz. -/
theorem stdNormalCDF_sub_le {a b : ℝ} (hab : a ≤ b) :
    stdNormalCDF b - stdNormalCDF a ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (b - a) := by
  simpa using normalCDF_sub_le (m := 0) (v := 1) one_ne_zero hab

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
absorbs the finitely many small `n`). It is not proved here.

**The previously recorded obstruction is overturned.** An earlier note on this theorem named the
CDF-level (Stieltjes) Lévy/Esseen inversion — "the identity `Δ_T(x) = (2π)⁻¹ ∫_{|t| ≤ T}
((φ_P − φ_Q)/(−it)) e^{−itx}(1 − |t|/T) dt`" — as *the estimate that fails*, on the ground that
the integrand is integrable at `t = 0` only through cancellation and that `F_P − F_Q` is not
`L¹`. That is no longer the situation. `ForMathlib/EsseenSmoothing.lean` now proves, axiom-clean
and **without any Stieltjes-level inversion**,

* `abs_measure_Iic_sub_le_of_integral_ramp` — the de-smoothing step ("E2"), and
* `abs_measure_Iic_sub_le_charFun` — Esseen's smoothing inequality at CDF level:
  `|F_P(x) − F_Q(x)| ≤ ∫ ‖φ_P(−2πξ) − φ_Q(−2πξ)‖ min(1/(π|ξ|), 1/(δπ²ξ²)) dξ + A δ`.

The `1/t` weight is obtained by running the whole argument on test functions: ramps squeeze the
half-line indicator, the non-`L¹` tail of a ramp cancels because `P − Q` has total mass zero, and
the resulting compactly supported trapezoid is a difference of two co-centred dilated tents whose
transforms cancel to exactly `1/(π|ξ|)`. The Lipschitz constant `A` for the Gaussian comparison
is `normalCDF_sub_le` above.

**(G2) is now CLOSED; the note that named it "the estimate that fails" is superseded.**
`ForMathlib/BerryEsseen.lean` proves, axiom-clean,

* `norm_charFun_sub_cubic_le` — the fourth-order Taylor expansion
  `‖φ_F(u) − (1 − v u²/2 − i m₃ u³/6)‖ ≤ (E X⁴) |u|⁴/24`, retaining the third cumulant;
* `norm_charFun_le_exp_neg_sq` — the quadratic majorant `‖φ_F(s)‖ ≤ e^{−v s²/4}` on the window
  `v s² ≤ 2`, `ρ|s| ≤ 3v/2`;
* `norm_pow_sub_pow_sub_lin_le` — the **second-order** telescoping bound
  `‖aⁿ − bⁿ − n bⁿ⁻¹(a − b)‖ ≤ n(n−1)/2 · Mⁿ⁻² ‖a − b‖²`, which unlike the first-order
  `norm_prod_sub_prod_le` *keeps* the damping factor `Mⁿ⁻²`;
* and hence `norm_charFun_pow_sub_edgeworth_le`, the damped expansion itself:
  `‖φ_F(s)ⁿ − e^{−n v s²/2}(1 − n i m₃ s³/6)‖ ≤ e^{−(n−2) v s²/4} · (n(n−1)/2 · D² + n(w + e₀))`
  with `D = ρ|s|³/6 + (v s²/2)²/2`, `e₀ = (E X⁴)|s|⁴/24 + (v s²/2)²/2` and
  `w = (v s²/2)(|m₃||s|³/6)`.

Substituting the standardized scaling `s = t/(σ√n)`, `v = σ²`, `m₃ = γσ³` turns this into
exactly the estimate that was called for:
`‖φ_F(t/(σ√n))ⁿ − e^{−t²/2}(1 + (γ/6)(it)³ n^{−1/2})‖ ≤ C (t⁴ + t⁵ + t⁶) e^{−t²/4}/n`
on `|t| ≤ c√n` — the three terms of the bound scaling as `t⁶/n`, `t⁴/n` and `t⁵/n^{3/2}`
respectively, all against the envelope `e^{−(n−2)t²/(4n)}`. The weighted integral in
`abs_measure_Iic_sub_le_charFun` therefore now converges to `O(n⁻¹)` rather than to a constant.

**Re-derivation: what actually remains.** Four items.

* (E1) **Signed comparison — bookkeeping, not an obstruction** (was (G1); unchanged). The
  Edgeworth approximant is not the distribution function of a probability measure: it is a signed
  measure with the explicit `L¹` density
  `y ↦ σ⁻¹φ(y/σ)(1 + (γ/6)(y³/σ³ − 3y/σ) n^{-1/2})`.
  (*Sign correction.* An earlier version of this note wrote that density with a minus sign in
  front of `(γ/6)`. That is wrong: differentiating the approximant
  `Φ(y/σ) − (γ/6)φ(y/σ)(y²/σ² − 1)n^{-1/2}` in the statement below and using
  `d/dx[φ(x)(x² − 1)] = −φ(x)(x³ − 3x)` gives a plus sign. The *statement* of the theorem is
  correct; only the note was.) `abs_measure_Iic_sub_le_charFun` is stated for two probability
  measures, and uses that hypothesis on `Q` only through (a) equality of total masses, which is
  what makes the ramp mass at `−∞` cancel (`tendsto_integral_ramp_atBot`), and (b) Parseval
  against a finite measure (`integral_fourier_measure`). Both survive verbatim for
  `volume.withDensity q` with `q` real `L¹` of integral `1`; restating the chain for a density
  instead of a measure is the work.
* (E2) **The Fourier transform of the Edgeworth density.** To feed (E1) into
  `norm_charFun_pow_sub_edgeworth_le` one needs
  `∫ e^{i t y} q_n(y) dy = e^{−σ²t²/2}(1 − i m₃ t³/(6√n))`, i.e. after the substitution
  `y = σu`, `θ = σt`, the Hermite identity
  `∫ e^{iθu}(u³ − 3u)φ(u) du = (iθ)³ e^{−θ²/2}`.
  Two integrations by parts against `u φ(u) = −φ'(u)` reduce this to Mathlib's Gaussian
  characteristic function; neither the identity nor the intermediate
  `∫ u² e^{iθu}φ(u) du = (1 − θ²)e^{−θ²/2}` is present at this pin. (This computation is what
  verifies that the Edgeworth approximant of the *statement* below matches the approximant of
  `norm_charFun_pow_sub_edgeworth_le`; the check has been carried out by hand and they agree.)
* (E3) **The Cramér tail** (was (G3)). Off the window one needs
  `∫_{c√n ≤ |t|} ‖φ_F(t/(σ√n))‖ⁿ min(1/|t|, 1/(δπ²t²)) dt = o(n⁻¹)`. `CramerCondition` gives
  `‖φ_F s‖ ≤ c < 1` only *off a compact set*; the moderate range `ε ≤ |s| ≤ R` additionally needs
  `sup_{ε ≤ |s| ≤ R} ‖φ_F s‖ < 1`, which by compactness and `continuous_charFun` reduces to
  `‖φ_F s‖ < 1` for every `s ≠ 0`.
  *The earlier verdict on this item is too pessimistic.* It claimed the reduction goes through
  the lattice characterisation `‖φ_F s₀‖ = 1 ↔ F` lattice, "absent from Mathlib v4.29.1". The
  lattice statement is never needed: what is needed is only that the modulus-one set is closed
  under integer multiples, and that follows from the *equality case in* `‖∫ f‖ ≤ ∫‖f‖`, which
  on a probability space is elementary — if `‖∫ e^{is₀x} dF‖ = 1 = ∫ 1 dF` then
  `Re(θ̄ e^{is₀x}) = 1` a.e. by nonnegativity of `1 − Re(θ̄ e^{is₀x})`, hence
  `e^{is₀x} = θ` a.e., hence `φ_F(k s₀) = θᵏ` has modulus `1` for every `k`, contradicting the
  cocompact bound once `k|s₀|` exceeds the compact set. So (E3) is a short elementary argument,
  not a missing Mathlib theory; it is simply not written yet.
* (E4) **The assembly.** Choose `δ ≍ n⁻¹` in `abs_measure_Iic_sub_le_charFun` (so that the
  Lipschitz term `A δ` from `normalCDF_sub_le` is `O(n⁻¹)`), split the `ξ`-integral at
  `|ξ| ≍ √n`, bound the inner range by (E2) + `norm_charFun_pow_sub_edgeworth_le` against the
  weight `1/(π|ξ|)`, and the outer range by (E3). This is the only step that is genuinely long
  rather than genuinely hard. -/
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
not proved here, and it is strictly harder than `edgeworth_mean_uniform`: it inherits (E1)–(E4)
recorded there and needs in addition the **bivariate** Edgeworth expansion for `(X̄, X̄₂)`
together with the delta-method transfer to the smooth function `(u, v) ↦ u/√(v − u²)`.

Two of the pieces this note used to name as missing are now present, and the corresponding
verdicts are dead. The CDF-level Esseen inversion is proved
(`abs_measure_Iic_sub_le_charFun` in `ForMathlib/EsseenSmoothing.lean`), and the damped
characteristic-function expansion — recorded as *the* binding estimate — is proved
(`norm_charFun_pow_sub_edgeworth_le` in `ForMathlib/BerryEsseen.lean`). What remains genuinely
specific to this theorem is the bivariate expansion: the univariate damped bound above does not
transfer to `(X̄, X̄₂)` without a two-dimensional analogue of
`norm_charFun_le_exp_neg_sq`, whose window is governed by the smallest eigenvalue of the
covariance of `(X, X²)` and therefore needs the nondegeneracy that `hFac` supplies. -/
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
`0 < ε < 1/2` is used). It therefore inherits, and adds nothing to, the obstructions recorded on
`edgeworth_studentized_uniform` and, through it, (E1)–(E4) on `edgeworth_mean_uniform`. -/
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
