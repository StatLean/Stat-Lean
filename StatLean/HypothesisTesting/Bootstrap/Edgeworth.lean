import StatLean.HypothesisTesting.Bootstrap.NonparametricMean
import StatLean.HypothesisTesting.ForMathlib.BivariateEdgeworth
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

The three expansions themselves are **statements only**; the supporting analysis around them is
proved:

* `skewness`, `stdNormalPDF`, `CramerCondition` — the carriers;
* `norm_charFun_lt_one_of_cramer`, `exists_bound_lt_one_of_cramer` — what Cramér's condition
  buys off the origin: `‖φ_F s‖ < 1` for every `s ≠ 0`, and a single constant `c < 1`
  dominating `‖φ_F‖` on a whole region `ε ≤ |s|`. This is the input of the Cramér tail;
* `normalCDF_sub_le`, `stdNormalCDF_sub_le` — the Lipschitz modulus of the normal distribution
  function, the constant `A` that Esseen's smoothing inequality consumes;
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
* **`edgeworth_mean_uniform` is now PROVED, axiom-clean**; only the two *studentized* results
  are statements at this pin. Its supporting chain: `ForMathlib/EsseenSmoothing.lean` proves
  Esseen's smoothing inequality at the level of distribution functions
  (`abs_measure_Iic_sub_le_charFun`), with `normalCDF_sub_le` below supplying its Lipschitz
  input, **and its signed-density form** (`abs_measure_Iic_sub_densityCDF_le_charFun`), which is
  what an Edgeworth approximant needs; `ForMathlib/BerryEsseen.lean` proves the damped expansion
  of `(charFun F)ⁿ` to order `n⁻¹` (`norm_charFun_pow_sub_edgeworth_le`) **and the Hermite
  Fourier identity** (`integral_hermite3_mul_cexp_mul_gaussian`) that transforms the Edgeworth
  density; the Cramér tail's analytic input is proved here (`exists_bound_lt_one_of_cramer`,
  transferred to the centred law by `cramerCondition_centredLaw`) and its bookkeeping in
  `ForMathlib/EsseenSmoothing.lean` (`setIntegral_mul_esseenWeight_tail_le`,
  `exists_pow_mul_geometric_le`). The assembly itself is here: the law of the root
  (`charFun_meanRootLaw`, `charFun_stdRootLaw`, `meanRootCDF_eq_stdRootLaw`, and the moments and
  integrability of `centredLaw`), the comparison density (`edgeworthDensity`, `edgeworthCDF`,
  `densityCDF_edgeworthDensity`, `abs_edgeworthDensity_le`,
  `setIntegral_abs_edgeworthDensity_le`, `charFunDensity_edgeworthDensity`,
  `norm_charFunDensity_edgeworthDensity_le`, `abs_edgeworthCDF_le`), the window estimate
  (`window_conditions`, `edgeworth_approx_eq`, `exists_window_core`, `exists_window_bound`), the
  outer range (`edgeworthCharFun_tail_le`, `edgeworthGap_tail_le`) and the glue
  (`esseen_split`, `abs_meanRootCDF_sub_edgeworthCDF_le`). See the status note (E1)–(E4) on that
  theorem.
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

/-! ## What Cramér's condition buys off the origin

The Cramér tail of an Edgeworth expansion needs a bound `‖φ_F s‖ ≤ c < 1` valid on a whole
region `ε ≤ |s|`, whereas `CramerCondition` supplies one only *off a compact set*. The three
results below close that gap. The classical argument passes through the characterisation
"`‖φ_F s₀‖ = 1` iff `F` is carried by a lattice", which is absent from Mathlib at this pin; it
is not needed. All that is used is that the modulus-one set is closed under integer multiples,
and that is the equality case of `‖∫ f‖ ≤ ∫‖f‖`, which on a probability space is elementary:
`1 − Re(θ̄ e^{i s x})` is nonnegative with vanishing integral, so `e^{i s x}` is a.e. constant. -/

section Cramer

variable {F : Measure ℝ}

/-- **Equality case of `‖∫ f‖ ≤ ∫ ‖f‖` for a characteristic function.** If the characteristic
function of a probability law has modulus `1` at `s`, then `x ↦ e^{i s x}` is almost surely
equal to the constant `charFun F s`.

The proof needs no general equality-case theory: `z x = conj(φ(s)) e^{i s x}` has modulus `1`
everywhere and integral `1`, so `1 − Re(z x)` is a nonnegative function with vanishing integral,
hence `Re(z x) = 1 = ‖z x‖` a.e., which forces `z x = 1`. -/
private lemma ae_cexp_eq_of_norm_charFun_eq_one [IsProbabilityMeasure F] {s : ℝ}
    (h : ‖charFun F s‖ = 1) :
    ∀ᵐ (x : ℝ) ∂F, Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I) = charFun F s := by
  have hnorm : ∀ x : ℝ, ‖Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := fun x => by
    rw [Complex.norm_exp,
      show (((s : ℂ) * (x : ℂ) * Complex.I)).re = 0 by simp, Real.exp_zero]
  have hInt : Integrable (fun x : ℝ => Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)) F :=
    (integrable_const (1 : ℝ)).mono'
      ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
      (ae_of_all _ fun x => le_of_eq (hnorm x))
  have hzn : ∀ x : ℝ,
      ‖(starRingEnd ℂ) (charFun F s) * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)‖ = 1 :=
    fun x => by rw [norm_mul, RCLike.norm_conj, h, hnorm, mul_one]
  have hcm : (starRingEnd ℂ) (charFun F s) * charFun F s = 1 := by
    rw [RCLike.conj_mul, h]; norm_num
  have hIprod : ∫ x : ℝ,
      ((starRingEnd ℂ) (charFun F s) * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)) ∂F = 1 := by
    have hpull : ∫ x : ℝ,
          ((starRingEnd ℂ) (charFun F s) * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)) ∂F
        = (starRingEnd ℂ) (charFun F s)
            * ∫ x : ℝ, Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I) ∂F := by
      simp_rw [← smul_eq_mul]
      exact integral_smul _ _
    rw [hpull, ← charFun_apply_real, hcm]
  have hIntRe : Integrable (fun x : ℝ =>
      ((starRingEnd ℂ) (charFun F s) * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)).re) F :=
    (hInt.const_mul _).re
  have hreInt : ∫ x : ℝ,
        ((starRingEnd ℂ) (charFun F s) * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)).re ∂F
      = (∫ x : ℝ,
        ((starRingEnd ℂ) (charFun F s) * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)) ∂F).re :=
    integral_re (hInt.const_mul _)
  rw [hIprod] at hreInt
  have hgnn : ∀ x : ℝ,
      0 ≤ 1 - ((starRingEnd ℂ) (charFun F s)
        * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)).re := fun x => by
    have hle := Complex.re_le_norm
      ((starRingEnd ℂ) (charFun F s) * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I))
    rw [hzn x] at hle
    linarith
  have hgint : Integrable (fun x : ℝ =>
      1 - ((starRingEnd ℂ) (charFun F s)
        * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)).re) F :=
    (integrable_const (1 : ℝ)).sub hIntRe
  have hgzero : ∫ x : ℝ, (1 - ((starRingEnd ℂ) (charFun F s)
      * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)).re) ∂F = 0 := by
    rw [integral_sub (integrable_const (1 : ℝ)) hIntRe, hreInt]
    simp
  have hae := (integral_eq_zero_iff_of_nonneg hgnn hgint).1 hgzero
  filter_upwards [hae] with x hx
  have hre1 : ((starRingEnd ℂ) (charFun F s)
      * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)).re = 1 := by
    have hx' : (1 : ℝ) - ((starRingEnd ℂ) (charFun F s)
        * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)).re = 0 := hx
    linarith
  have hz1 : (starRingEnd ℂ) (charFun F s)
      * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I) = 1 := by
    have hle : ‖(starRingEnd ℂ) (charFun F s)
          * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)‖
        ≤ ((starRingEnd ℂ) (charFun F s)
          * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)).re := by rw [hzn x, hre1]
    have heq := RCLike.norm_le_re_iff_eq_norm.1 hle
    rw [heq, hzn x]
    norm_num
  calc Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)
      = ((starRingEnd ℂ) (charFun F s) * charFun F s)
          * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I) := by rw [hcm, one_mul]
    _ = charFun F s * ((starRingEnd ℂ) (charFun F s)
          * Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I)) := by ring
    _ = charFun F s := by rw [hz1, mul_one]

/-- **The modulus-one set is closed under integer multiples.** If `‖charFun F s‖ = 1` then
`charFun F (k s) = (charFun F s)ᵏ`, so it too has modulus `1`. This is the only consequence of
`‖charFun F s‖ = 1` that the Cramér tail needs — in particular the lattice structure of `F`
never has to be exhibited. -/
private lemma norm_charFun_natCast_mul_eq_one [IsProbabilityMeasure F] {s : ℝ}
    (h : ‖charFun F s‖ = 1) (k : ℕ) : ‖charFun F ((k : ℝ) * s)‖ = 1 := by
  have hae := ae_cexp_eq_of_norm_charFun_eq_one h
  have hpow : charFun F ((k : ℝ) * s) = charFun F s ^ k := by
    rw [charFun_apply_real ((k : ℝ) * s)]
    have hc : ∀ᵐ (x : ℝ) ∂F,
        Complex.exp ((((k : ℝ) * s : ℝ) : ℂ) * (x : ℂ) * Complex.I) = charFun F s ^ k := by
      filter_upwards [hae] with x hx
      rw [← hx, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [integral_congr_ae hc]
    simp
  rw [hpow, norm_pow, h, one_pow]

/-- **Cramér's condition forces a strict bound away from the origin.** Under `CramerCondition`,
`‖charFun F s‖ < 1` for every `s ≠ 0`.

If `‖charFun F s‖ = 1` then `‖charFun F (k|s|)‖ = 1` for every `k : ℕ` by
`norm_charFun_natCast_mul_eq_one` (using `charFun_neg` to move to `|s|`), and `k|s| → ∞`
eventually leaves the compact set on which the cocompact bound may fail — contradiction. -/
theorem norm_charFun_lt_one_of_cramer [IsProbabilityMeasure F]
    (hCramer : CramerCondition F) {s : ℝ} (hs : s ≠ 0) : ‖charFun F s‖ < 1 := by
  rcases lt_or_eq_of_le (norm_charFun_le_one (μ := F) s) with hlt | heq
  · exact hlt
  exfalso
  obtain ⟨c, hc, hev⟩ := hCramer
  have hsym : ∀ t : ℝ, ‖charFun F (-t)‖ = ‖charFun F t‖ := fun t => by
    rw [charFun_neg, RCLike.norm_conj]
  have habs : ‖charFun F |s|‖ = 1 := by
    rcases abs_cases s with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; exact heq
    · rw [he, hsym]; exact heq
  have hspos : 0 < |s| := abs_pos.2 hs
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup] at hev
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev.2
  obtain ⟨k, hk⟩ := exists_nat_gt (M / |s|)
  have hkM : M ≤ (k : ℝ) * |s| := by
    rw [div_lt_iff₀ hspos] at hk
    linarith
  have h1 := hM _ hkM
  rw [norm_charFun_natCast_mul_eq_one habs k] at h1
  linarith

/-- **The uniform Cramér bound on `ε ≤ |s|`.** This is the form the Edgeworth tail estimate
consumes: a single constant `c < 1` dominating `‖charFun F s‖` on the *whole* region
`ε ≤ |s|`, not merely off a compact set.

The compact middle range `ε ≤ |s| ≤ R` is handled by `continuous_charFun` together with
`norm_charFun_lt_one_of_cramer`; the outer range by the cocompact bound; and negative arguments
by `charFun_neg`. -/
theorem exists_bound_lt_one_of_cramer [IsProbabilityMeasure F]
    (hCramer : CramerCondition F) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, c < 1 ∧ ∀ s : ℝ, ε ≤ |s| → ‖charFun F s‖ ≤ c := by
  obtain ⟨c₀, hc₀, hev⟩ := id hCramer
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup] at hev
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev.2
  have hεR : ε ≤ max M ε := le_max_right _ _
  obtain ⟨s₀, hs₀mem, hs₀max⟩ := (isCompact_Icc (a := ε) (b := max M ε)).exists_isMaxOn
    ⟨ε, le_rfl, hεR⟩ (Continuous.continuousOn (continuous_charFun (μ := F)).norm)
  have hs₀ne : s₀ ≠ 0 := fun hzero => by
    have := hs₀mem.1; rw [hzero] at this; linarith
  refine ⟨max c₀ ‖charFun F s₀‖, max_lt hc₀ (norm_charFun_lt_one_of_cramer hCramer hs₀ne), ?_⟩
  have hsym : ∀ t : ℝ, ‖charFun F (-t)‖ = ‖charFun F t‖ := fun t => by
    rw [charFun_neg, RCLike.norm_conj]
  have key : ∀ t : ℝ, ε ≤ t → ‖charFun F t‖ ≤ max c₀ ‖charFun F s₀‖ := by
    intro t ht
    rcases le_or_gt t (max M ε) with hle | hgt
    · exact (hs₀max ⟨ht, hle⟩).trans (le_max_right _ _)
    · exact (hM t ((le_max_left M ε).trans hgt.le)).trans (le_max_left _ _)
  intro s hs
  rcases abs_cases s with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he] at hs; exact key s hs
  · rw [he] at hs; rw [← hsym s]; exact key (-s) hs

end Cramer

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

/-! ## The law of the root

Item (E4).1 of the assembly programme below: the characteristic function of the law of the
centred and scaled sample mean is the `n`-th power of the characteristic function of the
*centred* sampling law, evaluated at `t/√n`. Mathlib's `charFun_inv_sqrt_mul_sum` is stated for
an `iIndepFun` family on an abstract probability space; `meanRootLaw` is defined on
`Measure.pi`, and there the factorisation is *direct* — no transfer through the canonical
i.i.d. construction is needed, because `MeasureTheory.integral_fintype_prod_eq_pow` is exactly
Fubini for a product of one-variable factors. -/

section RootLaw

/-- The **centred sampling law**: the pushforward of `F` under `x ↦ x − E_F X`. This is the law
the damped Edgeworth expansion `norm_charFun_pow_sub_edgeworth_le` is applied to, since that
result assumes a vanishing mean. -/
noncomputable def centredLaw (F : Measure ℝ) : Measure ℝ :=
  F.map fun x : ℝ => x - ∫ s, s ∂F

instance isProbabilityMeasure_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F] :
    IsProbabilityMeasure (centredLaw F) := by
  rw [centredLaw]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The root map `y ↦ √n (X̄ₙ − E_F X)` is `(√n)⁻¹` times the sum of the centred coordinates. -/
private lemma sqrt_mul_sub_mean_eq {n : ℕ} (hn : 0 < n) (m : ℝ) (y : Fin n → ℝ) :
    Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - m)
      = (Real.sqrt n)⁻¹ * ∑ i, (y i - m) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set r : ℝ := Real.sqrt n with hr
  have hs : 0 < r := Real.sqrt_pos.2 hn0
  have hsq : r * r = (n : ℝ) := Real.mul_self_sqrt hn0.le
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← hsq]
  have e1 : r * (r * r)⁻¹ = r⁻¹ := by
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have e2 : r⁻¹ * (r * r) = r := by
    rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  calc r * ((r * r)⁻¹ * (∑ i, y i) - m)
      = r * (r * r)⁻¹ * (∑ i, y i) - r * m := by ring
    _ = r⁻¹ * (∑ i, y i) - r * m := by rw [e1]
    _ = r⁻¹ * (∑ i, y i) - r⁻¹ * (r * r) * m := by rw [e2]
    _ = r⁻¹ * ((∑ i, y i) - r * r * m) := by ring

/-- **The characteristic function of the law of the centred root.**
`φ_{meanRootLaw F n}(t) = (φ_{F₀}(t/√n))ⁿ` for the centred law `F₀ = centredLaw F`.

This is item (E4).1 of the assembly of `edgeworth_mean_uniform`: it is what lets the damped
expansion `norm_charFun_pow_sub_edgeworth_le`, which estimates an `n`-th power of a
characteristic function, be applied to the sampling distribution of the root. -/
theorem charFun_meanRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] {n : ℕ} (hn : 0 < n)
    (t : ℝ) :
    charFun (meanRootLaw F n) t
      = charFun (centredLaw F) ((Real.sqrt n)⁻¹ * t) ^ n := by
  set m : ℝ := ∫ s, s ∂F with hm
  set c : ℝ := (Real.sqrt n)⁻¹ * t with hc
  have hmeasg : Measurable fun y : Fin n → ℝ =>
      Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - m) := by fun_prop
  have hstep1 : charFun (meanRootLaw F n) t
      = ∫ y : Fin n → ℝ, ∏ i : Fin n,
          Complex.exp ((c : ℂ) * ((y i - m : ℝ) : ℂ) * Complex.I)
        ∂(Measure.pi fun _ : Fin n => F) := by
    have hf : AEStronglyMeasurable
        (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
        ((Measure.pi fun _ : Fin n => F).map
          fun y : Fin n → ℝ => Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - m)) := by fun_prop
    rw [charFun_apply_real, meanRootLaw, ← hm, integral_map hmeasg.aemeasurable hf]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change Complex.exp ((t : ℂ)
      * ((Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - m) : ℝ) : ℂ) * Complex.I) = _
    rw [sqrt_mul_sub_mean_eq hn m y]
    have hsum : (t : ℂ) * ((((Real.sqrt n)⁻¹ * ∑ i, (y i - m) : ℝ)) : ℂ) * Complex.I
        = ∑ i : Fin n, ((c : ℂ) * ((y i - m : ℝ) : ℂ) * Complex.I) := by
      simp only [hc, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_sub,
        Complex.ofReal_inv, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, Complex.exp_sum]
  have hstep2 : (∫ y : Fin n → ℝ, ∏ i : Fin n,
        Complex.exp ((c : ℂ) * ((y i - m : ℝ) : ℂ) * Complex.I)
      ∂(Measure.pi fun _ : Fin n => F))
      = (∫ x : ℝ, Complex.exp ((c : ℂ) * ((x - m : ℝ) : ℂ) * Complex.I) ∂F) ^ n := by
    have h := MeasureTheory.integral_fintype_prod_eq_pow (ι := Fin n) (μ := F)
      (fun x : ℝ => Complex.exp ((c : ℂ) * ((x - m : ℝ) : ℂ) * Complex.I))
    simpa using h
  have hstep3 : (∫ x : ℝ, Complex.exp ((c : ℂ) * ((x - m : ℝ) : ℂ) * Complex.I) ∂F)
      = charFun (centredLaw F) c := by
    have hf3 : AEStronglyMeasurable
        (fun x : ℝ => Complex.exp ((c : ℂ) * (x : ℂ) * Complex.I))
        (F.map fun x : ℝ => x - m) := by fun_prop
    rw [charFun_apply_real, centredLaw, ← hm,
      integral_map (by fun_prop : AEMeasurable (fun x : ℝ => x - m) F) hf3]
  rw [hstep1, hstep2, hstep3]

instance isProbabilityMeasure_meanRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ) :
    IsProbabilityMeasure (meanRootLaw F n) := by
  rw [meanRootLaw]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The **standardized root law**: the law of `√n(X̄ₙ − E_F X)/σ`.

The whole Edgeworth comparison is run on this law rather than on `meanRootLaw`, because the
comparison density is then the `σ`-free `edgeworthDensity` and no Gaussian scaling identity is
needed. The `σ` reappears only in the *argument*, through `meanRootCDF_eq_stdRootLaw`. -/
noncomputable def stdRootLaw (F : Measure ℝ) (n : ℕ) : Measure ℝ :=
  (meanRootLaw F n).map fun y : ℝ => (Real.sqrt Var[fun t : ℝ => t; F])⁻¹ * y

instance isProbabilityMeasure_stdRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ) :
    IsProbabilityMeasure (stdRootLaw F n) := by
  rw [stdRootLaw]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- **The characteristic function of the standardized root**, as an `n`-th power. -/
theorem charFun_stdRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] {n : ℕ} (hn : 0 < n)
    (θ : ℝ) :
    charFun (stdRootLaw F n) θ
      = charFun (centredLaw F)
          ((Real.sqrt n)⁻¹ * ((Real.sqrt Var[fun t : ℝ => t; F])⁻¹ * θ)) ^ n := by
  rw [stdRootLaw, charFun_map_mul, charFun_meanRootLaw F hn]

/-- **The sampling distribution function is the standardized law at the rescaled argument.**
`meanRootCDF F n t = P'_n((-∞, t/σ])`. This is the identity that lets the whole comparison run
on the standardized scale. -/
theorem meanRootCDF_eq_stdRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ)
    (hFvar : 0 < Var[fun t : ℝ => t; F]) (t : ℝ) :
    meanRootCDF F n t
      = (stdRootLaw F n (Set.Iic (t / Real.sqrt Var[fun t : ℝ => t; F]))).toReal := by
  set σ : ℝ := Real.sqrt Var[fun t : ℝ => t; F] with hσdef
  have hσpos : 0 < σ := Real.sqrt_pos.2 hFvar
  have hpre : (fun y : ℝ => σ⁻¹ * y) ⁻¹' Set.Iic (t / σ) = Set.Iic t := by
    ext y
    have hcancel : σ * (t / σ) = t := by field_simp
    simp only [Set.mem_preimage, Set.mem_Iic]
    rw [inv_mul_le_iff₀ hσpos, hcancel]
  rw [meanRootCDF_eq F n t, stdRootLaw, ← hσdef,
    Measure.map_apply (by fun_prop) measurableSet_Iic, hpre]

/-! ### The moments of the centred law

`norm_charFun_pow_sub_edgeworth_le` is stated for a law with vanishing mean, second moment `v`
and third moment `m₃`. Under the centred law these are `0`, `Var_F` and `γ σ³` — the last being
literally the definition of `skewness`. -/

/-- Integration against the centred law is integration of the shifted integrand. -/
lemma integral_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F] {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (centredLaw F)) :
    (∫ x, g x ∂(centredLaw F)) = ∫ t, g (t - ∫ s, s ∂F) ∂F := by
  rw [centredLaw, integral_map (by fun_prop) hg]

/-- The centred law has mean zero. -/
lemma integral_id_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F]
    (hint : Integrable (fun t : ℝ => t) F) :
    (∫ x, x ∂(centredLaw F)) = 0 := by
  rw [integral_centredLaw F (g := fun x : ℝ => x) (by fun_prop),
    integral_sub hint (integrable_const _), integral_const]
  simp

/-- The second moment of the centred law is the variance of `F`. -/
lemma integral_sq_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F] :
    (∫ x, x ^ 2 ∂(centredLaw F)) = Var[fun t : ℝ => t; F] := by
  rw [integral_centredLaw F (g := fun x : ℝ => x ^ 2) (by fun_prop),
    variance_eq_integral (by fun_prop)]

/-- The third moment of the centred law is `γ σ³`: this *is* the definition of skewness. -/
lemma integral_cube_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFvar : 0 < Var[fun t : ℝ => t; F]) :
    (∫ x, x ^ 3 ∂(centredLaw F))
      = skewness F * Real.sqrt Var[fun t : ℝ => t; F] ^ 3 := by
  have hσ : Real.sqrt Var[fun t : ℝ => t; F] ≠ 0 := (Real.sqrt_pos.2 hFvar).ne'
  rw [integral_centredLaw F (g := fun x : ℝ => x ^ 3) (by fun_prop), skewness,
    div_mul_cancel₀ _ (pow_ne_zero 3 hσ)]

/-! ### Integrability of the moments, and the Cramér condition, under centring

`norm_charFun_pow_sub_edgeworth_le` consumes four integrability hypotheses and the outer range
consumes Cramér's condition; all five are stated for the *centred* law, and all five transfer
from `F` for free. Integrability transfers because a fourth moment does
(`memLp_four_centredLaw`) and every lower monomial is dominated by `1 + |x|⁴`; Cramér's
condition transfers because centring multiplies the characteristic function by a unimodular
factor (`norm_charFun_centredLaw`). -/

/-- A finite fourth moment survives centring. -/
lemma memLp_four_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF4 : MemLp (fun t : ℝ => t) 4 F) :
    MemLp (fun x : ℝ => x) 4 (centredLaw F) := by
  rw [centredLaw, memLp_map_measure_iff (by fun_prop) (by fun_prop)]
  exact hF4.sub (memLp_const _)

/-- Every monomial of degree at most four is dominated by `1 + |x|⁴`. -/
private lemma abs_pow_le_one_add_abs_pow_four {x : ℝ} {k : ℕ} (hk : k ≤ 4) :
    |x| ^ k ≤ 1 + |x| ^ 4 := by
  rcases le_total |x| 1 with h | h
  · have h1 : |x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg x) h
    have h4 : (0 : ℝ) ≤ |x| ^ 4 := by positivity
    linarith
  · have h1 : |x| ^ k ≤ |x| ^ 4 := pow_le_pow_right₀ h hk
    linarith

/-- The fourth absolute moment of the centred law is finite. -/
lemma integrable_abs_pow_four_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF4 : MemLp (fun t : ℝ => t) 4 F) :
    Integrable (fun x : ℝ => |x| ^ 4) (centredLaw F) := by
  have h4 : MemLp (fun x : ℝ => x) ((4 : ℕ) : ℝ≥0∞) (centredLaw F) := by
    simpa using memLp_four_centredLaw F hF4
  simpa [Real.norm_eq_abs] using h4.integrable_norm_pow'

/-- Every monomial of degree at most four is integrable under the centred law. -/
private lemma integrable_of_le_abs_pow_four (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF4 : MemLp (fun t : ℝ => t) 4 F) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (centredLaw F)) {k : ℕ} (hk : k ≤ 4)
    (hle : ∀ x : ℝ, |g x| ≤ |x| ^ k) :
    Integrable g (centredLaw F) := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add
    (integrable_abs_pow_four_centredLaw F hF4)) hg
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact (hle x).trans (abs_pow_le_one_add_abs_pow_four hk)

/-- The first moment of the centred law is finite. -/
lemma integrable_id_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF4 : MemLp (fun t : ℝ => t) 4 F) :
    Integrable (fun x : ℝ => x) (centredLaw F) :=
  integrable_of_le_abs_pow_four F hF4 (by fun_prop) (k := 1) (by norm_num)
    fun x => by rw [pow_one]

/-- The second moment of the centred law is finite. -/
lemma integrable_sq_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF4 : MemLp (fun t : ℝ => t) 4 F) :
    Integrable (fun x : ℝ => x ^ 2) (centredLaw F) :=
  integrable_of_le_abs_pow_four F hF4 (by fun_prop) (k := 2) (by norm_num)
    fun x => by rw [abs_pow]

/-- The third absolute moment of the centred law is finite. -/
lemma integrable_abs_cube_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF4 : MemLp (fun t : ℝ => t) 4 F) :
    Integrable (fun x : ℝ => |x| ^ 3) (centredLaw F) :=
  integrable_of_le_abs_pow_four F hF4 (by fun_prop) (k := 3) (by norm_num)
    fun x => le_of_eq (abs_of_nonneg (by positivity))

/-- The fourth moment of the centred law is finite. -/
lemma integrable_pow_four_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF4 : MemLp (fun t : ℝ => t) 4 F) :
    Integrable (fun x : ℝ => x ^ 4) (centredLaw F) :=
  integrable_of_le_abs_pow_four F hF4 (by fun_prop) (k := 4) le_rfl
    fun x => le_of_eq (abs_pow x 4)

/-- **Centring multiplies the characteristic function by a unimodular factor.** -/
lemma charFun_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F] (t : ℝ) :
    charFun (centredLaw F) t
      = Complex.exp (-((t * ∫ s, s ∂F : ℝ) : ℂ) * Complex.I) * charFun F t := by
  set m : ℝ := ∫ s, s ∂F with hm
  have hf : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      (F.map fun x : ℝ => x - m) := by fun_prop
  have hpull : (∫ x : ℝ, Complex.exp (-((t * m : ℝ) : ℂ) * Complex.I)
        * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂F)
      = Complex.exp (-((t * m : ℝ) : ℂ) * Complex.I)
        * ∫ x : ℝ, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂F :=
    MeasureTheory.integral_const_mul _ _
  rw [charFun_apply_real, centredLaw, ← hm,
    integral_map (by fun_prop : AEMeasurable (fun x : ℝ => x - m) F) hf,
    charFun_apply_real, ← hpull]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change Complex.exp ((t : ℂ) * ((x - m : ℝ) : ℂ) * Complex.I)
    = Complex.exp (-((t * m : ℝ) : ℂ) * Complex.I) * Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Centring does not change the modulus of the characteristic function.** -/
lemma norm_charFun_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F] (t : ℝ) :
    ‖charFun (centredLaw F) t‖ = ‖charFun F t‖ := by
  have hre : (-((t * ∫ s, s ∂F : ℝ) : ℂ) * Complex.I).re = 0 := by simp
  rw [charFun_centredLaw, norm_mul, Complex.norm_exp, hre, Real.exp_zero, one_mul]

/-- **Cramér's condition survives centring.** -/
lemma cramerCondition_centredLaw (F : Measure ℝ) [IsProbabilityMeasure F]
    (hCramer : CramerCondition F) : CramerCondition (centredLaw F) := by
  obtain ⟨c, hc, hev⟩ := hCramer
  exact ⟨c, hc, hev.mono fun s hs => by rw [norm_charFun_centredLaw]; exact hs⟩

end RootLaw

/-! ## The studentized root as a function of a bivariate mean

The studentized root is **not** a normalised sum, so its characteristic function is not a power
and `norm_charFun_pow_sub_edgeworth_le` does not apply to it. What it *is* is a fixed smooth
function of the bivariate sample mean of `Z(x) = (x − μ, (x − μ)² − σ²)`, which is a normalised
sum in `ℝ²` and to which `ForMathlib/BivariateEdgeworth.lean` does apply. This section makes
that reduction exact: `studentizedRootCDF F n x` is the mass, under the *bivariate* root law
`vecRootLaw F (studentPair F) n`, of the region `{w : H_n(w) ≤ x}` with

`H_n(w) = w₀ / √(σ² + w₁ n^{-1/2} − w₀² n^{-1})`.

The region is curved and depends on `n`; that is the whole difficulty of the studentized
expansion, and it is exactly what the note on `edgeworth_studentized_uniform` isolates. -/

section StudentizedReduction

/-- The **studentizing pair** `Z(x) = (x − E_F X, (x − E_F X)² − Var_F X)`, a centred random
vector in `ℝ²` whose sample mean carries both the numerator and the denominator of the
studentized root. -/
noncomputable def studentPair (F : Measure ℝ) : ℝ → EuclideanSpace ℝ (Fin 2) := fun x =>
  WithLp.toLp 2 ![x - ∫ s, s ∂F, (x - ∫ s, s ∂F) ^ 2 - Var[fun t : ℝ => t; F]]

lemma measurable_studentPair (F : Measure ℝ) : Measurable (studentPair F) := by
  have hvec : Measurable fun x : ℝ =>
      (![x - ∫ s, s ∂F, (x - ∫ s, s ∂F) ^ 2 - Var[fun t : ℝ => t; F]] : Fin 2 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i
    · change Measurable fun x : ℝ => x - ∫ s, s ∂F
      fun_prop
    · change Measurable fun x : ℝ => (x - ∫ s, s ∂F) ^ 2 - Var[fun t : ℝ => t; F]
      fun_prop
  have htoLp : Measurable (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) := by
    fun_prop
  exact htoLp.comp hvec

/-- **The plug-in sample variance, recentred at an arbitrary point.**
`n⁻¹ ∑ (yᵢ − ȳ)² = n⁻¹ ∑ (yᵢ − m)² − (ȳ − m)²` for every `m`. This is the identity that turns
the denominator of the studentized root into a function of the bivariate mean. -/
private lemma sampleVariance_eq_sub {n : ℕ} (hn : 0 < n) (m : ℝ) (y : Fin n → ℝ) :
    sampleVariance y
      = (n : ℝ)⁻¹ * (∑ i, (y i - m) ^ 2) - ((n : ℝ)⁻¹ * (∑ i, y i) - m) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set S : ℝ := ∑ i, y i with hS
  set db : ℝ := (n : ℝ)⁻¹ * S - m with hdb
  have hsum1 : ∑ i, (y i - m) = (n : ℝ) * db := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hdb, ← hS]
    field_simp
  have hpt : ∀ i, (y i - (n : ℝ)⁻¹ * S) ^ 2
      = (y i - m) ^ 2 - 2 * db * (y i - m) + db ^ 2 := by
    intro i
    rw [hdb]; ring
  have hkey : ∑ i, (y i - (n : ℝ)⁻¹ * S) ^ 2
      = (∑ i, (y i - m) ^ 2) - (n : ℝ) * db ^ 2 := by
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum1,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [sampleVariance, hkey]
  field_simp

/-- **The studentized root is a fixed smooth function of the bivariate mean.**
`studentizedRootCDF F n x` is the mass that the bivariate root law of `studentPair F` gives to
the region `{w : w₀/√(σ² + w₁ n^{-1/2} − w₀² n^{-1}) ≤ x}`.

This is the reduction the studentized Edgeworth expansion runs on: the left-hand side is a
distribution function of a statistic that is *not* a sum, the right-hand side is a set-function
of a law to which the multivariate damped expansion
(`norm_charFun_smul_pow_sub_edgeworth_le`, `charFun_vecRootLaw`) applies. -/
theorem studentizedRootCDF_eq_vecRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] {n : ℕ}
    (hn : 0 < n) (x : ℝ) :
    studentizedRootCDF F n x
      = (vecRootLaw F (studentPair F) n
          {w : EuclideanSpace ℝ (Fin 2) |
            w 0 / Real.sqrt (Var[fun t : ℝ => t; F] + w 1 * (Real.sqrt n)⁻¹
              - w 0 ^ 2 * (n : ℝ)⁻¹) ≤ x}).toReal := by
  set m : ℝ := ∫ s, s ∂F with hm
  set v : ℝ := Var[fun t : ℝ => t; F] with hv
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hnn : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
  set R : Set (EuclideanSpace ℝ (Fin 2)) :=
    {w | w 0 / Real.sqrt (v + w 1 * (Real.sqrt n)⁻¹ - w 0 ^ 2 * (n : ℝ)⁻¹) ≤ x} with hR
  have hRm : MeasurableSet R := by
    have h0 : Measurable fun w : EuclideanSpace ℝ (Fin 2) => w 0 := by fun_prop
    have h1 : Measurable fun w : EuclideanSpace ℝ (Fin 2) => w 1 := by fun_prop
    refine measurableSet_le (h0.div ?_) measurable_const
    exact (((h1.mul_const ((Real.sqrt n)⁻¹)).const_add v).sub
      ((h0.pow_const 2).mul_const ((n : ℝ)⁻¹))).sqrt
  -- the coordinates of the vector root
  have hcoord : ∀ (y : Fin n → ℝ) (i : Fin 2),
      ((Real.sqrt n)⁻¹ • ∑ j, studentPair F (y j)) i
        = (Real.sqrt n)⁻¹ * ∑ j, (studentPair F (y j)) i := by
    intro y i
    simp [Finset.sum_apply]
  have hset : {y : Fin n → ℝ |
        Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - m) / Real.sqrt (sampleVariance y) ≤ x}
      = (fun y : Fin n → ℝ => (Real.sqrt n)⁻¹ • ∑ j, studentPair F (y j)) ⁻¹' R := by
    ext y
    have h0 : ((Real.sqrt n)⁻¹ • ∑ j, studentPair F (y j)) 0
        = Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - m) := by
      rw [hcoord y 0]
      have hcomp : ∀ j, (studentPair F (y j)) 0 = y j - m := fun j => rfl
      simp_rw [hcomp]
      rw [← sqrt_mul_sub_mean_eq hn m y]
    have h1 : ((Real.sqrt n)⁻¹ • ∑ j, studentPair F (y j)) 1
        = (Real.sqrt n)⁻¹ * ∑ j, ((y j - m) ^ 2 - v) := by
      rw [hcoord y 1]
      have hcomp : ∀ j, (studentPair F (y j)) 1 = (y j - m) ^ 2 - v := fun j => rfl
      simp_rw [hcomp]
    have hrad : v + ((Real.sqrt n)⁻¹ * ∑ j, ((y j - m) ^ 2 - v)) * (Real.sqrt n)⁻¹
        - (Real.sqrt n * ((n : ℝ)⁻¹ * (∑ i, y i) - m)) ^ 2 * (n : ℝ)⁻¹
        = sampleVariance y := by
      have hinv : (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹ = (n : ℝ)⁻¹ := by
        rw [← mul_inv, hnn]
      have e1 : ∀ X : ℝ, ((Real.sqrt (n : ℝ))⁻¹ * X) * (Real.sqrt (n : ℝ))⁻¹
          = (n : ℝ)⁻¹ * X := fun X => by rw [← hinv]; ring
      have e2 : ∀ B : ℝ, (Real.sqrt (n : ℝ) * B) ^ 2 = (n : ℝ) * B ^ 2 := fun B => by
        rw [mul_pow, sq, hnn]
      have hsum : ∑ j, ((y j - m) ^ 2 - v) = (∑ j, (y j - m) ^ 2) - (n : ℝ) * v := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      rw [sampleVariance_eq_sub hn m y, hsum, e1, e2]
      field_simp
      ring
    simp only [Set.mem_preimage, hR, Set.mem_setOf_eq, h0, h1, hrad]
  rw [studentizedRootCDF, ← hm, hset, vecRootLaw,
    Measure.map_apply (measurable_vecRoot (measurable_studentPair F) n) hRm]

end StudentizedReduction

/-! ## The Edgeworth approximant on the standardized scale

Item (E4).2 of the assembly programme. The comparison object of an Edgeworth expansion is a
**signed** `L¹` density, and `abs_measure_Iic_sub_densityCDF_le_charFun` consumes it through two
data: its `densityCDF`, which has to be the approximant appearing in the statement, and its
total-variation modulus `∫_{(a,b]} |q| ≤ A(b − a)`, whose constant `A` has to be uniform in `n`.

Everything here is written on the **standardized** scale — the density is
`q_n(u) = φ(u)(1 + (γ/6)(u³ − 3u) n^{-1/2})`, with no `σ` in it. The `σ` of the theorem is then
carried entirely by the argument, `u = t/σ`, which costs one `Measure.map` on the law side and
nothing at all here. In particular no Gaussian scaling identity is needed: `∫_{(-∞,u]} φ = Φ(u)`
is `gaussianReal_apply_eq_integral` verbatim. -/

section Approximant

/-- The **one-term Edgeworth density**, `q_n(u) = φ(u)(1 + (γ/6)(u³ − 3u) n^{-1/2})`. It is a
signed `L¹` density, not a probability density: for `|γ| n^{-1/2}` large it takes both signs.
Its distribution function is `edgeworthCDF` (`densityCDF_edgeworthDensity`). -/
noncomputable def edgeworthDensity (γ : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  stdNormalPDF u * (1 + γ / 6 * (u ^ 3 - 3 * u) * (Real.sqrt n)⁻¹)

/-- The **one-term Edgeworth approximant**, `Φ(u) − (γ/6)φ(u)(u² − 1) n^{-1/2}`: the comparison
distribution function of the expansion, on the standardized scale. -/
noncomputable def edgeworthCDF (γ : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  stdNormalCDF u - 1 / 6 * γ * stdNormalPDF u * (u ^ 2 - 1) * (Real.sqrt n)⁻¹

/-- The **antiderivative of the third Hermite weight**, `−φ(u)(u² − 1)`, whose derivative is
`φ(u)(u³ − 3u)` and whose limit at `−∞` is `0`. -/
noncomputable def hermiteAntideriv (u : ℝ) : ℝ := -(stdNormalPDF u * (u ^ 2 - 1))

/-- The standard normal density in the repo's spelling is Mathlib's Gaussian density. -/
lemma stdNormalPDF_eq_gaussianPDFReal (u : ℝ) : stdNormalPDF u = gaussianPDFReal 0 1 u := by
  have hg : gaussianPDFReal 0 1 u
      = (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹
        * Real.exp (-(u - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) := rfl
  rw [hg, stdNormalPDF, div_eq_inv_mul]
  norm_num

/-- `Φ(u) = ∫_{(-∞,u]} φ`: the standard normal distribution function *is* the `densityCDF` of
the standard normal density. -/
lemma stdNormalCDF_eq_setIntegral (u : ℝ) :
    stdNormalCDF u = ∫ y in Set.Iic u, stdNormalPDF y := by
  have hnn : 0 ≤ ∫ y in Set.Iic u, gaussianPDFReal 0 1 y :=
    integral_nonneg fun y => gaussianPDFReal_nonneg 0 1 y
  simp_rw [stdNormalPDF_eq_gaussianPDFReal]
  rw [stdNormalCDF, normalCDF, gaussianReal_apply_eq_integral 0 one_ne_zero (Set.Iic u),
    ENNReal.toReal_ofReal hnn]

/-- `φ' = −u φ`. -/
lemma hasDerivAt_stdNormalPDF (u : ℝ) :
    HasDerivAt stdNormalPDF (-u * stdNormalPDF u) u := by
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-u) u := by
    have := ((hasDerivAt_pow 2 u).neg).div_const 2
    convert this using 1
    push_cast
    ring
  have h2 := (h1.exp).div_const (Real.sqrt (2 * Real.pi))
  change HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi)) _ u
  convert h2 using 1
  rw [stdNormalPDF]
  ring

/-- `d/du[−φ(u)(u² − 1)] = φ(u)(u³ − 3u)`: the Hermite antiderivative identity. -/
lemma hasDerivAt_hermiteAntideriv (u : ℝ) :
    HasDerivAt hermiteAntideriv (stdNormalPDF u * (u ^ 3 - 3 * u)) u := by
  have h := ((hasDerivAt_stdNormalPDF u).mul ((hasDerivAt_pow 2 u).sub_const 1)).neg
  change HasDerivAt (fun x : ℝ => -(stdNormalPDF x * (x ^ 2 - 1))) _ u
  convert h using 1
  push_cast
  ring

/-- The Hermite antiderivative vanishes at `−∞`. -/
lemma tendsto_hermiteAntideriv_atBot :
    Filter.Tendsto hermiteAntideriv Filter.atBot (𝓝 0) := by
  have hw : Filter.Tendsto (fun u : ℝ => u ^ 2 / 2) Filter.atBot Filter.atTop := by
    have h1 : Filter.Tendsto (fun u : ℝ => |u| ^ 2) Filter.atBot Filter.atTop :=
      (tendsto_pow_atTop (n := 2) (by norm_num)).comp tendsto_abs_atBot_atTop
    have h2 : Filter.Tendsto (fun u : ℝ => u ^ 2) Filter.atBot Filter.atTop := by
      simpa [sq_abs] using h1
    exact h2.atTop_div_const (by norm_num)
  have h1 : Filter.Tendsto (fun w : ℝ => w ^ 1 * Real.exp (-w)) Filter.atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 : Filter.Tendsto (fun w : ℝ => Real.exp (-w)) Filter.atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have h3 : Filter.Tendsto (fun w : ℝ => (2 * w - 1) * Real.exp (-w)) Filter.atTop (𝓝 0) := by
    have h4 := (h1.const_mul (2 : ℝ)).sub h2
    rw [mul_zero, sub_zero] at h4
    exact h4.congr fun w => by ring
  have hg : Filter.Tendsto
      (fun w : ℝ => -((2 * w - 1) * Real.exp (-w) / Real.sqrt (2 * Real.pi)))
      Filter.atTop (𝓝 0) := by
    have := (h3.div_const (Real.sqrt (2 * Real.pi))).neg
    rw [zero_div, neg_zero] at this
    exact this
  refine (hg.comp hw).congr fun u => ?_
  simp only [Function.comp_apply, hermiteAntideriv, stdNormalPDF]
  rw [neg_div]
  ring_nf

/-- The standard normal density is continuous. -/
lemma continuous_stdNormalPDF : Continuous stdNormalPDF := by
  change Continuous fun x : ℝ => Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi)
  fun_prop

/-- Gaussian polynomial moments: `y ↦ φ(y) yᵏ` is integrable. -/
lemma integrable_stdNormalPDF_mul_pow (k : ℕ) :
    Integrable (fun y : ℝ => stdNormalPDF y * y ^ k) := by
  refine Integrable.mono' ((integrable_abs_pow_mul_exp_neg_half_sq k).const_mul
      (Real.sqrt (2 * Real.pi))⁻¹)
    (continuous_stdNormalPDF.mul (continuous_pow k)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  refine le_of_eq ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, stdNormalPDF, abs_div,
    abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg (Real.sqrt_nonneg _), neg_div]
  ring

/-- The standard normal density is integrable. -/
lemma integrable_stdNormalPDF : Integrable stdNormalPDF := by
  simpa using integrable_stdNormalPDF_mul_pow 0

/-- `y ↦ φ(y)(y³ − 3y)` is integrable: the derivative appearing in the FTC step. -/
lemma integrable_stdNormalPDF_mul_hermite3 :
    Integrable (fun y : ℝ => stdNormalPDF y * (y ^ 3 - 3 * y)) := by
  have h3 := integrable_stdNormalPDF_mul_pow 3
  have h1 := (integrable_stdNormalPDF_mul_pow 1).const_mul (3 : ℝ)
  refine (h3.sub h1).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply]
  ring

/-- The Edgeworth density is integrable. -/
lemma integrable_edgeworthDensity (γ : ℝ) (n : ℕ) :
    Integrable (edgeworthDensity γ n) := by
  have hh := integrable_stdNormalPDF_mul_hermite3.const_mul (γ / 6 * (Real.sqrt n)⁻¹)
  refine (integrable_stdNormalPDF.fun_add hh).congr (Filter.Eventually.of_forall fun y => ?_)
  rw [edgeworthDensity]
  ring

/-- **The FTC step.** `∫_{(-∞,u]} φ(y)(y³ − 3y) dy = −φ(u)(u² − 1)`. -/
lemma setIntegral_Iic_stdNormalPDF_mul_hermite3 (u : ℝ) :
    (∫ y in Set.Iic u, stdNormalPDF y * (y ^ 3 - 3 * y)) = hermiteAntideriv u := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (f := hermiteAntideriv)
    (f' := fun y : ℝ => stdNormalPDF y * (y ^ 3 - 3 * y)) (a := u) (m := 0)
    (fun x _ => hasDerivAt_hermiteAntideriv x)
    integrable_stdNormalPDF_mul_hermite3.integrableOn tendsto_hermiteAntideriv_atBot
  rw [h, sub_zero]

/-- **(E4).2 — the approximant is the distribution function of the Edgeworth density.**
`∫_{(-∞,u]} q_n = Φ(u) − (γ/6)φ(u)(u² − 1) n^{-1/2}`. -/
theorem densityCDF_edgeworthDensity (γ : ℝ) (n : ℕ) (u : ℝ) :
    densityCDF (edgeworthDensity γ n) u = edgeworthCDF γ n u := by
  have hsplit : ∀ y : ℝ, edgeworthDensity γ n y
      = stdNormalPDF y + (γ / 6 * (Real.sqrt n)⁻¹) * (stdNormalPDF y * (y ^ 3 - 3 * y)) := by
    intro y
    rw [edgeworthDensity]
    ring
  rw [densityCDF, setIntegral_congr_fun measurableSet_Iic fun y _ => hsplit y,
    integral_add integrable_stdNormalPDF.integrableOn
      (integrable_stdNormalPDF_mul_hermite3.const_mul _).integrableOn,
    MeasureTheory.integral_const_mul, setIntegral_Iic_stdNormalPDF_mul_hermite3,
    ← stdNormalCDF_eq_setIntegral, hermiteAntideriv, edgeworthCDF]
  ring

/-! ### The total-variation modulus

The second datum `abs_measure_Iic_sub_densityCDF_le_charFun` consumes is a constant `A` with
`∫_{(a,b]} |q_n| ≤ A(b − a)`. For a density this is just a uniform bound on `|q_n|`, and the
whole point is that it must not depend on `n`: it does not, because `n^{-1/2} ≤ 1` and
`φ(u)|u|ᵏ ≤ (2π)^{-1/2} 4ᵏ k!` by `abs_pow_le_const_mul_exp_sq_div_four`. -/

/-- `e^{−u²/2}|u|ᵏ ≤ 4ᵏ k!`: the Gaussian kills every monomial, with an explicit constant. -/
private lemma exp_neg_half_sq_mul_abs_pow_le (k : ℕ) (u : ℝ) :
    Real.exp (-u ^ 2 / 2) * |u| ^ k ≤ 4 ^ k * (Nat.factorial k : ℝ) := by
  have hmul : Real.exp (-u ^ 2 / 2) * |u| ^ k
      ≤ Real.exp (-u ^ 2 / 2) * (4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4)) :=
    mul_le_mul_of_nonneg_left (abs_pow_le_const_mul_exp_sq_div_four k u) (Real.exp_pos _).le
  have heq : Real.exp (-u ^ 2 / 2) * (4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4))
      = 4 ^ k * (Nat.factorial k : ℝ) * Real.exp (-u ^ 2 / 4) := by
    rw [show Real.exp (-u ^ 2 / 2) * (4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4))
          = 4 ^ k * (Nat.factorial k : ℝ)
            * (Real.exp (-u ^ 2 / 2) * Real.exp (u ^ 2 / 4)) from by ring,
      ← Real.exp_add]
    congr 2
    ring
  have hle1 : Real.exp (-u ^ 2 / 4) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])
  have hCnn : (0 : ℝ) ≤ 4 ^ k * (Nat.factorial k : ℝ) := by positivity
  calc Real.exp (-u ^ 2 / 2) * |u| ^ k
      ≤ Real.exp (-u ^ 2 / 2) * (4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4)) := hmul
    _ = 4 ^ k * (Nat.factorial k : ℝ) * Real.exp (-u ^ 2 / 4) := heq
    _ ≤ 4 ^ k * (Nat.factorial k : ℝ) * 1 := by nlinarith
    _ = 4 ^ k * (Nat.factorial k : ℝ) := mul_one _

/-- `φ(u)|u|ᵏ ≤ (2π)^{-1/2} C` for any `C` dominating `4ᵏ k!`. -/
private lemma stdNormalPDF_mul_abs_pow_le (k : ℕ) {C : ℝ}
    (hC : 4 ^ k * (Nat.factorial k : ℝ) ≤ C) (u : ℝ) :
    stdNormalPDF u * |u| ^ k ≤ (Real.sqrt (2 * Real.pi))⁻¹ * C := by
  have hrw : stdNormalPDF u * |u| ^ k
      = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-u ^ 2 / 2) * |u| ^ k) := by
    rw [stdNormalPDF]; ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_left ((exp_neg_half_sq_mul_abs_pow_le k u).trans hC)
    (by positivity)

/-- **A uniform bound on the Edgeworth density.** For every `n ≥ 1` and every `u`,
`|q_n(u)| ≤ (2π)^{-1/2}(1 + 66|γ|)`. The constant is *independent of `n`* — which is what the
de-smoothing loss `2Aδ` of `abs_measure_Iic_sub_densityCDF_le_charFun` needs, since `δ` is
taken to be `n⁻¹`. -/
theorem abs_edgeworthDensity_le (γ : ℝ) {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    |edgeworthDensity γ n u| ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |γ|) := by
  have hpdfnn : 0 ≤ stdNormalPDF u := by rw [stdNormalPDF]; positivity
  have hsqrt0 : (0 : ℝ) ≤ (Real.sqrt n)⁻¹ := by positivity
  have hsqrt : (Real.sqrt n)⁻¹ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (1 : ℝ) ≤ Real.sqrt n := by
      simpa using Real.sqrt_le_sqrt h1
    exact inv_le_one_of_one_le₀ h2
  have habs3 : |u ^ 3 - 3 * u| ≤ |u| ^ 3 + 3 * |u| := by
    have h := abs_add_le (u ^ 3) (-(3 * u))
    rw [abs_neg] at h
    calc |u ^ 3 - 3 * u| = |u ^ 3 + -(3 * u)| := by rw [sub_eq_add_neg]
      _ ≤ |u ^ 3| + |3 * u| := h
      _ = |u| ^ 3 + 3 * |u| := by
          rw [abs_pow, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have hbracket : |1 + γ / 6 * (u ^ 3 - 3 * u) * (Real.sqrt n)⁻¹|
      ≤ 1 + |γ| / 6 * (|u| ^ 3 + 3 * |u|) := by
    have htri := abs_add_le (1 : ℝ) (γ / 6 * (u ^ 3 - 3 * u) * (Real.sqrt n)⁻¹)
    rw [abs_one] at htri
    have hval : |γ / 6 * (u ^ 3 - 3 * u) * (Real.sqrt n)⁻¹|
        = |γ| / 6 * |u ^ 3 - 3 * u| * (Real.sqrt n)⁻¹ := by
      rw [abs_mul, abs_mul, abs_div, abs_of_nonneg hsqrt0]
      try norm_num
    have hnn : (0 : ℝ) ≤ |γ| / 6 * |u ^ 3 - 3 * u| := by positivity
    have hstep : |γ / 6 * (u ^ 3 - 3 * u) * (Real.sqrt n)⁻¹|
        ≤ |γ| / 6 * (|u| ^ 3 + 3 * |u|) := by
      rw [hval]
      calc |γ| / 6 * |u ^ 3 - 3 * u| * (Real.sqrt n)⁻¹
          ≤ |γ| / 6 * |u ^ 3 - 3 * u| * 1 := mul_le_mul_of_nonneg_left hsqrt hnn
        _ = |γ| / 6 * |u ^ 3 - 3 * u| := mul_one _
        _ ≤ |γ| / 6 * (|u| ^ 3 + 3 * |u|) :=
            mul_le_mul_of_nonneg_left habs3 (by positivity)
    linarith [htri, hstep]
  have hkey : |edgeworthDensity γ n u|
      ≤ stdNormalPDF u * (1 + |γ| / 6 * (|u| ^ 3 + 3 * |u|)) := by
    rw [edgeworthDensity, abs_mul, abs_of_nonneg hpdfnn]
    exact mul_le_mul_of_nonneg_left hbracket hpdfnn
  have hb0 := stdNormalPDF_mul_abs_pow_le 0 (C := 1) (by norm_num) u
  have hb1 := stdNormalPDF_mul_abs_pow_le 1 (C := 4) (by norm_num [Nat.factorial]) u
  have hb3 := stdNormalPDF_mul_abs_pow_le 3 (C := 384) (by norm_num [Nat.factorial]) u
  rw [pow_zero, mul_one, mul_one] at hb0
  rw [pow_one] at hb1
  have e1 := mul_le_mul_of_nonneg_left hb1 (by positivity : (0 : ℝ) ≤ |γ| / 2)
  have e3 := mul_le_mul_of_nonneg_left hb3 (by positivity : (0 : ℝ) ≤ |γ| / 6)
  have hexp : stdNormalPDF u * (1 + |γ| / 6 * (|u| ^ 3 + 3 * |u|))
      = stdNormalPDF u + |γ| / 6 * (stdNormalPDF u * |u| ^ 3)
        + |γ| / 2 * (stdNormalPDF u * |u|) := by ring
  rw [hexp] at hkey
  linarith [hkey, hb0, e1, e3]

/-- **(E4).2 — the total-variation modulus of the Edgeworth density**, with a constant
independent of `n`. This is the hypothesis `hA` of
`abs_measure_Iic_sub_densityCDF_le_charFun`. -/
theorem setIntegral_abs_edgeworthDensity_le (γ : ℝ) {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (hab : a ≤ b) :
    (∫ y in Set.Ioc a b, |edgeworthDensity γ n y|)
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |γ|) * (b - a) := by
  calc (∫ y in Set.Ioc a b, |edgeworthDensity γ n y|)
      ≤ ∫ _y in Set.Ioc a b, (Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |γ|) :=
        setIntegral_mono_on (integrable_edgeworthDensity γ n).abs.integrableOn
          (continuous_const.integrableOn_Ioc) measurableSet_Ioc
          fun y _ => abs_edgeworthDensity_le γ hn y
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |γ|) * (b - a) := by
        rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_comm]

/-- **(E4).2 — the Fourier transform of the Edgeworth density.**
`∫ e^{ity} q_n(y) dy = e^{−t²/2}(1 − i γ t³ n^{-1/2}/6)`.

This is where (E2) is *used*: `integral_hermite3_mul_cexp_mul_gaussian` turns the Hermite factor
`u³ − 3u` into `(it)³`. The right-hand side is exactly the approximant estimated by
`norm_charFun_pow_sub_edgeworth_le` after the standardized substitution `s = t/(σ√n)`,
`v = σ²`, `m₃ = γσ³`: there `e^{−n v s²/2} = e^{−t²/2}` and `n i m₃ s³/6 = i γ t³/(6√n)`. -/
theorem charFunDensity_edgeworthDensity (γ : ℝ) (n : ℕ) (t : ℝ) :
    charFunDensity (edgeworthDensity γ n) t
      = Complex.exp (-(t : ℂ) ^ 2 / 2)
        * (1 - Complex.I * (γ : ℂ) * (t : ℂ) ^ 3
            * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) / 6) := by
  have hint1 : Integrable (fun u : ℝ =>
      Complex.exp ((t : ℂ) * (u : ℂ) * Complex.I) * Complex.exp (-(u : ℂ) ^ 2 / 2)) := by
    refine (integrable_cubic_mul_cexp_mul_gaussian t 0 0 0 1).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have hint2 : Integrable (fun u : ℝ => ((u : ℂ) ^ 3 - 3 * (u : ℂ)) *
      (Complex.exp ((t : ℂ) * (u : ℂ) * Complex.I) * Complex.exp (-(u : ℂ) ^ 2 / 2))) := by
    refine (integrable_cubic_mul_cexp_mul_gaussian t 1 0 (-3) 0).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have hcong : ∀ y : ℝ,
      Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * ((edgeworthDensity γ n y : ℝ) : ℂ)
      = (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) *
          ((((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) * (((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
              (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
                * Complex.exp (-(y : ℂ) ^ 2 / 2)))
            + Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
                * Complex.exp (-(y : ℂ) ^ 2 / 2)) := by
    intro y
    simp only [edgeworthDensity, stdNormalPDF]
    push_cast
    ring
  have hpull1 : (∫ y : ℝ, (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) *
        ((((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) * (((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
            (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
              * Complex.exp (-(y : ℂ) ^ 2 / 2)))
          + Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * Complex.exp (-(y : ℂ) ^ 2 / 2)))
      = (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) *
        ∫ y : ℝ, ((((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) * (((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
            (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
              * Complex.exp (-(y : ℂ) ^ 2 / 2)))
          + Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * Complex.exp (-(y : ℂ) ^ 2 / 2)) :=
    MeasureTheory.integral_const_mul _ _
  have hadd : (∫ y : ℝ, ((((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) * (((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
            (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
              * Complex.exp (-(y : ℂ) ^ 2 / 2)))
          + Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * Complex.exp (-(y : ℂ) ^ 2 / 2)))
      = (∫ y : ℝ, (((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) * (((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
            (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
              * Complex.exp (-(y : ℂ) ^ 2 / 2))))
        + ∫ y : ℝ, Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
            * Complex.exp (-(y : ℂ) ^ 2 / 2) :=
    integral_add (hint2.const_mul _) hint1
  have hpull2 : (∫ y : ℝ, (((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) * (((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
        (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * Complex.exp (-(y : ℂ) ^ 2 / 2))))
      = (((γ / 6 * (Real.sqrt n)⁻¹ : ℝ)) : ℂ) *
        ∫ y : ℝ, ((y : ℂ) ^ 3 - 3 * (y : ℂ)) *
          (Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * Complex.exp (-(y : ℂ) ^ 2 / 2)) :=
    MeasureTheory.integral_const_mul _ _
  rw [charFunDensity, integral_congr_ae (Filter.Eventually.of_forall hcong), hpull1, hadd,
    hpull2, integral_hermite3_mul_cexp_mul_gaussian, integral_cexp_mul_gaussian]
  have hS : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    exact_mod_cast hpos.ne'
  have hcube : ((t : ℂ) * Complex.I) ^ 3 = -(Complex.I * (t : ℂ) ^ 3) := by
    have hI3 : (Complex.I) ^ 3 = -Complex.I := by
      rw [pow_succ, Complex.I_sq]; ring
    rw [mul_pow, hI3]; ring
  rw [hcube]
  push_cast
  field_simp
  ring

/-- **(E4).4 — the Gaussian tail of the Edgeworth characteristic function.**
`‖φ_{q_n}(θ)‖ ≤ e^{−θ²/2}(1 + |γ||θ|³/6)`, uniformly in `n ≥ 1`. This is the second half of
the outer-range estimate: on `|ξ| ≥ ρ_n ≍ √n` the right-hand side is `e^{−2π²c²n}` up to a
polynomial factor, hence geometric in `n`. -/
theorem norm_charFunDensity_edgeworthDensity_le (γ : ℝ) {n : ℕ} (hn : 1 ≤ n) (θ : ℝ) :
    ‖charFunDensity (edgeworthDensity γ n) θ‖
      ≤ Real.exp (-θ ^ 2 / 2) * (1 + |γ| * |θ| ^ 3 / 6) := by
  have hsqrt0 : (0 : ℝ) ≤ (Real.sqrt n)⁻¹ := by positivity
  have hsqrt : (Real.sqrt n)⁻¹ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt h1)
  have hexp : Complex.exp (-(θ : ℂ) ^ 2 / 2) = ((Real.exp (-θ ^ 2 / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hterm : ‖Complex.I * (γ : ℂ) * (θ : ℂ) ^ 3 * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) / 6‖
      = |γ| * |θ| ^ 3 * (Real.sqrt n)⁻¹ / 6 := by
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg hsqrt0]
    norm_num
  rw [charFunDensity_edgeworthDensity, norm_mul, hexp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hnn : (0 : ℝ) ≤ |γ| * |θ| ^ 3 := by positivity
  calc ‖1 - Complex.I * (γ : ℂ) * (θ : ℂ) ^ 3 * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) / 6‖
      ≤ ‖(1 : ℂ)‖ + ‖Complex.I * (γ : ℂ) * (θ : ℂ) ^ 3 * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) / 6‖ :=
        norm_sub_le _ _
    _ = 1 + |γ| * |θ| ^ 3 * (Real.sqrt n)⁻¹ / 6 := by rw [norm_one, hterm]
    _ ≤ 1 + |γ| * |θ| ^ 3 / 6 := by nlinarith

/-- **(E4).4 — the Gaussian tail of the Edgeworth characteristic function, off a window.**
On `ρ ≤ |ξ|` the bound of `norm_charFunDensity_edgeworthDensity_le` at `θ = −2πξ` is at most
`(1 + 512π³|γ|) e^{−π²ρ²}`: half of the Gaussian factor absorbs the cubic polynomial (through
`exp_neg_half_sq_mul_abs_pow_le`), and the other half is monotone in `|ξ|`. With `ρ = c√n`
the right-hand side is geometric in `n`, which is what the outer range needs. -/
private lemma edgeworthCharFun_tail_le (γ : ℝ) {ρ ξ : ℝ} (hρ : 0 ≤ ρ) (hξ : ρ ≤ |ξ|) :
    Real.exp (-(2 * Real.pi * ξ) ^ 2 / 2) * (1 + |γ| * |2 * Real.pi * ξ| ^ 3 / 6)
      ≤ (1 + 512 * Real.pi ^ 3 * |γ|) * Real.exp (-(Real.pi ^ 2 * ρ ^ 2)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have habs : |2 * Real.pi * ξ| ^ 3 = 8 * Real.pi ^ 3 * |ξ| ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hπ]
    ring
  have hsplit : Real.exp (-(2 * Real.pi * ξ) ^ 2 / 2)
      = Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) * Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsq : ρ ^ 2 ≤ ξ ^ 2 := by
    have h := sq_abs ξ
    nlinarith [abs_nonneg ξ]
  have h1 : Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) ≤ Real.exp (-(Real.pi ^ 2 * ρ ^ 2)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hcube : Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) * |ξ| ^ 3 ≤ 384 := by
    have hmono : Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) ≤ Real.exp (-ξ ^ 2 / 2) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [sq_nonneg ξ]
    have hstep := mul_le_mul_of_nonneg_right hmono (by positivity : (0 : ℝ) ≤ |ξ| ^ 3)
    have hgauss := exp_neg_half_sq_mul_abs_pow_le 3 ξ
    have hval : (4 : ℝ) ^ 3 * (Nat.factorial 3 : ℝ) = 384 := by norm_num [Nat.factorial]
    rw [hval] at hgauss
    linarith
  have hone : Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ξ])
  have h2 : Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) * (1 + |γ| * |2 * Real.pi * ξ| ^ 3 / 6)
      ≤ 1 + 512 * Real.pi ^ 3 * |γ| := by
    rw [habs]
    have hexpand : Real.exp (-(Real.pi ^ 2 * ξ ^ 2))
          * (1 + |γ| * (8 * Real.pi ^ 3 * |ξ| ^ 3) / 6)
        = Real.exp (-(Real.pi ^ 2 * ξ ^ 2))
          + (4 * Real.pi ^ 3 * |γ| / 3) * (Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) * |ξ| ^ 3) := by
      ring
    rw [hexpand]
    have hc : (4 * Real.pi ^ 3 * |γ| / 3) * (Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) * |ξ| ^ 3)
        ≤ (4 * Real.pi ^ 3 * |γ| / 3) * 384 :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    nlinarith
  calc Real.exp (-(2 * Real.pi * ξ) ^ 2 / 2) * (1 + |γ| * |2 * Real.pi * ξ| ^ 3 / 6)
      = Real.exp (-(Real.pi ^ 2 * ξ ^ 2))
          * (Real.exp (-(Real.pi ^ 2 * ξ ^ 2)) * (1 + |γ| * |2 * Real.pi * ξ| ^ 3 / 6)) := by
        rw [hsplit]; ring
    _ ≤ Real.exp (-(Real.pi ^ 2 * ρ ^ 2)) * (1 + 512 * Real.pi ^ 3 * |γ|) :=
        mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    _ = (1 + 512 * Real.pi ^ 3 * |γ|) * Real.exp (-(Real.pi ^ 2 * ρ ^ 2)) := by ring

/-- The standard normal distribution function takes values in `[0, 1]`. -/
private lemma abs_stdNormalCDF_le_one (u : ℝ) : |stdNormalCDF u| ≤ 1 := by
  have hnn : (0 : ℝ) ≤ stdNormalCDF u := ENNReal.toReal_nonneg
  have hle : (gaussianReal 0 1 (Set.Iic u)).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by simp) (prob_le_one (μ := gaussianReal 0 1))
  rw [abs_of_nonneg hnn]
  exact hle

/-- **A uniform bound on the Edgeworth approximant**, `|Φ(u) − (γ/6)φ(u)(u² − 1)n^{-1/2}|
≤ 1 + 6|γ|`, with an `n`-free constant. Its only role in the assembly is to absorb the finitely
many small `n` at which the damping factor of the window estimate is not yet available. -/
theorem abs_edgeworthCDF_le (γ : ℝ) {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    |edgeworthCDF γ n u| ≤ 1 + 6 * |γ| := by
  have hpdfnn : 0 ≤ stdNormalPDF u := by rw [stdNormalPDF]; positivity
  have hsqrt0 : (0 : ℝ) ≤ (Real.sqrt n)⁻¹ := by positivity
  have hsqrt : (Real.sqrt n)⁻¹ ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt h1)
  have hb0 := stdNormalPDF_mul_abs_pow_le 0 (C := 1) (by norm_num) u
  have hb2 := stdNormalPDF_mul_abs_pow_le 2 (C := 32) (by norm_num [Nat.factorial]) u
  rw [pow_zero, mul_one, mul_one] at hb0
  rw [sq_abs] at hb2
  have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      have : Real.sqrt 4 ≤ Real.sqrt (2 * Real.pi) :=
        Real.sqrt_le_sqrt (by nlinarith [Real.two_le_pi])
      rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hinvnn : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hprod : |stdNormalPDF u * (u ^ 2 - 1)| ≤ 33 * (Real.sqrt (2 * Real.pi))⁻¹ := by
    have hexp : stdNormalPDF u * (u ^ 2 - 1)
        = stdNormalPDF u * u ^ 2 - stdNormalPDF u := by ring
    have hu2 : (0 : ℝ) ≤ stdNormalPDF u * u ^ 2 := by positivity
    rw [hexp, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hterm : |1 / 6 * γ * stdNormalPDF u * (u ^ 2 - 1) * (Real.sqrt n)⁻¹| ≤ 6 * |γ| := by
    have hrw : |1 / 6 * γ * stdNormalPDF u * (u ^ 2 - 1) * (Real.sqrt n)⁻¹|
        = |γ| / 6 * |stdNormalPDF u * (u ^ 2 - 1)| * (Real.sqrt n)⁻¹ := by
      rw [show 1 / 6 * γ * stdNormalPDF u * (u ^ 2 - 1) * (Real.sqrt n)⁻¹
            = (γ / 6) * (stdNormalPDF u * (u ^ 2 - 1)) * (Real.sqrt n)⁻¹ from by ring,
        abs_mul, abs_mul, abs_div, abs_of_nonneg hsqrt0]
      norm_num
    rw [hrw]
    have hnn : (0 : ℝ) ≤ |γ| / 6 * |stdNormalPDF u * (u ^ 2 - 1)| := by positivity
    have hstep : |γ| / 6 * |stdNormalPDF u * (u ^ 2 - 1)| * (Real.sqrt n)⁻¹
        ≤ |γ| / 6 * (33 * (Real.sqrt (2 * Real.pi))⁻¹) := by
      calc |γ| / 6 * |stdNormalPDF u * (u ^ 2 - 1)| * (Real.sqrt n)⁻¹
          ≤ |γ| / 6 * |stdNormalPDF u * (u ^ 2 - 1)| * 1 :=
            mul_le_mul_of_nonneg_left hsqrt hnn
        _ = |γ| / 6 * |stdNormalPDF u * (u ^ 2 - 1)| := mul_one _
        _ ≤ |γ| / 6 * (33 * (Real.sqrt (2 * Real.pi))⁻¹) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
    have hgnn : (0 : ℝ) ≤ |γ| := abs_nonneg γ
    have hkey := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ 33 * (|γ| / 6))
    linarith
  rw [edgeworthCDF]
  have htri : |stdNormalCDF u - 1 / 6 * γ * stdNormalPDF u * (u ^ 2 - 1) * (Real.sqrt n)⁻¹|
      ≤ |stdNormalCDF u|
        + |1 / 6 * γ * stdNormalPDF u * (u ^ 2 - 1) * (Real.sqrt n)⁻¹| := by
    have h := abs_add_le (stdNormalCDF u)
      (-(1 / 6 * γ * stdNormalPDF u * (u ^ 2 - 1) * (Real.sqrt n)⁻¹))
    rw [abs_neg] at h
    rw [sub_eq_add_neg]
    exact h
  linarith [abs_stdNormalCDF_le_one u, htri, hterm]

/-- The Edgeworth total-variation constant is positive. -/
lemma edgeworthTV_pos (γ : ℝ) : 0 < (Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |γ|) := by
  have h : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hg : (0 : ℝ) ≤ |γ| := abs_nonneg γ
  positivity

end Approximant

/-! ## The window estimate: elementary envelopes

Item (E4).3 of the assembly programme needs, before anything analytic, two elementary
ingredients: the Gaussian envelope `e^{−π²ξ²/2}(|ξ|⁴ + |ξ|⁸)` that the damped expansion
produces on the window, and the algebraic normalisation that turns the bound of
`norm_charFun_pow_sub_edgeworth_le` into `K n^{-1}` times that envelope. Both are recorded
here; neither mentions a measure. -/

section WindowEnvelope

/-- Monomials of intermediate degree are dominated by the two extreme ones. -/
private lemma pow_le_pow_four_add_eight {p : ℝ} (hp : 0 ≤ p) {k : ℕ}
    (h4 : 4 ≤ k) (h8 : k ≤ 8) : p ^ k ≤ p ^ 4 + p ^ 8 := by
  rcases le_total p 1 with h | h
  · have hk : p ^ k ≤ p ^ 4 := pow_le_pow_of_le_one hp h h4
    have : (0 : ℝ) ≤ p ^ 8 := pow_nonneg hp 8
    linarith
  · have hk : p ^ k ≤ p ^ 8 := pow_le_pow_right₀ h h8
    have : (0 : ℝ) ≤ p ^ 4 := pow_nonneg hp 4
    linarith

/-- The Gaussian envelope of the window estimate. -/
private noncomputable def windowEnvelope (ξ : ℝ) : ℝ :=
  Real.exp (-(Real.pi ^ 2 * ξ ^ 2 / 2)) * (|ξ| ^ 4 + |ξ| ^ 8)

/-- The envelope after the Esseen weight has been applied. -/
private noncomputable def windowDom (ξ : ℝ) : ℝ :=
  Real.exp (-(Real.pi ^ 2 * ξ ^ 2 / 2)) * (|ξ| ^ 3 + |ξ| ^ 7) * (Real.pi)⁻¹

private lemma windowEnvelope_nonneg (ξ : ℝ) : 0 ≤ windowEnvelope ξ := by
  unfold windowEnvelope; positivity

private lemma windowDom_nonneg (ξ : ℝ) : 0 ≤ windowDom ξ := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  unfold windowDom; positivity

private lemma windowEnvelope_mul_weight (ξ : ℝ) :
    windowEnvelope ξ * (1 / (Real.pi * |ξ|)) = windowDom ξ := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases eq_or_ne ξ 0 with rfl | h
  · simp [windowEnvelope, windowDom]
  · have hx : |ξ| ≠ 0 := abs_ne_zero.2 h
    have hsplit : |ξ| ^ 4 + |ξ| ^ 8 = (|ξ| ^ 3 + |ξ| ^ 7) * |ξ| := by ring
    unfold windowEnvelope windowDom
    rw [hsplit]
    field_simp

private lemma integrable_windowDom : Integrable windowDom := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h3 := integrable_abs_pow_mul_exp_neg_half_sq 3
  have h7 := integrable_abs_pow_mul_exp_neg_half_sq 7
  have hg : Integrable (fun ξ : ℝ =>
      (|ξ| ^ 3 * Real.exp (-(ξ ^ 2 / 2)) + |ξ| ^ 7 * Real.exp (-(ξ ^ 2 / 2)))
        * (Real.pi)⁻¹) := (h3.add h7).mul_const _
  refine Integrable.mono' hg (by unfold windowDom; fun_prop)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (windowDom_nonneg ξ)]
  have hexp : Real.exp (-(Real.pi ^ 2 * ξ ^ 2 / 2)) ≤ Real.exp (-(ξ ^ 2 / 2)) := by
    refine Real.exp_le_exp.2 ?_
    have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi, Real.pi_pos]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.pi ^ 2 - 4) (sq_nonneg ξ),
      sq_nonneg ξ]
  have hnn : (0 : ℝ) ≤ |ξ| ^ 3 + |ξ| ^ 7 := by positivity
  have hmul : Real.exp (-(Real.pi ^ 2 * ξ ^ 2 / 2)) * (|ξ| ^ 3 + |ξ| ^ 7)
      ≤ |ξ| ^ 3 * Real.exp (-(ξ ^ 2 / 2)) + |ξ| ^ 7 * Real.exp (-(ξ ^ 2 / 2)) := by
    have := mul_le_mul_of_nonneg_right hexp hnn
    nlinarith [this]
  unfold windowDom
  exact mul_le_mul_of_nonneg_right hmul (by positivity)

private lemma add_sq_le_two_mul (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

set_option maxHeartbeats 2000000 in
-- The `field_simp`/`linear_combination` normalisations below run over a degree-8 rational
-- expression in six variables; the default heartbeat budget is not enough.
/-- **The algebraic core of the window estimate.** -/
private lemma exists_window_core (ρ β M σ : ℝ) (hρ : 0 ≤ ρ) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hσ : 0 < σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ p τ N : ℝ, 0 ≤ p → 0 < τ → τ ≤ 1 → N * τ ^ 2 = 1 → 1 ≤ N →
      N * (N - 1) / 2 * (ρ * (2 * Real.pi * p * τ / σ) ^ 3 / 6
            + (4 * Real.pi ^ 2 * p ^ 2 * τ ^ 2 / 2) ^ 2 / 2) ^ 2
          + N * ((4 * Real.pi ^ 2 * p ^ 2 * τ ^ 2 / 2)
              * (M * (2 * Real.pi * p * τ / σ) ^ 3 / 6)
            + (β * (2 * Real.pi * p * τ / σ) ^ 4 / 24
              + (4 * Real.pi ^ 2 * p ^ 2 * τ ^ 2 / 2) ^ 2 / 2))
        ≤ K * τ ^ 2 * (p ^ 4 + p ^ 8) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hσ0 : σ ≠ 0 := hσ.ne'
  set A : ℝ := 4 * Real.pi ^ 3 * ρ / (3 * σ ^ 3) with hAdef
  set B : ℝ := 2 * Real.pi ^ 4 with hBdef
  set C : ℝ := 8 * Real.pi ^ 5 * M / (3 * σ ^ 3) with hCdef
  set D : ℝ := 2 * Real.pi ^ 4 * β / (3 * σ ^ 4) + 2 * Real.pi ^ 4 with hDdef
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  have hC : 0 ≤ C := by rw [hCdef]; positivity
  have hD : 0 ≤ D := by rw [hDdef]; positivity
  refine ⟨A ^ 2 + B ^ 2 + C + D + 1, by positivity, ?_⟩
  intro p τ N hp hτ hτ1 hN hN1
  have hτ0 : τ ≠ 0 := hτ.ne'
  have e1 : ρ * (2 * Real.pi * p * τ / σ) ^ 3 / 6
        + (4 * Real.pi ^ 2 * p ^ 2 * τ ^ 2 / 2) ^ 2 / 2
      = A * (p ^ 3 * τ ^ 3) + B * (p ^ 4 * τ ^ 4) := by
    rw [hAdef, hBdef]; field_simp; ring
  have e2 : (4 * Real.pi ^ 2 * p ^ 2 * τ ^ 2 / 2) * (M * (2 * Real.pi * p * τ / σ) ^ 3 / 6)
        + (β * (2 * Real.pi * p * τ / σ) ^ 4 / 24
          + (4 * Real.pi ^ 2 * p ^ 2 * τ ^ 2 / 2) ^ 2 / 2)
      = C * (p ^ 5 * τ ^ 5) + D * (p ^ 4 * τ ^ 4) := by
    rw [hCdef, hDdef]; field_simp; ring
  rw [e1, e2]
  have hN2 : N ^ 2 * τ ^ 4 = 1 := by
    calc N ^ 2 * τ ^ 4 = (N * τ ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hN]; ring
  have h6 : N ^ 2 * τ ^ 6 = τ ^ 2 := by
    calc N ^ 2 * τ ^ 6 = (N ^ 2 * τ ^ 4) * τ ^ 2 := by ring
      _ = τ ^ 2 := by rw [hN2]; ring
  have h8 : N ^ 2 * τ ^ 8 = τ ^ 4 := by
    calc N ^ 2 * τ ^ 8 = (N ^ 2 * τ ^ 4) * τ ^ 4 := by ring
      _ = τ ^ 4 := by rw [hN2]; ring
  have h5 : N * τ ^ 5 = τ ^ 3 := by
    calc N * τ ^ 5 = (N * τ ^ 2) * τ ^ 3 := by ring
      _ = τ ^ 3 := by rw [hN]; ring
  have h4 : N * τ ^ 4 = τ ^ 2 := by
    calc N * τ ^ 4 = (N * τ ^ 2) * τ ^ 2 := by ring
      _ = τ ^ 2 := by rw [hN]; ring
  -- the squared term
  have hsq : (A * (p ^ 3 * τ ^ 3) + B * (p ^ 4 * τ ^ 4)) ^ 2
      ≤ 2 * (A * (p ^ 3 * τ ^ 3)) ^ 2 + 2 * (B * (p ^ 4 * τ ^ 4)) ^ 2 :=
    add_sq_le_two_mul _ _
  have hNN : N * (N - 1) / 2 ≤ N ^ 2 / 2 := by nlinarith
  have hpos : (0 : ℝ) ≤ (A * (p ^ 3 * τ ^ 3) + B * (p ^ 4 * τ ^ 4)) ^ 2 := sq_nonneg _
  have hterm1 : N * (N - 1) / 2 * (A * (p ^ 3 * τ ^ 3) + B * (p ^ 4 * τ ^ 4)) ^ 2
      ≤ N ^ 2 / 2 * (2 * (A * (p ^ 3 * τ ^ 3)) ^ 2 + 2 * (B * (p ^ 4 * τ ^ 4)) ^ 2) := by
    refine mul_le_mul hNN hsq hpos (by positivity)
  have hterm1' : N ^ 2 / 2 * (2 * (A * (p ^ 3 * τ ^ 3)) ^ 2 + 2 * (B * (p ^ 4 * τ ^ 4)) ^ 2)
      = A ^ 2 * p ^ 6 * τ ^ 2 + B ^ 2 * p ^ 8 * τ ^ 4 := by
    linear_combination (A ^ 2 * p ^ 6) * h6 + (B ^ 2 * p ^ 8) * h8
  have hterm2 : N * (C * (p ^ 5 * τ ^ 5) + D * (p ^ 4 * τ ^ 4))
      = C * p ^ 5 * τ ^ 3 + D * p ^ 4 * τ ^ 2 := by
    linear_combination (C * p ^ 5) * h5 + (D * p ^ 4) * h4
  rw [hterm2]
  -- monomial bounds
  have hp4 : (0 : ℝ) ≤ p ^ 4 := pow_nonneg hp 4
  have hp8 : (0 : ℝ) ≤ p ^ 8 := pow_nonneg hp 8
  have hPnn : (0 : ℝ) ≤ p ^ 4 + p ^ 8 := by linarith
  have hτ2 : (0 : ℝ) ≤ τ ^ 2 := sq_nonneg τ
  have hτ3 : τ ^ 3 ≤ τ ^ 2 := by nlinarith
  have hτ4 : τ ^ 4 ≤ τ ^ 2 := by nlinarith
  have key : ∀ a x y : ℝ, 0 ≤ a → 0 ≤ x → x ≤ p ^ 4 + p ^ 8 → 0 ≤ y → y ≤ τ ^ 2 →
      a * x * y ≤ a * (p ^ 4 + p ^ 8) * τ ^ 2 := by
    intro a x y ha hx0 hx hy0 hy
    have h1 : a * x ≤ a * (p ^ 4 + p ^ 8) := mul_le_mul_of_nonneg_left hx ha
    calc a * x * y ≤ a * x * τ ^ 2 := mul_le_mul_of_nonneg_left hy (by positivity)
      _ ≤ a * (p ^ 4 + p ^ 8) * τ ^ 2 := mul_le_mul_of_nonneg_right h1 hτ2
  have k1 := key (A ^ 2) (p ^ 6) (τ ^ 2) (by positivity) (by positivity)
    (pow_le_pow_four_add_eight hp (by norm_num) (by norm_num)) hτ2 le_rfl
  have k2 := key (B ^ 2) (p ^ 8) (τ ^ 4) (by positivity) hp8 (by linarith) (by positivity) hτ4
  have k3 := key C (p ^ 5) (τ ^ 3) hC (by positivity)
    (pow_le_pow_four_add_eight hp (by norm_num) (by norm_num)) (by positivity) hτ3
  have k4 := key D (p ^ 4) (τ ^ 2) hD hp4 (by linarith) hτ2 le_rfl
  have hfinal : A ^ 2 * (p ^ 4 + p ^ 8) * τ ^ 2 + B ^ 2 * (p ^ 4 + p ^ 8) * τ ^ 2
      + C * (p ^ 4 + p ^ 8) * τ ^ 2 + D * (p ^ 4 + p ^ 8) * τ ^ 2
      ≤ (A ^ 2 + B ^ 2 + C + D + 1) * τ ^ 2 * (p ^ 4 + p ^ 8) := by nlinarith
  calc N * (N - 1) / 2 * (A * (p ^ 3 * τ ^ 3) + B * (p ^ 4 * τ ^ 4)) ^ 2
        + (C * p ^ 5 * τ ^ 3 + D * p ^ 4 * τ ^ 2)
      ≤ (A ^ 2 * p ^ 6 * τ ^ 2 + B ^ 2 * p ^ 8 * τ ^ 4)
        + (C * p ^ 5 * τ ^ 3 + D * p ^ 4 * τ ^ 2) := by
        rw [← hterm1']; linarith
    _ ≤ (A ^ 2 + B ^ 2 + C + D + 1) * τ ^ 2 * (p ^ 4 + p ^ 8) := by linarith

end WindowEnvelope

/-! ## The window estimate: the geometry of the argument

On the window the damped expansion `norm_charFun_pow_sub_edgeworth_le` is applied at
`s = τ σ⁻¹ θ` with `θ = −2πξ` and `τ = n^{-1/2}`. The three lemmas below record the modulus
and the square of that argument, and check the two window conditions `v s² ≤ 2`,
`ρ₃|s| ≤ 3v/2` from a single bound `|ξ| τ ≤ c`. -/

section WindowArgument

/-- The modulus of the Edgeworth argument `s = −2πξ/(σ√n)`. -/
private lemma abs_window_arg {σ ξ τ : ℝ} (hσ : 0 < σ) (hτ : 0 ≤ τ) :
    |τ * (σ⁻¹ * (-(2 * Real.pi * ξ)))| = 2 * Real.pi * |ξ| * τ / σ := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [abs_mul, abs_mul, abs_of_nonneg hτ, abs_inv, abs_of_pos hσ, abs_neg, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  field_simp

/-- The square of the Edgeworth argument, weighted by the variance. -/
private lemma sq_window_arg {σ ξ τ : ℝ} (hσ : 0 < σ) :
    σ ^ 2 * (τ * (σ⁻¹ * (-(2 * Real.pi * ξ)))) ^ 2 = 4 * Real.pi ^ 2 * |ξ| ^ 2 * τ ^ 2 := by
  have h : |ξ| ^ 2 = ξ ^ 2 := sq_abs ξ
  rw [h]
  field_simp
  ring

/-- **The two window conditions of the damped expansion**, from a single bound on `|ξ| τ`. -/
private lemma window_conditions {σ ρ c ξ τ : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (hc2 : c ≤ 1 / (Real.pi * Real.sqrt 2))
    (hc3 : c ≤ 3 * σ ^ 3 / (4 * Real.pi * (ρ + 1)))
    (hξ : |ξ| * τ ≤ c) :
    σ ^ 2 * (τ * (σ⁻¹ * (-(2 * Real.pi * ξ)))) ^ 2 ≤ 2
      ∧ ρ * |τ * (σ⁻¹ * (-(2 * Real.pi * ξ)))| ≤ 3 * σ ^ 2 / 2 := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hx0 : (0 : ℝ) ≤ |ξ| * τ := by positivity
  have hc0 : (0 : ℝ) ≤ c := le_trans hx0 hξ
  constructor
  · rw [sq_window_arg hσ]
    have hroot : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hrootp : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hcsq : c ^ 2 ≤ 1 / (2 * Real.pi ^ 2) := by
      have h2 : c ^ 2 ≤ (1 / (Real.pi * Real.sqrt 2)) ^ 2 := by nlinarith
      have h3 : (1 / (Real.pi * Real.sqrt 2)) ^ 2 = 1 / (2 * Real.pi ^ 2) := by
        rw [div_pow, mul_pow, hroot, one_pow]
        ring
      linarith
    have hxsq : (|ξ| * τ) ^ 2 ≤ c ^ 2 := by nlinarith
    have heq : 4 * Real.pi ^ 2 * |ξ| ^ 2 * τ ^ 2 = 4 * Real.pi ^ 2 * (|ξ| * τ) ^ 2 := by ring
    rw [heq]
    have hstep : 4 * Real.pi ^ 2 * (|ξ| * τ) ^ 2 ≤ 4 * Real.pi ^ 2 * (1 / (2 * Real.pi ^ 2)) :=
      mul_le_mul_of_nonneg_left (le_trans hxsq hcsq) (by positivity)
    have hval : 4 * Real.pi ^ 2 * (1 / (2 * Real.pi ^ 2)) = 2 := by field_simp; ring
    linarith
  · rw [abs_window_arg hσ hτ]
    have hkey : ρ * (2 * Real.pi * |ξ| * τ / σ) = 2 * Real.pi * ρ / σ * (|ξ| * τ) := by
      field_simp
    rw [hkey]
    have hcoef : (0 : ℝ) ≤ 2 * Real.pi * ρ / σ := by positivity
    have step1 : 2 * Real.pi * ρ / σ * (|ξ| * τ) ≤ 2 * Real.pi * ρ / σ * c :=
      mul_le_mul_of_nonneg_left hξ hcoef
    have step2 : 2 * Real.pi * ρ / σ * c
        ≤ 2 * Real.pi * ρ / σ * (3 * σ ^ 3 / (4 * Real.pi * (ρ + 1))) :=
      mul_le_mul_of_nonneg_left hc3 hcoef
    have step3 : 2 * Real.pi * ρ / σ * (3 * σ ^ 3 / (4 * Real.pi * (ρ + 1)))
        = 3 * σ ^ 2 / 2 * (ρ / (ρ + 1)) := by
      have hρ1 : ρ + 1 ≠ 0 := by positivity
      field_simp
      ring
    have step4 : 3 * σ ^ 2 / 2 * (ρ / (ρ + 1)) ≤ 3 * σ ^ 2 / 2 := by
      have hr : ρ / (ρ + 1) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      nlinarith [sq_nonneg σ]
    linarith

/-- **The Edgeworth approximant in damped form.** The comparison object produced by
`charFunDensity_edgeworthDensity` is *literally* the approximant estimated by
`norm_charFun_pow_sub_edgeworth_le` at `s = τ σ⁻¹ θ`, `v = σ²`, `m₃ = γσ³`: the Gaussian
factors agree because `n v s² = θ²`, and the linear corrections because `n τ³ = τ`. -/
private lemma edgeworth_approx_eq (γ σ θ : ℝ) (hσ : σ ≠ 0) (m : ℕ) (τ : ℝ)
    (hτ : ((m : ℝ) + 2) * τ ^ 2 = 1) :
    Complex.exp (-(θ : ℂ) ^ 2 / 2)
        * (1 - Complex.I * (γ : ℂ) * (θ : ℂ) ^ 3 * ((τ : ℝ) : ℂ) / 6)
      = ((Real.exp (-(σ ^ 2 * (τ * (σ⁻¹ * θ)) ^ 2 / 2)) : ℝ) : ℂ) ^ (m + 2)
        * (1 - ((m : ℂ) + 2) * Complex.I * ((γ * σ ^ 3 : ℝ) : ℂ)
            * ((τ * (σ⁻¹ * θ) : ℝ) : ℂ) ^ 3 / 6) := by
  have hσ3 : σ ^ 3 ≠ 0 := pow_ne_zero 3 hσ
  have hvs : σ ^ 2 * (τ * (σ⁻¹ * θ)) ^ 2 = θ ^ 2 * τ ^ 2 := by field_simp
  have hgauss : ((Real.exp (-(σ ^ 2 * (τ * (σ⁻¹ * θ)) ^ 2 / 2)) : ℝ) : ℂ) ^ (m + 2)
      = Complex.exp (-(θ : ℂ) ^ 2 / 2) := by
    have hreal : Real.exp (-(σ ^ 2 * (τ * (σ⁻¹ * θ)) ^ 2 / 2)) ^ (m + 2)
        = Real.exp (-(θ ^ 2 / 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [hvs]
      push_cast
      linear_combination (-(θ ^ 2) / 2) * hτ
    calc ((Real.exp (-(σ ^ 2 * (τ * (σ⁻¹ * θ)) ^ 2 / 2)) : ℝ) : ℂ) ^ (m + 2)
        = ((Real.exp (-(σ ^ 2 * (τ * (σ⁻¹ * θ)) ^ 2 / 2)) ^ (m + 2) : ℝ) : ℂ) := by push_cast; ring
      _ = ((Real.exp (-(θ ^ 2 / 2)) : ℝ) : ℂ) := by rw [hreal]
      _ = Complex.exp (-(θ : ℂ) ^ 2 / 2) := by
          rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  have hN3 : ((m : ℝ) + 2) * τ ^ 3 = τ := by
    calc ((m : ℝ) + 2) * τ ^ 3 = (((m : ℝ) + 2) * τ ^ 2) * τ := by ring
      _ = τ := by rw [hτ]; ring
  have hlin : γ * θ ^ 3 * τ = ((m : ℝ) + 2) * (γ * σ ^ 3) * (τ * (σ⁻¹ * θ)) ^ 3 := by
    have hexp : ((m : ℝ) + 2) * (γ * σ ^ 3) * (τ * (σ⁻¹ * θ)) ^ 3
        = γ * θ ^ 3 * (((m : ℝ) + 2) * τ ^ 3) * (σ ^ 3 * σ⁻¹ ^ 3) := by ring
    have hinv : σ ^ 3 * σ⁻¹ ^ 3 = 1 := by field_simp
    rw [hexp, hN3, hinv]
    ring
  have hlinC : (γ : ℂ) * (θ : ℂ) ^ 3 * ((τ : ℝ) : ℂ)
      = (((m : ℝ) + 2 : ℝ) : ℂ) * ((γ * σ ^ 3 : ℝ) : ℂ) * ((τ * (σ⁻¹ * θ) : ℝ) : ℂ) ^ 3 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hlin
    push_cast at this ⊢
    linear_combination this
  rw [hgauss]
  congr 1
  push_cast at hlinC ⊢
  linear_combination (-Complex.I / 6) * hlinC

end WindowArgument

/-! ## The window estimate itself

Item (E4).3. On `|ξ| ≤ c√n` the damped expansion applies, and everything it produces is
`K n⁻¹` times the Gaussian envelope `windowEnvelope`: the polynomial part by the algebraic
core `exists_window_core`, and the damping factor `e^{−(n−2)vs²/4} = e^{−(1 − 2/n)π²ξ²}` by
`n ≥ 4`, which is where the finitely many small `n` are shed. -/

section WindowEstimate

set_option maxHeartbeats 1600000 in
-- The `ring`/`rw` normalisations below run over the degree-8 rational bound produced by
-- `norm_charFun_pow_sub_edgeworth_le`; the default heartbeat budget is not enough.
/-- **(E4).3 — the window estimate.** For `n ≥ 4` and `|ξ|/√n ≤ c`, the characteristic-function
difference that Esseen's inequality integrates is at most `K n⁻¹ · windowEnvelope ξ`, with a
constant `K` depending only on the sampling law. The two hypotheses on `c` are exactly the ones
`window_conditions` needs in order to certify the window of
`norm_charFun_pow_sub_edgeworth_le`. -/
private lemma exists_window_bound (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF4 : MemLp (fun t : ℝ => t) 4 F) (hFvar : 0 < Var[fun t : ℝ => t; F])
    {c : ℝ} (hc2 : c ≤ 1 / (Real.pi * Real.sqrt 2))
    (hc3 : c ≤ 3 * Real.sqrt Var[fun t : ℝ => t; F] ^ 3
      / (4 * Real.pi * ((∫ x, |x| ^ 3 ∂(centredLaw F)) + 1))) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 4 ≤ n → ∀ ξ : ℝ, |ξ| * (Real.sqrt n)⁻¹ ≤ c →
      ‖charFun (stdRootLaw F n) (-(2 * Real.pi * ξ))
          - charFunDensity (edgeworthDensity (skewness F) n) (-(2 * Real.pi * ξ))‖
        ≤ K / n * windowEnvelope ξ := by
  have hσ : 0 < Real.sqrt Var[fun t : ℝ => t; F] := Real.sqrt_pos.2 hFvar
  have hρ0 : (0 : ℝ) ≤ ∫ x, |x| ^ 3 ∂(centredLaw F) :=
    integral_nonneg fun x => by positivity
  have hβ0 : (0 : ℝ) ≤ ∫ x, x ^ 4 ∂(centredLaw F) :=
    integral_nonneg fun x => by positivity
  have hFint : Integrable (fun t : ℝ => t) F := hF4.integrable (by norm_num)
  have hvar : (∫ x, x ^ 2 ∂(centredLaw F)) = Real.sqrt Var[fun t : ℝ => t; F] ^ 2 := by
    rw [integral_sq_centredLaw, Real.sq_sqrt hFvar.le]
  have hthird : (∫ x, x ^ 3 ∂(centredLaw F))
      = skewness F * Real.sqrt Var[fun t : ℝ => t; F] ^ 3 :=
    integral_cube_centredLaw F hFvar
  obtain ⟨K, hK0, hK⟩ := exists_window_core (∫ x, |x| ^ 3 ∂(centredLaw F))
    (∫ x, x ^ 4 ∂(centredLaw F)) |skewness F * Real.sqrt Var[fun t : ℝ => t; F] ^ 3|
    (Real.sqrt Var[fun t : ℝ => t; F]) hρ0 hβ0 (abs_nonneg _) hσ
  refine ⟨K, hK0, ?_⟩
  intro n hn ξ hξ
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 ≤ m)
  have hNR : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hNpos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by rw [hNR]; positivity
  have hτ0 : (0 : ℝ) < (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ := by positivity
  have hτ2 : ((Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹) ^ 2 = (((m + 2 : ℕ) : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hNpos.le]
  have hτeq : ((m : ℝ) + 2) * ((Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹) ^ 2 = 1 := by
    rw [hτ2, ← hNR]
    field_simp
  have hτ1 : (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ ≤ 1 := by
    refine inv_le_one_of_one_le₀ ?_
    have h1 : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by rw [hNR]; linarith
    simpa using Real.sqrt_le_sqrt h1
  have hwc := window_conditions hσ hρ0 hτ0.le hc2 hc3 hξ
  have hbound := norm_charFun_pow_sub_edgeworth_le (centredLaw F)
    (integrable_id_centredLaw F hF4) (integrable_sq_centredLaw F hF4)
    (integrable_abs_cube_centredLaw F hF4) (integrable_pow_four_centredLaw F hF4)
    (integral_id_centredLaw F hFint) hvar hthird hwc.1 hwc.2 m
  have hBIGnn := nonneg_of_mul_nonneg_right ((norm_nonneg _).trans hbound)
    (pow_pos (Real.exp_pos _) m)
  have hsq := sq_window_arg (ξ := ξ) (τ := (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹) hσ
  have habs := abs_window_arg (ξ := ξ) hσ hτ0.le
  rw [charFun_stdRootLaw F (by omega : 0 < m + 2), charFunDensity_edgeworthDensity,
    edgeworth_approx_eq (skewness F) (Real.sqrt Var[fun t : ℝ => t; F])
      (-(2 * Real.pi * ξ)) hσ.ne' m (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ hτeq]
  refine hbound.trans ?_
  rw [hsq, habs] at hBIGnn ⊢
  set τ : ℝ := (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ with hτdef
  set σ : ℝ := Real.sqrt Var[fun t : ℝ => t; F] with hσdef
  have hcore := hK |ξ| τ ((m : ℝ) + 2) (abs_nonneg ξ) hτ0 hτ1 hτeq (by linarith)
  have hdamp : Real.exp (-(4 * Real.pi ^ 2 * |ξ| ^ 2 * τ ^ 2 / 4)) ^ m
      ≤ Real.exp (-(Real.pi ^ 2 * ξ ^ 2 / 2)) := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    rw [sq_abs]
    have hτ2nn : (0 : ℝ) ≤ τ ^ 2 := sq_nonneg τ
    have h1 : (1 : ℝ) / 2 ≤ (m : ℝ) * τ ^ 2 := by
      linarith [hτeq, mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - 2) hτ2nn]
    linarith [mul_nonneg (mul_nonneg (sq_nonneg Real.pi) (sq_nonneg ξ))
      (by linarith : (0 : ℝ) ≤ (m : ℝ) * τ ^ 2 - 1 / 2)]
  have hRHS : K / ((m + 2 : ℕ) : ℝ) * windowEnvelope ξ
      = Real.exp (-(Real.pi ^ 2 * ξ ^ 2 / 2)) * (K * τ ^ 2 * (|ξ| ^ 4 + |ξ| ^ 8)) := by
    unfold windowEnvelope
    rw [hτ2]
    ring
  rw [hRHS]
  refine mul_le_mul hdamp ?_ hBIGnn (Real.exp_pos _).le
  refine le_trans (le_of_eq ?_) hcore
  ring

/-- **(E4).4 — the outer range.** Off the window the two characteristic functions are estimated
separately: the law of the root by Cramér's condition (`hcr`, supplied by
`exists_bound_lt_one_of_cramer` on the centred law), the approximant by its own Gaussian tail
(`edgeworthCharFun_tail_le`). Both bounds are geometric in `n`. -/
private lemma edgeworthGap_tail_le (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFvar : 0 < Var[fun t : ℝ => t; F]) {c cr ε : ℝ} (hc : 0 ≤ c)
    (hcr : ∀ s : ℝ, ε ≤ |s| → ‖charFun (centredLaw F) s‖ ≤ cr)
    (hε : ε * Real.sqrt Var[fun t : ℝ => t; F] ≤ 2 * Real.pi * c)
    {n : ℕ} (hn : 1 ≤ n) {ξ : ℝ} (hξ : c * Real.sqrt n ≤ |ξ|) :
    ‖charFun (stdRootLaw F n) (-(2 * Real.pi * ξ))
        - charFunDensity (edgeworthDensity (skewness F) n) (-(2 * Real.pi * ξ))‖
      ≤ cr ^ n + (1 + 512 * Real.pi ^ 3 * |skewness F|)
          * Real.exp (-(Real.pi ^ 2 * (c * Real.sqrt n) ^ 2)) := by
  have hσ : 0 < Real.sqrt Var[fun t : ℝ => t; F] := Real.sqrt_pos.2 hFvar
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hcnn : (0 : ℝ) ≤ c * Real.sqrt n := mul_nonneg hc (Real.sqrt_nonneg _)
  have hc' : c ≤ |ξ| * (Real.sqrt n)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hsn]
    exact hξ
  have h1 : ‖charFun (stdRootLaw F n) (-(2 * Real.pi * ξ))‖ ≤ cr ^ n := by
    rw [charFun_stdRootLaw F (by omega : 0 < n), norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) (hcr _ ?_) n
    rw [abs_window_arg hσ (by positivity), le_div_iff₀ hσ]
    linarith [hε, mul_le_mul_of_nonneg_left hc' (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have h2 := norm_charFunDensity_edgeworthDensity_le (skewness F) hn (-(2 * Real.pi * ξ))
  rw [neg_sq, abs_neg] at h2
  exact (norm_sub_le _ _).trans
    (add_le_add h1 (h2.trans (edgeworthCharFun_tail_le (skewness F) hcnn hξ)))

/-- **The Esseen integral, split at the window.** A nonnegative integrand dominated by
`Kw · windowEnvelope` on `|ξ| ≤ ρ` and by the constant `M` on `ρ ≤ |ξ|` is integrable against
the Esseen weight, with weighted integral at most `Kw ∫ windowDom + 2M/(δπ²ρ)`. This packages
the two halves of (E4).3–(E4).4 into the single hypothesis `hint` and the single conclusion
that `abs_measure_Iic_sub_densityCDF_le_charFun` consumes. -/
private lemma esseen_split (g : ℝ → ℝ) {δ ρ Kw M : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hKw : 0 ≤ Kw)
    (hg0 : ∀ ξ, 0 ≤ g ξ) (hgm : AEStronglyMeasurable g volume)
    (hwin : ∀ ξ, |ξ| ≤ ρ → g ξ ≤ Kw * windowEnvelope ξ)
    (htail : ∀ ξ, ρ ≤ |ξ| → g ξ ≤ M) :
    Integrable (fun ξ : ℝ =>
        g ξ * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)))
      ∧ (∫ ξ : ℝ, g ξ * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)))
        ≤ Kw * (∫ ξ : ℝ, windowDom ξ) + 2 * M / (δ * Real.pi ^ 2 * ρ) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hwnn : ∀ ξ : ℝ, 0 ≤ min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)) := fun ξ =>
    le_min (div_nonneg zero_le_one (by positivity))
      (div_nonneg zero_le_one (mul_nonneg (mul_nonneg hδ.le (by positivity)) (sq_nonneg ξ)))
  have hprodmeas : AEStronglyMeasurable
      (fun ξ : ℝ => g ξ * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)))
      volume := hgm.mul (by fun_prop)
  have hAmeas : MeasurableSet {ξ : ℝ | |ξ| ≤ ρ} :=
    measurableSet_le (by fun_prop) measurable_const
  have hTmeas : MeasurableSet {ξ : ℝ | ρ ≤ |ξ|} :=
    measurableSet_le measurable_const (by fun_prop)
  have hdom : Integrable (fun ξ : ℝ => Kw * windowDom ξ) := integrable_windowDom.const_mul Kw
  have hptwin : ∀ ξ : ℝ, |ξ| ≤ ρ →
      g ξ * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))
        ≤ Kw * windowDom ξ := by
    intro ξ hξ
    calc g ξ * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))
        ≤ Kw * windowEnvelope ξ
            * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)) :=
          mul_le_mul_of_nonneg_right (hwin ξ hξ) (hwnn ξ)
      _ ≤ Kw * windowEnvelope ξ * (1 / (Real.pi * |ξ|)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _)
            (mul_nonneg hKw (windowEnvelope_nonneg ξ))
      _ = Kw * windowDom ξ := by rw [mul_assoc, windowEnvelope_mul_weight]
  have hAint : IntegrableOn
      (fun ξ : ℝ => g ξ * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)))
      {ξ : ℝ | |ξ| ≤ ρ} := by
    refine Integrable.mono' hdom.integrableOn hprodmeas.restrict ?_
    filter_upwards [ae_restrict_mem hAmeas] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 ξ) (hwnn ξ))]
    exact hptwin ξ hξ
  have hTint : IntegrableOn
      (fun ξ : ℝ => g ξ * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)))
      {ξ : ℝ | ρ ≤ |ξ|} := by
    refine Integrable.mono' ((integrableOn_esseenWeight_tail hδ hρ).const_mul M)
      hprodmeas.restrict ?_
    filter_upwards [ae_restrict_mem hTmeas] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 ξ) (hwnn ξ))]
    exact mul_le_mul_of_nonneg_right (htail ξ hξ) (hwnn ξ)
  have hcover : {ξ : ℝ | |ξ| ≤ ρ} ∪ {ξ : ℝ | ρ ≤ |ξ|} = Set.univ := by
    ext ξ
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total |ξ| ρ
  have hInt : Integrable
      (fun ξ : ℝ => g ξ * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2))) := by
    rw [← integrableOn_univ, ← hcover]
    exact hAint.union hTint
  refine ⟨hInt, ?_⟩
  have hnnT : 0 ≤ᵐ[volume.restrict {ξ : ℝ | ρ ≤ |ξ|}]
      fun ξ : ℝ => g ξ * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)) :=
    Filter.Eventually.of_forall fun ξ => mul_nonneg (hg0 ξ) (hwnn ξ)
  have hcompl : {ξ : ℝ | |ξ| ≤ ρ}ᶜ ⊆ {ξ : ℝ | ρ ≤ |ξ|} := by
    intro ξ hξ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hξ
    exact hξ.le
  have hb2 := setIntegral_mono_set hTint hnnT hcompl.eventuallyLE
  have hb3 := setIntegral_mul_esseenWeight_tail_le hδ hρ hgm hg0 htail
  have hb1 : (∫ ξ in {ξ : ℝ | |ξ| ≤ ρ},
        g ξ * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)))
      ≤ Kw * ∫ ξ : ℝ, windowDom ξ := by
    calc (∫ ξ in {ξ : ℝ | |ξ| ≤ ρ},
          g ξ * min (1 / (Real.pi * |ξ|)) (1 / (δ * Real.pi ^ 2 * ξ ^ 2)))
        ≤ ∫ ξ in {ξ : ℝ | |ξ| ≤ ρ}, Kw * windowDom ξ :=
          setIntegral_mono_on hAint hdom.integrableOn hAmeas hptwin
      _ ≤ ∫ ξ : ℝ, Kw * windowDom ξ := by
          have h := setIntegral_mono_set (μ := volume) (f := fun ξ : ℝ => Kw * windowDom ξ)
            hdom.integrableOn
            (Filter.Eventually.of_forall fun ξ => mul_nonneg hKw (windowDom_nonneg ξ))
            (Set.subset_univ {ξ : ℝ | |ξ| ≤ ρ}).eventuallyLE
          rwa [setIntegral_univ] at h
      _ = Kw * ∫ ξ : ℝ, windowDom ξ := MeasureTheory.integral_const_mul _ _
  have hsplit := integral_add_compl hAmeas hInt
  linarith

/-- The approximant of the statement, on the standardized scale: `(t/σ)² = t²/Var`. -/
private lemma edgeworthCDF_eq_approx (F : Measure ℝ)
    (hFvar : 0 < Var[fun t : ℝ => t; F]) (n : ℕ) (t : ℝ) :
    edgeworthCDF (skewness F) n (t / Real.sqrt Var[fun t : ℝ => t; F])
      = stdNormalCDF (t / Real.sqrt Var[fun t : ℝ => t; F]) -
        1 / 6 * skewness F * stdNormalPDF (t / Real.sqrt Var[fun t : ℝ => t; F]) *
          (t ^ 2 / Var[fun t : ℝ => t; F] - 1) * (Real.sqrt n)⁻¹ := by
  have hsq : (t / Real.sqrt Var[fun t : ℝ => t; F]) ^ 2 = t ^ 2 / Var[fun t : ℝ => t; F] := by
    rw [div_pow, Real.sq_sqrt hFvar.le]
  rw [edgeworthCDF, hsq]

/-- **One sample size of the assembly.** Esseen's signed-density inequality at flank width
`δ = n⁻¹`, with the window/tail split of `esseen_split` supplying both its integrability
hypothesis and the bound on its right-hand side. -/
private lemma abs_meanRootCDF_sub_edgeworthCDF_le (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFvar : 0 < Var[fun t : ℝ => t; F]) {n : ℕ} (hn : 1 ≤ n) {c Kw M : ℝ} (hc : 0 < c)
    (hKw : 0 ≤ Kw)
    (hwin : ∀ ξ : ℝ, |ξ| ≤ c * Real.sqrt n →
      ‖charFun (stdRootLaw F n) (-(2 * Real.pi * ξ))
          - charFunDensity (edgeworthDensity (skewness F) n) (-(2 * Real.pi * ξ))‖
        ≤ Kw * windowEnvelope ξ)
    (htail : ∀ ξ : ℝ, c * Real.sqrt n ≤ |ξ| →
      ‖charFun (stdRootLaw F n) (-(2 * Real.pi * ξ))
          - charFunDensity (edgeworthDensity (skewness F) n) (-(2 * Real.pi * ξ))‖ ≤ M)
    (t : ℝ) :
    |meanRootCDF F n t - edgeworthCDF (skewness F) n (t / Real.sqrt Var[fun t : ℝ => t; F])|
      ≤ Kw * (∫ ξ : ℝ, windowDom ξ)
          + 2 * M / (1 / (n : ℝ) * Real.pi ^ 2 * (c * Real.sqrt n))
        + 2 * ((Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |skewness F|) * (1 / (n : ℝ))) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hδ : (0 : ℝ) < 1 / (n : ℝ) := div_pos one_pos hnR
  have hρpos : (0 : ℝ) < c * Real.sqrt n := mul_pos hc (Real.sqrt_pos.2 hnR)
  have hgm : AEStronglyMeasurable (fun ξ : ℝ =>
      ‖charFun (stdRootLaw F n) (-(2 * Real.pi * ξ))
        - charFunDensity (edgeworthDensity (skewness F) n) (-(2 * Real.pi * ξ))‖) volume := by
    have h1 : Continuous fun ξ : ℝ => charFun (stdRootLaw F n) (-(2 * Real.pi * ξ)) :=
      (continuous_charFun (μ := stdRootLaw F n)).comp (by fun_prop)
    have h2 : Continuous fun ξ : ℝ =>
        charFunDensity (edgeworthDensity (skewness F) n) (-(2 * Real.pi * ξ)) := by
      simp only [charFunDensity_edgeworthDensity]
      fun_prop
    exact (h1.sub h2).norm.aestronglyMeasurable
  obtain ⟨hint, hbnd⟩ := esseen_split
    (fun ξ : ℝ => ‖charFun (stdRootLaw F n) (-(2 * Real.pi * ξ))
      - charFunDensity (edgeworthDensity (skewness F) n) (-(2 * Real.pi * ξ))‖)
    hδ hρpos hKw (fun ξ => norm_nonneg _) hgm hwin htail
  have hmain := abs_measure_Iic_sub_densityCDF_le_charFun (P := stdRootLaw F n)
    (integrable_edgeworthDensity (skewness F) n) hδ
    (fun a b hab => setIntegral_abs_edgeworthDensity_le (skewness F) hn hab) hint
    (t / Real.sqrt Var[fun t : ℝ => t; F])
  rw [← meanRootCDF_eq_stdRootLaw F n hFvar t, densityCDF_edgeworthDensity] at hmain
  exact hmain.trans (add_le_add hbnd le_rfl)

end WindowEstimate


/-! ## The expansions -/

section Edgeworth

variable {F : Measure ℝ}

set_option maxHeartbeats 1600000 in
-- The assembly below elaborates a long `calc` over a constant built from eight ingredients;
-- the default heartbeat budget is not enough.
/-- **One-term Edgeworth expansion for the centred sample mean, uniform remainder.**

Under a finite fourth moment and Cramér's condition, the sampling distribution function of the
centred and scaled sample mean equals the normal approximation `Φ(t/σ)` corrected by the
skewness term `−(1/6) γ φ(t/σ) (t²/σ² − 1) n^{-1/2}`, with a remainder bounded by `C/n`
uniformly in the argument, for a constant `C` depending only on the sampling law.

**PROVED, axiom-clean.** This is Hall (1992), Thm 2.2 with `j = 1`. The programme (E1)–(E4)
recorded below is complete: the assembly takes `δ = n⁻¹` and splits the Esseen integral at
`|ξ| = c√n` with `c = min(1/(π√2), 3σ³/(4π(ρ₃ + 1)))`, bounds the window by
`exists_window_bound` and the outer range by `edgeworthGap_tail_le`, glues the two with
`esseen_split`, and absorbs the finitely many `n ≤ 3` into `C` through `abs_edgeworthCDF_le`
(the approximant is bounded by an `n`-free constant) and `meanRootCDF ∈ [0, 1]`.

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

**Re-derivation: (E1)–(E4) are ALL CLOSED.** The record below is kept because it names, piece
by piece, where each ingredient lives.

* (E1) **Signed comparison — CLOSED.** The Edgeworth approximant is not the distribution
  function of a probability measure: it is a signed measure with the explicit `L¹` density
  `q_n(y) = σ⁻¹φ(y/σ)(1 + (γ/6)(y³/σ³ − 3y/σ) n^{-1/2})`.
  (*Sign correction.* An earlier version of this note wrote that density with a minus sign in
  front of `(γ/6)`. That is wrong: differentiating the approximant
  `Φ(y/σ) − (γ/6)φ(y/σ)(y²/σ² − 1)n^{-1/2}` in the statement below and using
  `d/dx[φ(x)(x² − 1)] = −φ(x)(x³ − 3x)` gives a plus sign. The *statement* of the theorem is
  correct; only the note was.) The whole smoothing chain is now available for such a
  comparison: `ForMathlib/EsseenSmoothing.lean` proves
  `abs_measure_Iic_sub_densityCDF_le_charFun`,
  `|F_P(x) − ∫_{(-∞,x]} q| ≤ ∫ ‖φ_P(−2πξ) − φ_q(−2πξ)‖ min(1/(π|ξ|), 1/(δπ²ξ²)) dξ + 2Aδ`,
  together with the intermediate `abs_integral_ramp_mul_sub_densityCDF_le`,
  `abs_measure_Iic_sub_densityCDF_le_of_integral_ramp`,
  `abs_integral_ramp_mul_sub_le_of_trapezoid`, `integral_fourier_density` and
  `norm_integral_fourier_sub_density_le`.
  *Two details of the earlier diagnosis are corrected by the re-derivation.* First, positivity
  was used in exactly **one** place, not two: the comparison of a ramp integral with a
  distribution function (for a measure this is monotonicity). Its correct substitute is the
  **total-variation modulus** `∫_{(a,b]} |q| ≤ A (b − a)`, which for a density is the same
  constant a Lipschitz distribution function supplies; the de-smoothing loss becomes `2Aδ`
  instead of `Aδ`. Second, **equality of total masses is not needed as a hypothesis at all**:
  the ramp mass at `−∞` vanishes for any `L¹` density on its own, because the ramp of shoulder
  `v` is supported in `(-∞, v + δ]` and `∫_{(-∞,t]} |q| → 0` as `t → −∞`. Total mass enters
  only through finiteness of the right-hand side, whose weight `1/(π|ξ|)` is integrable at the
  origin exactly when `φ_P(0) = φ_q(0)`.
* (E2) **The Fourier transform of the Edgeworth density — CLOSED.**
  `ForMathlib/BerryEsseen.lean` proves `integral_hermite3_mul_cexp_mul_gaussian`,
  `∫ e^{iθu}(u³ − 3u) e^{−u²/2} du = (iθ)³ √(2π) e^{−θ²/2}`, together with
  `integral_sq_mul_cexp_mul_gaussian` and the base `integral_cexp_mul_gaussian`. Substituting
  `y = σu`, `θ = σt` gives `∫ e^{ity} q_n(y) dy = e^{−σ²t²/2}(1 − i γσ³ t³/(6√n))`, and with
  `s = t/√n`, `v = σ²`, `m₃ = γσ³` that is *literally* the approximant
  `e^{−n v s²/2}(1 − n i m₃ s³/6)` of `norm_charFun_pow_sub_edgeworth_le`: the two agree, so
  the statement below is the one the damped expansion estimates.
  *A detail of the earlier route is corrected.* Two integrations by parts are not needed, and
  neither is any boundary evaluation: for a quadratic `P`,
  `d/du[P(u) e^{iθu − u²/2}] = (P'(u) + (iθ − u)P(u)) e^{iθu − u²/2}`, so choosing
  `P(u) = −u² − iθu + (θ² + 1)` makes the bracket `u³ − 3u − (iθ)³`, and the identity is one
  application of "the integral of a derivative of an integrable function with integrable
  derivative vanishes". (`P(u) = −u − iθ` does the same for the `u²` intermediate.)
* (E3) **The Cramér tail — CLOSED.** Its analytic input is `exists_bound_lt_one_of_cramer`
  above: a single `c < 1` dominating `‖charFun F‖` on the whole region `ε ≤ |s|`, not merely
  off a compact set.
  *The verdict recorded before that was wrong.* It claimed the reduction goes through the
  lattice characterisation `‖φ_F s₀‖ = 1 ↔ F` lattice, "absent from Mathlib v4.29.1" and
  therefore blocking. The lattice statement is never needed: all that is used is that the
  modulus-one set is closed under integer multiples (`norm_charFun_natCast_mul_eq_one`), and
  that follows from the *equality case in* `‖∫ f‖ ≤ ∫‖f‖`, which on a probability space is
  elementary.
  The remaining bookkeeping is now also done, in `ForMathlib/EsseenSmoothing.lean`:
  `setIntegral_mul_esseenWeight_tail_le` gives
  `∫_{ρ ≤ |ξ|} f(ξ) min(1/(π|ξ|), 1/(δπ²ξ²)) dξ ≤ 2M/(δπ²ρ)` whenever `0 ≤ f ≤ M` there
  (off the origin the flank term alone dominates the weight, and `∫ ξ⁻²` over the two tails is
  `2/ρ`), and `exists_pow_mul_geometric_le` bounds `nᵏ cⁿ`. With `δ ≍ n⁻¹`, `ρ ≍ √n` and
  `M = cⁿ` the outer contribution is `cⁿ · O(n^{3/2}) = o(n^{-k})` for every `k`.
* (E4) **The assembly — CLOSED.** It is long rather than hard, and the re-derivation split it
  into four named pieces, none of which was an obstruction. All four, and the glue between
  them, are proved above.
  1. *The law of the root — **CLOSED**.* `charFun_meanRootLaw`:
     `charFun (meanRootLaw F n) t = (charFun (centredLaw F) (t/√n))ⁿ`.
     *The recorded route is superseded, in the direction of being easier.* The note said this
     needs a **transfer** through the canonical i.i.d. construction (`exists_iid` /
     `iIndepFun_iff_map_fun_eq_pi_map`) because Mathlib's `charFun_inv_sqrt_mul_sum` is stated
     for `iIndepFun` rather than for `Measure.pi`. No transfer is needed and
     `charFun_inv_sqrt_mul_sum` is not used at all: `meanRootLaw` *lives* on `Measure.pi`, the
     root map is `(√n)⁻¹ ∑ (yᵢ − m)` (`sqrt_mul_sub_mean_eq`), `Complex.exp_sum` turns the
     exponential of that sum into a product of one-variable factors, and
     `MeasureTheory.integral_fintype_prod_eq_pow` is precisely Fubini for such a product.
     The glue is closed with it: `stdRootLaw` — the law of `√n(X̄ₙ − μ)/σ` — with
     `charFun_stdRootLaw` and `meanRootCDF_eq_stdRootLaw`
     (`meanRootCDF F n t = P'_n((-∞, t/σ])`), and the moments of the centred law
     (`integral_id_centredLaw`, `integral_sq_centredLaw`, `integral_cube_centredLaw`:
     mean `0`, second moment `Var_F`, third moment `γσ³`), which are the `0`, `v`, `m₃` that
     `norm_charFun_pow_sub_edgeworth_le` consumes.
  2. *The approximant is the `densityCDF` of `q_n` — **CLOSED**.*
     `densityCDF_edgeworthDensity`:
     `∫_{(-∞,u]} q_n = Φ(u) − (γ/6)φ(u)(u² − 1)n^{-1/2}`, by
     `integral_Iic_of_hasDerivAt_of_tendsto'` against `hasDerivAt_hermiteAntideriv`
     (`d/du[−φ(u)(u² − 1)] = φ(u)(u³ − 3u)`) and `tendsto_hermiteAntideriv_atBot`.
     The total-variation modulus is `setIntegral_abs_edgeworthDensity_le`, with the
     **`n`-free** constant `(2π)^{-1/2}(1 + 66|γ|)` of `abs_edgeworthDensity_le` — `n`-freeness
     is what matters, since the de-smoothing loss is `2Aδ` with `δ ≍ n⁻¹`.
     *One simplification over the recorded plan.* Everything is written on the **standardized**
     scale, so the comparison density is the `σ`-free
     `q_n(u) = φ(u)(1 + (γ/6)(u³ − 3u)n^{-1/2})` and no Gaussian scaling identity
     (`normalCDF 0 σ² x = Φ(x/σ)`) is needed anywhere: `∫_{(-∞,u]} φ = Φ(u)` is
     `gaussianReal_apply_eq_integral` verbatim (`stdNormalCDF_eq_setIntegral`), and the `σ` is
     carried entirely by the *argument*, through `meanRootCDF_eq_stdRootLaw`.
     The Fourier side of the comparison is closed too. `charFunDensity_edgeworthDensity` gives
     `∫ e^{ity} q_n(y) dy = e^{−t²/2}(1 − i γ t³/(6√n))`, and that is *literally* the
     approximant `e^{−n v s²/2}(1 − n i m₃ s³/6)` of `norm_charFun_pow_sub_edgeworth_le` at
     `s = t/(σ√n)`, `v = σ²`, `m₃ = γσ³`. So the two objects
     `abs_measure_Iic_sub_densityCDF_le_charFun` compares are exactly the two objects the
     damped expansion estimates: the remaining work is quantitative only.
  3. *The window integral — **CLOSED*** (`exists_window_bound`). Take `δ = 1/n` and split at
     `|ξ| = ρ_n ≍ √n`, chosen so that `|ξ| ≤ ρ_n` implies the window conditions `v s² ≤ 2`,
     `ρ₃|s| ≤ 3v/2` of `norm_charFun_pow_sub_edgeworth_le` at `s = −2πξ/(σ√n)`; explicitly
     `v s² = 4π²ξ²/n ≤ 2` iff `ξ² ≤ n/(2π²)`, and `ρ₃|s| ≤ 3v/2` iff
     `|ξ| ≤ 3σ³√n/(4πρ₃)`, so `ρ_n = c√n` with `c = min(1/(π√2), 3σ³/(4πρ₃))`. On that range
     the damped bound is `e^{−(1 − 2/n)π²ξ²} · O((ξ⁴ + ξ⁵ + ξ⁶ + ξ⁸)/n)` against the weight
     `1/(π|ξ|)`, so the estimate reduces to the Gaussian moment integrals
     `∫ |ξ|^k e^{−aξ²} dξ` — whose *values* are irrelevant, only their finiteness
     (`integrable_windowDom`).
     *Two details of the executed proof.* First, the damping is taken as `e^{−π²ξ²/2}`, which
     needs `(n − 2)/n ≥ 1/2`, i.e. `n ≥ 4`; the finitely many `n ≤ 3` are absorbed into `C`
     because `meanRootCDF ∈ [0, 1]` and `|edgeworthCDF| ≤ 1 + 6|γ|` with an `n`-free constant
     (`abs_edgeworthCDF_le`). Second, the polynomial part is *exactly* the algebraic core
     `exists_window_core` after `abs_window_arg`/`sq_window_arg` rewrite `|s|` and `v s²`,
     and after `edgeworth_approx_eq` identifies the approximant of
     `charFunDensity_edgeworthDensity` with the one `norm_charFun_pow_sub_edgeworth_le`
     estimates. Folded into this piece is the integrability hypothesis `hint` of
     `abs_measure_Iic_sub_densityCDF_le_charFun`, discharged by `esseen_split` from the same
     two bounds.
  4. *The outer range — **CLOSED*** (`edgeworthGap_tail_le`). `‖φ_P − φ_q‖ ≤ crⁿ + ‖φ_{q_n}‖`
     there; the first term is handled by (E3) — `exists_bound_lt_one_of_cramer` applied to the
     *centred* law, which is legitimate because centring only multiplies the characteristic
     function by a unimodular factor (`cramerCondition_centredLaw`, `norm_charFun_centredLaw`),
     and the argument `s = −2πξ/(σ√n)` has `|s| ≥ 2πc/σ` on `|ξ| ≥ c√n`. For the second,
     `norm_charFunDensity_edgeworthDensity_le` supplies the Gaussian tail
     `‖φ_{q_n}(θ)‖ ≤ e^{−θ²/2}(1 + |γ||θ|³/6)`, uniformly in `n ≥ 1`, and
     `edgeworthCharFun_tail_le` turns it into `(1 + 512π³|γ|) e^{−π²c²n}` by spending half the
     Gaussian factor on the cubic polynomial. Both are geometric in `n`, and with
     `δ = n⁻¹`, `ρ_n = c√n` the weighted tail `2M/(δπ²ρ_n) = 2M√n/(π²c)` is `O(n⁻¹)` by
     `exists_pow_mul_geometric_le` with `k = 2` (`n^{3/2} ≤ n²`). -/
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
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hσ : 0 < Real.sqrt Var[fun t : ℝ => t; F] := Real.sqrt_pos.2 hFvar
  have hρ0 : (0 : ℝ) ≤ ∫ x, |x| ^ 3 ∂(centredLaw F) := integral_nonneg fun x => by positivity
  -- the window half-width `c = min(1/(π√2), 3σ³/(4π(ρ₃ + 1)))`
  obtain ⟨c, hcpos, hc2, hc3⟩ :
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 / (Real.pi * Real.sqrt 2)
        ∧ c ≤ 3 * Real.sqrt Var[fun t : ℝ => t; F] ^ 3
            / (4 * Real.pi * ((∫ x, |x| ^ 3 ∂(centredLaw F)) + 1)) := by
    refine ⟨_, lt_min (by positivity) (div_pos (mul_pos (by norm_num) (pow_pos hσ 3))
      (mul_pos (by positivity) (by linarith))), min_le_left _ _, min_le_right _ _⟩
  -- (E4).3, the window
  obtain ⟨K, hK0, hK⟩ := exists_window_bound F hF4 hFvar hc2 hc3
  -- (E4).4, the outer range: the Cramér constant and the Gaussian one
  have hεpos : (0 : ℝ) < 2 * Real.pi * c / Real.sqrt Var[fun t : ℝ => t; F] :=
    div_pos (mul_pos (by positivity) hcpos) hσ
  obtain ⟨cr0, hcr1, hcr0b⟩ :=
    exists_bound_lt_one_of_cramer (cramerCondition_centredLaw F hCramer) hεpos
  have hcrnn : (0 : ℝ) ≤ max cr0 0 := le_max_right _ _
  have hcrlt : max cr0 0 < 1 := max_lt hcr1 one_pos
  have hcrb : ∀ s : ℝ, 2 * Real.pi * c / Real.sqrt Var[fun t : ℝ => t; F] ≤ |s| →
      ‖charFun (centredLaw F) s‖ ≤ max cr0 0 := fun s h => (hcr0b s h).trans (le_max_left _ _)
  have hεle : 2 * Real.pi * c / Real.sqrt Var[fun t : ℝ => t; F]
      * Real.sqrt Var[fun t : ℝ => t; F] ≤ 2 * Real.pi * c :=
    le_of_eq (div_mul_cancel₀ _ hσ.ne')
  have hd0 : (0 : ℝ) ≤ Real.exp (-(Real.pi ^ 2 * c ^ 2)) := (Real.exp_pos _).le
  have hd1 : Real.exp (-(Real.pi ^ 2 * c ^ 2)) < 1 := by
    have hneg : -(Real.pi ^ 2 * c ^ 2) < 0 := by
      have : (0 : ℝ) < Real.pi ^ 2 * c ^ 2 := mul_pos (by positivity) (pow_pos hcpos 2)
      linarith
    calc Real.exp (-(Real.pi ^ 2 * c ^ 2)) < Real.exp 0 := Real.exp_lt_exp.2 hneg
      _ = 1 := Real.exp_zero
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_pow_mul_geometric_le hcrnn hcrlt 2
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_pow_mul_geometric_le hd0 hd1 2
  -- the constants entering `C`
  have hW0 : (0 : ℝ) ≤ ∫ ξ : ℝ, windowDom ξ := integral_nonneg fun ξ => windowDom_nonneg ξ
  have hB0 : (0 : ℝ) ≤ 1 + 512 * Real.pi ^ 3 * |skewness F| := by positivity
  have hP0 : (0 : ℝ) ≤ (Real.pi ^ 2 * c)⁻¹ :=
    inv_nonneg.2 (mul_nonneg (by positivity) hcpos.le)
  have hA0 : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |skewness F|) :=
    (edgeworthTV_pos (skewness F)).le
  have hKW : (0 : ℝ) ≤ K * ∫ ξ : ℝ, windowDom ξ := mul_nonneg hK0.le hW0
  have hTC : (0 : ℝ) ≤ 2 * (C₁ + (1 + 512 * Real.pi ^ 3 * |skewness F|) * C₂)
      * (Real.pi ^ 2 * c)⁻¹ :=
    mul_nonneg (by nlinarith [hC₁0, hC₂0, hB0]) hP0
  have hgam : (0 : ℝ) ≤ |skewness F| := abs_nonneg _
  refine ⟨K * (∫ ξ : ℝ, windowDom ξ)
      + 2 * ((Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |skewness F|))
      + 2 * (C₁ + (1 + 512 * Real.pi ^ 3 * |skewness F|) * C₂) * (Real.pi ^ 2 * c)⁻¹
      + 3 * (2 + 6 * |skewness F|) + 1, by linarith, ?_⟩
  intro n hn t
  have hn1 : 1 ≤ n := hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  rw [← edgeworthCDF_eq_approx F hFvar n t]
  rcases le_or_gt 4 n with h4 | h4
  · -- the main range: the window estimate and the outer estimate, split at `c√n`
    have hwin : ∀ ξ : ℝ, |ξ| ≤ c * Real.sqrt (n : ℝ) →
        ‖charFun (stdRootLaw F n) (-(2 * Real.pi * ξ))
            - charFunDensity (edgeworthDensity (skewness F) n) (-(2 * Real.pi * ξ))‖
          ≤ K / (n : ℝ) * windowEnvelope ξ := by
      intro ξ hξ
      refine hK n h4 ξ ?_
      rw [← div_eq_mul_inv, div_le_iff₀ hsn]
      exact hξ
    have hdpow : Real.exp (-(Real.pi ^ 2 * (c * Real.sqrt (n : ℝ)) ^ 2))
        = Real.exp (-(Real.pi ^ 2 * c ^ 2)) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [mul_pow, Real.sq_sqrt hnR.le]
      ring
    have htail : ∀ ξ : ℝ, c * Real.sqrt (n : ℝ) ≤ |ξ| →
        ‖charFun (stdRootLaw F n) (-(2 * Real.pi * ξ))
            - charFunDensity (edgeworthDensity (skewness F) n) (-(2 * Real.pi * ξ))‖
          ≤ max cr0 0 ^ n
            + (1 + 512 * Real.pi ^ 3 * |skewness F|)
              * Real.exp (-(Real.pi ^ 2 * c ^ 2)) ^ n := by
      intro ξ hξ
      have h := edgeworthGap_tail_le F hFvar hcpos.le hcrb hεle hn1 hξ
      rwa [hdpow] at h
    have hstep := abs_meanRootCDF_sub_edgeworthCDF_le F hFvar hn1 hcpos
      (div_nonneg hK0.le hnR.le) hwin htail t
    -- `δ ρ = π²c/√n`, so the outer contribution is `2 M √n /(π²c)`
    have hnn : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hnR.le
    have hDeq : 1 / (n : ℝ) * Real.pi ^ 2 * (c * Real.sqrt (n : ℝ))
        = Real.pi ^ 2 * c / Real.sqrt (n : ℝ) := by
      rw [eq_div_iff hsn.ne']
      have h : 1 / (n : ℝ) * Real.pi ^ 2 * (c * Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ)
          = Real.pi ^ 2 * c * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) / (n : ℝ)) := by ring
      rw [h, hnn, div_self hnR.ne', mul_one]
    rw [hDeq, div_div_eq_mul_div] at hstep
    set Bc : ℝ := 1 + 512 * Real.pi ^ 3 * |skewness F| with hBcdef
    set Ac : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |skewness F|) with hAcdef
    set Wc : ℝ := ∫ ξ : ℝ, windowDom ξ with hWcdef
    set Mn : ℝ := max cr0 0 ^ n + Bc * Real.exp (-(Real.pi ^ 2 * c ^ 2)) ^ n with hMndef
    have hMn0 : (0 : ℝ) ≤ Mn :=
      add_nonneg (pow_nonneg hcrnn n) (mul_nonneg hB0 (pow_nonneg hd0 n))
    have hsqle : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have h2 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq hnR.le] at h2
    have hMn2 : Mn * Real.sqrt (n : ℝ) * (n : ℝ) ≤ C₁ + Bc * C₂ := by
      have h1 : Mn * Real.sqrt (n : ℝ) * (n : ℝ) ≤ Mn * (n : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqle hMn0) hnR.le
      have h2 : Mn * (n : ℝ) * (n : ℝ) ≤ C₁ + Bc * C₂ := by
        rw [hMndef]
        linarith [hC₁ n, mul_le_mul_of_nonneg_left (hC₂ n) hB0]
      linarith
    have hb2 : 2 * Mn * Real.sqrt (n : ℝ) / (Real.pi ^ 2 * c)
        ≤ 2 * (C₁ + Bc * C₂) * (Real.pi ^ 2 * c)⁻¹ / (n : ℝ) := by
      rw [le_div_iff₀ hnR, div_eq_mul_inv]
      linarith [mul_le_mul_of_nonneg_right hMn2 hP0]
    calc |meanRootCDF F n t
            - edgeworthCDF (skewness F) n (t / Real.sqrt Var[fun t : ℝ => t; F])|
        ≤ K / (n : ℝ) * Wc + 2 * Mn * Real.sqrt (n : ℝ) / (Real.pi ^ 2 * c)
            + 2 * (Ac * (1 / (n : ℝ))) := hstep
      _ ≤ K * Wc / (n : ℝ) + 2 * (C₁ + Bc * C₂) * (Real.pi ^ 2 * c)⁻¹ / (n : ℝ)
            + 2 * Ac / (n : ℝ) := by
          have e1 : K / (n : ℝ) * Wc = K * Wc / (n : ℝ) := by ring
          have e3 : 2 * (Ac * (1 / (n : ℝ))) = 2 * Ac / (n : ℝ) := by ring
          linarith
      _ ≤ (K * Wc + 2 * Ac + 2 * (C₁ + Bc * C₂) * (Real.pi ^ 2 * c)⁻¹
            + 3 * (2 + 6 * |skewness F|) + 1) / (n : ℝ) := by
          rw [← add_div, ← add_div, div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · -- the finitely many small `n`, absorbed by boundedness of both sides
    have hn3 : (n : ℝ) ≤ 3 := by exact_mod_cast (by omega : n ≤ 3)
    have hm1 : |meanRootCDF F n t| ≤ 1 := by
      rw [meanRootCDF_eq_stdRootLaw F n hFvar t, abs_of_nonneg ENNReal.toReal_nonneg]
      simpa using ENNReal.toReal_mono (by simp) (prob_le_one (μ := stdRootLaw F n))
    have hap := abs_edgeworthCDF_le (skewness F) hn1 (t / Real.sqrt Var[fun t : ℝ => t; F])
    have htri : |meanRootCDF F n t
          - edgeworthCDF (skewness F) n (t / Real.sqrt Var[fun t : ℝ => t; F])|
        ≤ |meanRootCDF F n t|
          + |edgeworthCDF (skewness F) n (t / Real.sqrt Var[fun t : ℝ => t; F])| := by
      have h := abs_add_le (meanRootCDF F n t)
        (-(edgeworthCDF (skewness F) n (t / Real.sqrt Var[fun t : ℝ => t; F])))
      rw [abs_neg] at h
      rw [sub_eq_add_neg]
      exact h
    rw [le_div_iff₀ hnR]
    calc |meanRootCDF F n t
            - edgeworthCDF (skewness F) n (t / Real.sqrt Var[fun t : ℝ => t; F])| * (n : ℝ)
        ≤ (2 + 6 * |skewness F|) * 3 :=
          mul_le_mul (by linarith) hn3 hnR.le (by positivity)
      _ ≤ K * (∫ ξ : ℝ, windowDom ξ)
            + 2 * ((Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |skewness F|))
            + 2 * (C₁ + (1 + 512 * Real.pi ^ 3 * |skewness F|) * C₂) * (Real.pi ^ 2 * c)⁻¹
            + 3 * (2 + 6 * |skewness F|) + 1 := by linarith

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
not proved here, and it is strictly harder than `edgeworth_mean_uniform`: (E1)–(E4) recorded
there are now all closed, but this theorem needs in addition the **bivariate** Edgeworth
expansion for `(X̄, X̄₂)` together with the delta-method transfer to the smooth function
`(u, v) ↦ u/√(v − u²)`. That single missing estimate is what the re-derivation below isolates.

Several pieces this note used to name as missing are now present, and the corresponding
verdicts are dead. The CDF-level Esseen inversion is proved
(`abs_measure_Iic_sub_le_charFun` in `ForMathlib/EsseenSmoothing.lean`), so is its
signed-density form (`abs_measure_Iic_sub_densityCDF_le_charFun`), so is the Cramér-tail
bookkeeping (`setIntegral_mul_esseenWeight_tail_le`, `exists_pow_mul_geometric_le`), and so is
the damped characteristic-function expansion — recorded as *the* binding estimate —
(`norm_charFun_pow_sub_edgeworth_le` in `ForMathlib/BerryEsseen.lean`) together with the
Hermite Fourier identity (`integral_hermite3_mul_cexp_mul_gaussian`).

**Re-derivation of the bivariate verdict: it stands, and it is now isolated.** Three points.

* *The rate is not weaker here.* Both this theorem and `edgeworth_mean_uniform` are stated with
  the same remainder `C/n`; there is no `O(n^{-1/2+ε})` slack in the statement to exploit.
* *No Slutsky-type reduction to the centred root can work, at any rate finer than `n^{-1/2}`.*
  Evaluating the centred approximant at the argument `σt` gives
  `Φ(t) − (1/6)γφ(t)(t² − 1)n^{-1/2}` (the `σ`'s cancel: `φ(σt/σ) = φ(t)` and
  `(σt)²/σ² − 1 = t² − 1`), while the studentized approximant is
  `Φ(t) + (1/6)γφ(t)(2t² + 1)n^{-1/2}`. Their difference is exactly
  `(1/2) γ t² φ(t) n^{-1/2}`, which is nonzero for every `t ≠ 0` as soon as `γ ≠ 0`. So the two
  sampling distribution functions differ at order `n^{-1/2}`, and a reduction of one to the
  other that is accurate to `O(n⁻¹)` — indeed any argument controlling only `o(1)`, which is
  all Slutsky and the continuous-mapping theorem give — cannot produce the studentized
  `n^{-1/2}` coefficient. The advantage of studentizing *is* this discrepancy; an argument that
  loses it proves nothing.
* *What is genuinely missing is one estimate, not the whole route.* The CDF-level half of the
  argument is dimension-free in the sense that matters: after the delta-method transfer one is
  still comparing two laws **on the line** — the law of the studentized root and its signed
  approximant — so `abs_measure_Iic_sub_densityCDF_le_charFun`, `normalCDF_sub_le` and the
  tail lemmas apply verbatim. What does *not* transfer is the characteristic-function estimate:
  `√n(X̄ − μ)/σ̂` is **not** a sum of i.i.d. summands, so its characteristic function is not a
  power of `charFun F` and `norm_charFun_pow_sub_edgeworth_le` cannot be applied to it. The
  standard remedy is to pass to `(X̄, X̄₂)`, which *is* an i.i.d. sum in `ℝ²`, expand there, and
  transfer through the smooth function `(u, v) ↦ u/√(v − u²)`. That needs a two-dimensional
  analogue of `norm_charFun_le_exp_neg_sq`, whose window is governed by the smallest eigenvalue
  of the covariance of `(X, X²)` and therefore needs the nondegeneracy that `hFac` supplies. -/
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
`edgeworth_studentized_uniform` — which, now that (E1)–(E4) on `edgeworth_mean_uniform` are all
closed, is the bivariate expansion alone. -/
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
