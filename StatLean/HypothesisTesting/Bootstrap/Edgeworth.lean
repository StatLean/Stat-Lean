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
* The three expansions are **statements only** at this pin, but every named prerequisite of the
  centred one is now proved. `ForMathlib/EsseenSmoothing.lean` proves Esseen's smoothing
  inequality at the level of distribution functions (`abs_measure_Iic_sub_le_charFun`), with
  `normalCDF_sub_le` below supplying its Lipschitz input, **and its signed-density form**
  (`abs_measure_Iic_sub_densityCDF_le_charFun`), which is what an Edgeworth approximant needs;
  `ForMathlib/BerryEsseen.lean` proves the damped expansion of `(charFun F)ⁿ` to order `n⁻¹`
  (`norm_charFun_pow_sub_edgeworth_le`) **and the Hermite Fourier identity**
  (`integral_hermite3_mul_cexp_mul_gaussian`) that transforms the Edgeworth density; the Cramér
  tail's analytic input is proved here (`exists_bound_lt_one_of_cramer`) and its bookkeeping in
  `ForMathlib/EsseenSmoothing.lean` (`setIntegral_mul_esseenWeight_tail_le`,
  `exists_pow_mul_geometric_le`). What is left for `edgeworth_mean_uniform` is the **assembly
  alone**. See the re-derived status note (E1)–(E4) on that theorem.
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

end RootLaw

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

**Re-derivation: (E1)–(E3) are now CLOSED; only (E4) remains.**

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
* (E4) **The assembly — the one item left.** It is long rather than hard, and the
  re-derivation splits it into four named pieces, none of which is an obstruction:
  1. *The law of the root.* `meanRootCDF F n x = (meanRootLaw F n) (Iic x)` (`meanRootCDF_eq`
     in `Bootstrap/NonparametricMean.lean`), and one needs
     `charFun (meanRootLaw F n) t = (charFun F₀ (t/√n))ⁿ` for the centred law `F₀`. Mathlib's
     `charFun_inv_sqrt_mul_sum` is stated for `iIndepFun` on a probability space rather than
     for `Measure.pi`, so this is a *transfer* through the canonical i.i.d. construction
     (`exists_iid` / `iIndepFun_iff_map_fun_eq_pi_map`), of the kind already carried out in
     `ChiSquaredMultinomial.lean` — not a new analytic fact.
  2. *The approximant is the `densityCDF` of `q_n`.* One must check
     `∫_{(-∞,x]} q_n = Φ(x/σ) − (γ/6)φ(x/σ)(x²/σ² − 1)n^{-1/2}`, i.e. an FTC computation
     against `d/dx[φ(x)(x² − 1)] = −φ(x)(x³ − 3x)` with the limit `0` at `−∞`; and the
     total-variation modulus `∫_{(a,b]} |q_n| ≤ A (b − a)` with `A = sup|q_n|` uniform in
     `n ≥ 1`, which is elementary since `φ(u)(1 + (γ/6)(u³ − 3u))` is bounded.
  3. *The window integral.* Take `δ = 1/n` and split at `|ξ| = ρ_n ≍ √n`, chosen so that
     `|ξ| ≤ ρ_n` implies the window conditions `v s² ≤ 2`, `ρ₃|s| ≤ 3v/2` of
     `norm_charFun_pow_sub_edgeworth_le` at `s = −2πξ/√n`. On that range the damped bound is
     `e^{−(1 − 2/n) v π² ξ²} · O((ξ⁴ + ξ⁵ + ξ⁶)/n)` against the weight `1/(π|ξ|)`, so the
     estimate reduces to the Gaussian moment integrals `∫ |ξ|^k e^{−aξ²} dξ`. This is the
     genuinely long computation; it also needs the finitely many small `n` (where
     `1 − 2/n ≤ 0`) absorbed into `C`, which is legitimate because both `meanRootCDF` and the
     approximant are bounded.
  4. *The outer range.* `‖φ_P − φ_q‖ ≤ cⁿ + ‖φ_{q_n}‖` there, the first term handled by (E3)
     and the second by the Gaussian tail of `φ_{q_n}(−2πξ) = e^{−σ²(2πξ)²/2}(1 + …)`. -/
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
