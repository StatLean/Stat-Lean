import StatLean.HypothesisTesting.Bootstrap.NonparametricMean
import StatLean.HypothesisTesting.ForMathlib.BivariateEdgeworth
import StatLean.HypothesisTesting.ForMathlib.EsseenSmoothing
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

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
* `cramerCondition_of_absolutelyContinuous` — Riemann–Lebesgue: `F ≪ volume` implies Cramér's
  condition, so the studentized hypothesis set is stronger than the centred one;
* `VecCramerCondition`, `norm_charFun_lt_one_of_projLaw_cramer`,
  `exists_bound_lt_one_of_vecCramer` — the same off-the-origin bound in an inner product space,
  uniform over directions; the strict bound in one direction is one-dimensional and the
  uniformity is compactness;
* `abs_inv_sqrt_one_add_sub_le`, `abs_studentFactor_sub_taylor_le` — the uniform second-order
  Taylor bound for the studentizing factor `(1 + x)^{-1/2}`, proved algebraically, and the
  resulting `O(n^{-1})` pointwise replacement of the studentized root by its surrogate;
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
* The **studentized** route is set up here too, and most of its analytic steps are proved.
  `ForMathlib/BivariateEdgeworth.lean` supplies the multivariate damped expansion — via the
  projection identity `charFun_smul_eq_charFun_map_inner`, which makes the restriction of a
  characteristic function to a ray a *one-dimensional* characteristic function, so that no
  two-dimensional argument is needed — together with the expansion of the *mixed* characteristic
  function `∫ ⟪w,b⟫e^{i⟪w,a⟫}` that the scalar route needs and that no differentiation of an
  inequality can give (`mixCharFun_vecRootLaw`, `norm_mixCharFun_vecRootLaw_sub_le`), while
  `studentizedRootCDF_eq_vecRootLaw` below identifies `studentizedRootCDF F n` **exactly** with
  a set-function of the bivariate root law of `studentPair F = (X − μ, (X − μ)² − σ²)`, and
  `abs_studentFactor_sub_taylor_le` bounds the exact statistic against its Taylor surrogate
  uniformly. What is left is probabilistic: a truncation-based tail bound with its
  anti-concentration companion, and the multivariate Cramér condition for the parabola-carried
  bivariate law (the direction-uniform half of which is the `VecCramer` section below). See the
  status note (S1)–(S2), (M1)–(M3) on `edgeworth_studentized_uniform`.
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
open scoped ENNReal NNReal Topology RealInnerProductSpace

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

/-- **An absolutely continuous law satisfies Cramér's condition.**

This is the Riemann–Lebesgue lemma, in the form the Edgeworth expansions consume: writing
`F = volume.withDensity (dF/dx)`, the characteristic function of `F` is the Fourier integral of
its density up to the reparametrisation `s = −2πw`, so `φ_F(s) → 0` as `|s| → ∞`, and in
particular `‖φ_F(s)‖ ≤ 1/2` off a compact set.

The point of recording it is that `edgeworth_studentized_uniform` is stated under `F ≪ volume`
while `edgeworth_mean_uniform` is stated under `CramerCondition F`: this lemma is the bridge
between the two hypothesis sets, so the studentized statement's smoothness assumption is
strictly stronger than the centred one's, as it should be. -/
theorem cramerCondition_of_absolutelyContinuous (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F ≪ volume) : CramerCondition F := by
  set p : ℝ → ℝ≥0∞ := F.rnDeriv volume with hpdef
  have hpm : Measurable p := F.measurable_rnDeriv volume
  have hplt : ∀ᵐ x ∂(volume : Measure ℝ), p x < ⊤ := Measure.rnDeriv_lt_top F volume
  have hFd : (volume : Measure ℝ).withDensity p = F :=
    Measure.withDensity_rnDeriv_eq F volume hF
  -- the characteristic function is the Fourier integral of the density, at `w = −s/(2π)`
  have hchar : ∀ s : ℝ, charFun F s
      = ∫ v : ℝ, Real.fourierChar (-(v * (-(2 * Real.pi)⁻¹ * s)))
          • (((p v).toReal : ℝ) : ℂ) := by
    intro s
    rw [charFun_apply_real, ← hFd, integral_withDensity_eq_integral_toReal_smul hpm hplt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only []
    have hex : (2 * Real.pi * -(v * (-(2 * Real.pi)⁻¹ * s)) : ℝ) = s * v := by
      have hpi : (2 * Real.pi) ≠ 0 := by positivity
      field_simp
    rw [Circle.smul_def, Real.fourierChar_apply, hex, smul_eq_mul, Complex.ofReal_mul]
    change (((p v).toReal : ℝ) : ℂ) * Complex.exp (((s : ℝ) : ℂ) * ((v : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((s : ℝ) : ℂ) * ((v : ℝ) : ℂ) * Complex.I) * (((p v).toReal : ℝ) : ℂ)
    ring
  have hRL : Filter.Tendsto (fun w : ℝ => ∫ v : ℝ, Real.fourierChar (-(v * w))
        • (((p v).toReal : ℝ) : ℂ)) (Filter.cocompact ℝ) (nhds 0) :=
    Real.tendsto_integral_exp_smul_cocompact _
  have hc : (-(2 * Real.pi)⁻¹ : ℝ) ≠ 0 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    simp [hpi]
  have hmap : Filter.Tendsto (fun s : ℝ => -(2 * Real.pi)⁻¹ * s)
      (Filter.cocompact ℝ) (Filter.cocompact ℝ) :=
    le_of_eq (Homeomorph.mulLeft₀ (-(2 * Real.pi)⁻¹ : ℝ) hc).map_cocompact
  have hTend : Filter.Tendsto (fun s : ℝ => charFun F s) (Filter.cocompact ℝ) (nhds 0) := by
    have hcomp := hRL.comp hmap
    simpa [Function.comp_def, hchar] using hcomp
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [NormedAddGroup.tendsto_nhds_zero.1 hTend (1 / 2) (by norm_num)] with s hs
  exact hs.le

end Cramer

/-! ## Cramér's condition in an inner product space — (M3)(i)

The Cramér tail of the *studentized* expansion needs a bound `‖φ_ρ t‖ ≤ c < 1` on a whole
region `ε ≤ ‖t‖` of the plane, for `ρ` the law of the bivariate summand. The note on
`edgeworth_studentized_uniform` isolates two halves of that requirement, and this section
proves the second one and makes the first one precise.

* *The directional reduction is free.* `charFun_smul_eq_charFun_map_inner` evaluated at `s = 1`
  says `φ_μ(t) = φ_{projLaw μ t}(1)`, so the strict bound `‖φ_μ(t)‖ < 1` at a **single**
  nonzero `t` is the one-dimensional `norm_charFun_lt_one_of_cramer` applied to the projected
  law, at the argument `1 ≠ 0` (`norm_charFun_lt_one_of_projLaw_cramer`). No two-dimensional
  input, and no uniformity, is used here.
* *Uniformity over directions is a compactness statement, and it is proved here.* Given the
  cocompact bound of `VecCramerCondition` and the pointwise strict bound above,
  `exists_bound_lt_one_of_vecCramer` produces a single `c < 1` valid on all of `ε ≤ ‖t‖`: the
  bound holds off a compact `K` by hypothesis, and on the compact `K ∩ {ε ≤ ‖t‖}` the
  continuous function `‖φ_μ‖` attains a maximum at some `t₀`, which is `< 1` because
  `‖t₀‖ ≥ ε > 0` forces `t₀ ≠ 0`. This is the "compactness argument over the circle" the note
  calls for, in the form that is actually needed — over a compact annulus rather than the
  circle, which avoids having to control the radial variable separately.

What remains open in (M3)(i) is only the cocompact half itself, `VecCramerCondition`, for the
*specific* bivariate law of `studentPair F`. That law is carried by a parabola and hence is
singular in `ℝ²` even when `F ≪ volume`, so it is not supplied by Riemann–Lebesgue: on the
axis `t₁ = 0` it is the one-dimensional Cramér condition for `F`, while for `t₁` bounded away
from `0` the phase `t₀y + t₁y²` is genuinely quadratic and the decay is a van der Corput
second-derivative estimate. Uniformity across the transition between the two regimes is the
classical delicate point, and it is *not* a corollary of the directionwise conditions —
multivariate Cramér is strictly stronger than Cramér in every direction. -/

section VecCramer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **Cramér's condition in an inner product space**: the modulus of the characteristic
function is eventually bounded by a constant strictly below `1` off the compact sets. The
verbatim analogue of `CramerCondition`, with `Filter.cocompact ℝ` replaced by
`Filter.cocompact E`. -/
def VecCramerCondition (μ : Measure E) : Prop :=
  ∃ c : ℝ, c < 1 ∧ ∀ᶠ t in Filter.cocompact E, ‖charFun μ t‖ ≤ c

/-- **The strict bound at a single nonzero direction is one-dimensional.**

`φ_μ(t) = φ_{projLaw μ t}(1)` by `charFun_smul_eq_charFun_map_inner` at `s = 1`, so
`‖φ_μ(t)‖ < 1` as soon as the *projected* law in the direction `t` satisfies the
one-dimensional Cramér condition. For the bivariate law of `studentPair F` the projected law in
the direction `t` is the law of `t₀(X − μ) + t₁((X − μ)² − σ²)`, a nonconstant polynomial image
of `F`, so absolute continuity of `F` supplies the hypothesis in every direction. -/
theorem norm_charFun_lt_one_of_projLaw_cramer (μ : Measure E) [IsProbabilityMeasure μ] {t : E}
    (hproj : CramerCondition (projLaw μ t)) : ‖charFun μ t‖ < 1 := by
  have h : charFun μ t = charFun (projLaw μ t) 1 := by
    have h1 := charFun_smul_eq_charFun_map_inner μ t 1
    rwa [one_smul] at h1
  rw [h]
  exact norm_charFun_lt_one_of_cramer hproj one_ne_zero

/-- **The uniform Cramér bound on `ε ≤ ‖t‖`, in an inner product space.**

A single constant `c < 1` dominating `‖φ_μ t‖ on the whole region `ε ≤ ‖t‖`, from the cocompact
bound plus the pointwise strict bound off the origin. This is the exact analogue of
`exists_bound_lt_one_of_cramer` and is what an Edgeworth tail estimate consumes; the proof is
the compactness argument over directions, run on the compact set `K ∩ {ε ≤ ‖t‖}`. -/
theorem exists_bound_lt_one_of_vecCramer (μ : Measure E) [IsProbabilityMeasure μ]
    (hCramer : VecCramerCondition μ) (hpt : ∀ t : E, t ≠ 0 → ‖charFun μ t‖ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, c < 1 ∧ ∀ t : E, ε ≤ ‖t‖ → ‖charFun μ t‖ ≤ c := by
  obtain ⟨c₀, hc₀, hev⟩ := hCramer
  rw [Filter.eventually_iff, mem_cocompact] at hev
  obtain ⟨K, hKcomp, hKsub⟩ := hev
  have hAcomp : IsCompact (K ∩ {t : E | ε ≤ ‖t‖}) :=
    hKcomp.inter_right (isClosed_le continuous_const continuous_norm)
  rcases (K ∩ {t : E | ε ≤ ‖t‖}).eq_empty_or_nonempty with hAe | hAne
  · refine ⟨c₀, hc₀, fun t ht => ?_⟩
    have htK : t ∉ K := fun hK => by
      have hmem : t ∈ K ∩ {t : E | ε ≤ ‖t‖} := ⟨hK, ht⟩
      rw [hAe] at hmem
      exact hmem.elim
    exact hKsub htK
  · obtain ⟨t₀, ht₀mem, ht₀max⟩ := hAcomp.exists_isMaxOn hAne
      (Continuous.continuousOn (continuous_charFun (μ := μ)).norm)
    have ht₀ne : t₀ ≠ 0 := by
      intro h0
      have hge : ε ≤ ‖t₀‖ := ht₀mem.2
      rw [h0, norm_zero] at hge
      linarith
    refine ⟨max c₀ ‖charFun μ t₀‖, max_lt hc₀ (hpt t₀ ht₀ne), fun t ht => ?_⟩
    by_cases hK : t ∈ K
    · exact (ht₀max ⟨hK, ht⟩).trans (le_max_right _ _)
    · exact (hKsub hK).trans (le_max_left _ _)

/-- **The uniform Cramér bound from the directionwise conditions plus the cocompact bound.**
The packaged form: the pointwise hypothesis of `exists_bound_lt_one_of_vecCramer` is discharged
direction by direction through the projection identity. -/
theorem exists_bound_lt_one_of_projLaw_cramer (μ : Measure E) [IsProbabilityMeasure μ]
    (hCramer : VecCramerCondition μ)
    (hdir : ∀ t : E, t ≠ 0 → CramerCondition (projLaw μ t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, c < 1 ∧ ∀ t : E, ε ≤ ‖t‖ → ‖charFun μ t‖ ≤ c :=
  exists_bound_lt_one_of_vecCramer μ hCramer
    (fun t ht => norm_charFun_lt_one_of_projLaw_cramer μ (hdir t ht)) hε

/-- **Multivariate Cramér is exactly a Riemann–Lebesgue statement that is uniform over the
unit sphere of directions.**

`VecCramerCondition μ` follows from a single bound `‖φ_{projLaw μ θ}(R)‖ ≤ c < 1` holding for
every unit vector `θ` and every large radius `R`. The proof is the projection identity written
in polar form: `t = ‖t‖ • (t/‖t‖)`, so `φ_μ(t) = φ_{projLaw μ (t/‖t‖)}(‖t‖)`, and in a proper
space `‖t‖ → ∞` along `cocompact E`.

This pins down what is left of (M3)(i) for the law of `studentPair F`, and it is the reason
that residue is *not* a corollary of the directionwise conditions. Each projected law
`ν_θ = law of θ₀(X − μ) + θ₁((X − μ)² − σ²)` is a nonconstant polynomial image of an absolutely
continuous law and hence itself absolutely continuous, so `‖φ_{ν_θ}(R)‖ → 0` as `R → ∞` for
every *fixed* `θ` by Riemann–Lebesgue (`cramerCondition_of_absolutelyContinuous`). What is
missing — and only this — is that the convergence be **uniform over the compact sphere**. Two
routes are classical, and both give the stronger conclusion `limsup = 0` rather than merely
`< 1`:

* the two-regime van der Corput argument (`|θ₁|` bounded away from `0`: second-derivative test
  on the genuinely quadratic phase `θ₀y + θ₁y²`; `|θ₁|` small: first-derivative test, the phase
  being close to linear), with the uniformity across the transition as the delicate point;
* the soft route: `θ ↦ ν_θ` is continuous in total variation on the sphere — the density of
  `ν_θ` is `∑_{roots} f(y)/|θ₀ + 2θ₁y|`, whose `|·|^{-1/2}` singularity at the critical value
  `−θ₀/(2θ₁)` escapes to infinity as `θ₁ → 0` and therefore carries vanishing mass — and
  Riemann–Lebesgue is uniform on totally bounded subsets of `L¹`, since
  `‖φ_ν(R) − φ_{ν'}(R)‖ ≤ ‖ν − ν'‖_{TV}` for every `R`.

Neither is available in Mathlib at present. -/
theorem vecCramerCondition_of_uniform_sphere [ProperSpace E] (μ : Measure E)
    {c R₀ : ℝ} (hc : c < 1) (hR₀ : 0 < R₀)
    (h : ∀ θ : E, ‖θ‖ = 1 → ∀ R : ℝ, R₀ ≤ R → ‖charFun (projLaw μ θ) R‖ ≤ c) :
    VecCramerCondition μ := by
  refine ⟨c, hc, ?_⟩
  filter_upwards [(tendsto_norm_cocompact_atTop (E := E)).eventually_ge_atTop R₀] with t ht
  have htpos : (0 : ℝ) < ‖t‖ := lt_of_lt_of_le hR₀ ht
  set θ : E := (‖t‖)⁻¹ • t with hθdef
  have hθ : ‖θ‖ = 1 := by
    rw [hθdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ htpos.ne']
  have hpolar : (‖t‖ : ℝ) • θ = t := by
    rw [hθdef, smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
  have hid : charFun μ t = charFun (projLaw μ θ) ‖t‖ := by
    rw [← charFun_smul_eq_charFun_map_inner μ θ ‖t‖, hpolar]
  rw [hid]
  exact h θ hθ ‖t‖ ht

end VecCramer

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

/-- The inner product with the studentizing pair, in coordinates. -/
lemma inner_studentPair (F : Measure ℝ) (t : EuclideanSpace ℝ (Fin 2)) (x : ℝ) :
    (⟪studentPair F x, t⟫ : ℝ)
      = t 0 * (x - ∫ s, s ∂F)
        + t 1 * ((x - ∫ s, s ∂F) ^ 2 - Var[fun s : ℝ => s; F]) := by
  -- over `ℝ` the scalar inner product `⟪a, b⟫` is *definitionally* `b * a`
  rw [studentPair, PiLp.inner_apply, Fin.sum_univ_two]
  rfl

/-- **The studentizing pair is centred in every direction.** This is the `hmean` hypothesis of
`norm_charFun_smul_pow_sub_edgeworth_le` for the bivariate law of `studentPair F`. -/
lemma integral_inner_studentPair (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF4 : MemLp (fun s : ℝ => s) 4 F) (t : EuclideanSpace ℝ (Fin 2)) :
    ∫ w, (⟪w, t⟫ : ℝ) ∂(F.map (studentPair F)) = 0 := by
  set m : ℝ := ∫ s, s ∂F with hm
  set v : ℝ := Var[fun s : ℝ => s; F] with hv
  have hi1 : Integrable (fun y : ℝ => y) (centredLaw F) := integrable_id_centredLaw F hF4
  have hi2 : Integrable (fun y : ℝ => y ^ 2) (centredLaw F) := integrable_sq_centredLaw F hF4
  have hg : ∫ y, (t 0 * y + t 1 * (y ^ 2 - v)) ∂(centredLaw F)
      = ∫ x, (t 0 * (x - m) + t 1 * ((x - m) ^ 2 - v)) ∂F :=
    integral_centredLaw F (g := fun y : ℝ => t 0 * y + t 1 * (y ^ 2 - v)) (by fun_prop)
  have h1 : Integrable (fun y : ℝ => t 0 * y) (centredLaw F) := hi1.const_mul _
  have hsub : Integrable (fun y : ℝ => y ^ 2 - v) (centredLaw F) := hi2.sub (integrable_const v)
  have h2 : Integrable (fun y : ℝ => t 1 * (y ^ 2 - v)) (centredLaw F) := hsub.const_mul _
  have hs1 : ∫ y : ℝ, y ∂(centredLaw F) = 0 :=
    integral_id_centredLaw F (hF4.integrable (by norm_num))
  have hs2 : ∫ y : ℝ, (y ^ 2 - v) ∂(centredLaw F) = 0 := by
    rw [integral_sub hi2 (integrable_const v), integral_sq_centredLaw, integral_const]
    simp [hv]
  have hval : ∫ y, (t 0 * y + t 1 * (y ^ 2 - v)) ∂(centredLaw F) = 0 := by
    rw [integral_add h1 h2, integral_const_mul, integral_const_mul, hs1, hs2]
    ring
  rw [integral_map (measurable_studentPair F).aemeasurable (by fun_prop)]
  simp_rw [inner_studentPair F t, ← hm, ← hv]
  rw [← hg, hval]

/-! ### The deterministic core of (M2): the studentizing factor is its own Taylor polynomial

`studentizedRootCDF_eq_vecRootLaw` shows the studentized root is the *exact* smooth function
`(u, x) ↦ u (1 + x)^{-1/2}` of the bivariate mean, with `x = v n^{-1/2} − u² n^{-1}` on the
standardized scale. Item (M2) asks to replace it by its Taylor surrogate
`T̃_n = u − u v n^{-1/2}/2` with an error that is `O(n^{-1})` *uniformly*, and it has two halves:
a deterministic pointwise bound, and a probabilistic tail estimate on the polynomial that bound
produces. The deterministic half is closed here, with explicit constants and no smallness
assumption beyond `|x| ≤ 1/2`.

The proof is purely algebraic; no calculus and no mean value theorem are used. Substituting
`a = √(1 + x)`, so that `x = a² − 1`,

`(1 + x)^{-1/2} − (1 − x/2) = a⁻¹ − 1 + (a² − 1)/2 = (a³ − 3a + 2)/(2a) = (a − 1)²(a + 2)/(2a)`

while `x² = (a − 1)²(a + 1)²`, so the claim is the elementary inequality
`(a + 2)/(2a) ≤ (a + 1)²`, valid on the range `a ≥ 0.7` that `|x| ≤ 1/2` forces. Writing the
remainder as an explicit product of a square and a polynomial is what makes the estimate
uniform in `x`, which is what (M2) needs and what a Taylor-with-Lagrange-remainder statement
would not directly give. -/

/-- **Uniform second-order Taylor bound for the studentizing factor.**
`|(1 + x)^{-1/2} − (1 − x/2)| ≤ x²` for `|x| ≤ 1/2`. -/
theorem abs_inv_sqrt_one_add_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |(Real.sqrt (1 + x))⁻¹ - (1 - x / 2)| ≤ x ^ 2 := by
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  have h1x : (0 : ℝ) < 1 + x := by linarith
  set a : ℝ := Real.sqrt (1 + x) with ha
  have hapos : 0 < a := Real.sqrt_pos.2 h1x
  have hasq : a ^ 2 = 1 + x := Real.sq_sqrt h1x.le
  have hxa : x = a ^ 2 - 1 := by linarith
  have ha7 : (0.7 : ℝ) ≤ a := by nlinarith [hasq, hapos, sq_nonneg (a - 0.7)]
  have hkey : a⁻¹ - (1 - x / 2) = (a - 1) ^ 2 * (a + 2) / (2 * a) := by
    rw [hxa]
    field_simp
    ring
  have hx2eq : x ^ 2 = (a - 1) ^ 2 * (a + 1) ^ 2 := by rw [hxa]; ring
  rw [hkey, hx2eq, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  have hpoly : (0 : ℝ) ≤ 2 * a ^ 3 + 4 * a ^ 2 + a - 2 := by nlinarith [ha7, hapos]
  nlinarith [mul_nonneg (sq_nonneg (a - 1)) hpoly]

/-- **The pointwise polynomial replacement for the studentized root.**

With `r = n^{-1/2}` and `x = v r − u² r²` the exact studentized root is `u (1 + x)^{-1/2}` and
its Taylor surrogate is `u − u v r / 2`; the two differ by at most

`|u|³ r²/2 + |u| x²`,

which is `O(n^{-1})` times a polynomial in the two coordinates. The first term is the *cubic*
correction that the surrogate discards — it is exactly what makes the studentized `n^{-1/2}`
coefficient `(1/6)γ(2t² + 1)` differ from the centred one — and the second is the genuine
second-order remainder.

This is (M2)(i) with the probability removed. What is still missing for (M2) is the tail
estimate `P(|u|³ r²/2 + |u| x² > ε n^{-1}) = O(n^{-1})` for the bivariate root, which under a
fourth moment only requires truncating the summands at level `√n`, and the anti-concentration
of the surrogate's law. -/
theorem abs_studentFactor_sub_taylor_le (u v r : ℝ)
    (hx : |v * r - u ^ 2 * r ^ 2| ≤ 1 / 2) :
    |u * (Real.sqrt (1 + (v * r - u ^ 2 * r ^ 2)))⁻¹ - (u - u * v * r / 2)|
      ≤ |u| ^ 3 * r ^ 2 / 2 + |u| * (v * r - u ^ 2 * r ^ 2) ^ 2 := by
  set x : ℝ := v * r - u ^ 2 * r ^ 2 with hxdef
  have hsplit : u * (Real.sqrt (1 + x))⁻¹ - (u - u * v * r / 2)
      = u * ((Real.sqrt (1 + x))⁻¹ - (1 - x / 2)) + u ^ 3 * r ^ 2 / 2 := by
    rw [hxdef]
    ring
  have habs3 : |u ^ 3 * r ^ 2 / 2| = |u| ^ 3 * r ^ 2 / 2 := by
    rw [abs_div, abs_mul, abs_pow, abs_pow, sq_abs]
    norm_num
  calc |u * (Real.sqrt (1 + x))⁻¹ - (u - u * v * r / 2)|
      = |u * ((Real.sqrt (1 + x))⁻¹ - (1 - x / 2)) + u ^ 3 * r ^ 2 / 2| := by rw [hsplit]
    _ ≤ |u * ((Real.sqrt (1 + x))⁻¹ - (1 - x / 2))| + |u ^ 3 * r ^ 2 / 2| := abs_add_le _ _
    _ = |u| * |(Real.sqrt (1 + x))⁻¹ - (1 - x / 2)| + |u| ^ 3 * r ^ 2 / 2 := by
        rw [abs_mul, habs3]
    _ ≤ |u| * x ^ 2 + |u| ^ 3 * r ^ 2 / 2 := by
        have hstep :=
          mul_le_mul_of_nonneg_left (abs_inv_sqrt_one_add_sub_le hx) (abs_nonneg u)
        linarith
    _ = |u| ^ 3 * r ^ 2 / 2 + |u| * x ^ 2 := by ring

/-! ### (M2) re-derived: the second-order surrogate is not accurate enough, and the
third-order one is

Wave 13 recorded the remaining half of (M2) as the tail estimate
`P(|u|³r²/2 + |u|x² > εn⁻¹) = O(n⁻¹)`. **That claim is false**, and the reason is arithmetic
rather than technical. With `r = n^{-1/2}` the first term is `|u|³/(2n)`, so

`{|u|³ r²/2 > ε n⁻¹} = {|u|³ > 2ε}`,

an event of probability bounded away from `0`: under the central limit theorem `u` converges
to a nondegenerate Gaussian, so `P(|u|³ > 2ε) → P(|N(0,σ²)|³ > 2ε) > 0` for every fixed
`ε > 0`. No truncation of the summands can repair this — the failure is at the level of the
limit law, not of the tails.

What the arithmetic actually says is that the *deterministic* input has to be one order
better. Chasing the constants: if the surrogate is `H` and `|T̃ − H| ≤ Q · n^{-α}` with `Q` a
random variable having `p` moments, then splitting at `λ` gives an error
`P(Q > λ n^{α−1}) + sup_x P(H ∈ (x, x + λ n^{-1}])`, i.e. `≈ λ⁻ᵖ n^{p(1−α)} + λ n^{-1}`, which
is `O(n^{-1})` only if `α > 1`. The second-order surrogate has `α = 1` exactly, and *no* choice
of `λ` works; the third-order surrogate has `α = 3/2`, and then `λ = √n` with `p = 2` gives
`O(n^{-1})` on both sides. This is why Hall's smooth-function expansions retain the quadratic
term of the delta-method Taylor polynomial even for a *one-term* expansion.

The two results below supply that third-order deterministic core, by the same purely algebraic
substitution `a = √(1 + x)` that closed the second-order one: the remainder is exhibited as an
explicit product `(a − 1)³ · (polynomial)/(8a)`, so the estimate is uniform in `x` and no
calculus is involved. `abs_studentFactor_sub_taylor3_le'` then puts it in the shape the
probability consumes — an explicit `r³` times a polynomial in the two coordinates. -/

private lemma abs_sub_le_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  rwa [← sub_eq_add_neg, abs_neg] at h

/-- **Uniform third-order Taylor bound for the studentizing factor.**
`|(1 + x)^{-1/2} − (1 − x/2 + 3x²/8)| ≤ |x|³` for `|x| ≤ 1/2`.

Substituting `a = √(1 + x)` turns the remainder into `−(a − 1)³(3a² + 9a + 8)/(8a)` and `|x|³`
into `|a − 1|³(a + 1)³`, so the claim is the elementary `(3a² + 9a + 8) ≤ 8a(a + 1)³` on the
range `a ≥ 0.7` that `|x| ≤ 1/2` forces. -/
theorem abs_inv_sqrt_one_add_sub_taylor3_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |(Real.sqrt (1 + x))⁻¹ - (1 - x / 2 + 3 * x ^ 2 / 8)| ≤ |x| ^ 3 := by
  obtain ⟨hx1, hx2⟩ := abs_le.1 hx
  have h1x : (0 : ℝ) < 1 + x := by linarith
  set a : ℝ := Real.sqrt (1 + x) with ha
  have hapos : 0 < a := Real.sqrt_pos.2 h1x
  have hasq : a ^ 2 = 1 + x := Real.sq_sqrt h1x.le
  have hxa : x = a ^ 2 - 1 := by linarith
  have ha7 : (0.7 : ℝ) ≤ a := by nlinarith [hasq, hapos, sq_nonneg (a - 0.7)]
  have hkey : a⁻¹ - (1 - x / 2 + 3 * x ^ 2 / 8)
      = -((a - 1) ^ 3 * (3 * a ^ 2 + 9 * a + 8)) / (8 * a) := by
    rw [hxa]
    field_simp
    ring
  have hpolypos : (0 : ℝ) < 3 * a ^ 2 + 9 * a + 8 := by nlinarith [hapos]
  have hx3 : |x| ^ 3 = |a - 1| ^ 3 * (a + 1) ^ 3 := by
    have hfac : x = (a - 1) * (a + 1) := by rw [hxa]; ring
    rw [hfac, abs_mul, mul_pow, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a + 1)]
  have habs : |(-((a - 1) ^ 3 * (3 * a ^ 2 + 9 * a + 8))) / (8 * a)|
      = |a - 1| ^ 3 * (3 * a ^ 2 + 9 * a + 8) / (8 * a) := by
    rw [abs_div, abs_neg, abs_mul, abs_pow, abs_of_pos hpolypos,
      abs_of_pos (by linarith : (0 : ℝ) < 8 * a)]
  rw [hkey, habs, hx3, div_le_iff₀ (by positivity)]
  have hpoly : (0 : ℝ) ≤ 8 * a ^ 4 + 24 * a ^ 3 + 21 * a ^ 2 - a - 8 := by
    nlinarith [ha7, hapos, sq_nonneg (a - 0.7)]
  nlinarith [mul_nonneg (pow_nonneg (abs_nonneg (a - 1)) 3) hpoly]

/-- **The third-order pointwise polynomial replacement for the studentized root.**

With `r = n^{-1/2}` and `x = v r − u² r²`, the exact studentized root `u (1 + x)^{-1/2}` differs
from the *quadratic* delta-method surrogate

`H = u − u v r/2 + u³ r²/2 + 3 u v² r²/8`

by at most `|u| |x|³ + (3/4)|u|³|v| r³ + (3/8)|u|⁵ r⁴`. The last two terms are the `r³` and `r⁴`
parts of `u(1 − x/2 + 3x²/8)` that `H` discards.

Unlike `abs_studentFactor_sub_taylor_le`, whose error is `O(r²) = O(n⁻¹)` and therefore of the
same order as the accuracy being claimed, this error is `O(r³) = O(n^{-3/2})` — one power
better, which is exactly the margin the split into a tail event and an anti-concentration
interval consumes. -/
theorem abs_studentFactor_sub_taylor3_le (u v r : ℝ)
    (hx : |v * r - u ^ 2 * r ^ 2| ≤ 1 / 2) :
    |u * (Real.sqrt (1 + (v * r - u ^ 2 * r ^ 2)))⁻¹
        - (u - u * v * r / 2 + u ^ 3 * r ^ 2 / 2 + 3 * u * v ^ 2 * r ^ 2 / 8)|
      ≤ |u| * |v * r - u ^ 2 * r ^ 2| ^ 3
        + 3 / 4 * |u| ^ 3 * |v| * |r| ^ 3 + 3 / 8 * |u| ^ 5 * |r| ^ 4 := by
  set x : ℝ := v * r - u ^ 2 * r ^ 2 with hxdef
  have hsplit : u * (Real.sqrt (1 + x))⁻¹
        - (u - u * v * r / 2 + u ^ 3 * r ^ 2 / 2 + 3 * u * v ^ 2 * r ^ 2 / 8)
      = u * ((Real.sqrt (1 + x))⁻¹ - (1 - x / 2 + 3 * x ^ 2 / 8))
        - 3 / 4 * (u ^ 3 * v * r ^ 3) + 3 / 8 * (u ^ 5 * r ^ 4) := by
    rw [hxdef]
    ring
  have habs3 : |3 / 4 * (u ^ 3 * v * r ^ 3)| = 3 / 4 * |u| ^ 3 * |v| * |r| ^ 3 := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    ring
  have habs4 : |3 / 8 * (u ^ 5 * r ^ 4)| = 3 / 8 * |u| ^ 5 * |r| ^ 4 := by
    rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 8)]
    ring
  calc |u * (Real.sqrt (1 + x))⁻¹
          - (u - u * v * r / 2 + u ^ 3 * r ^ 2 / 2 + 3 * u * v ^ 2 * r ^ 2 / 8)|
      = |u * ((Real.sqrt (1 + x))⁻¹ - (1 - x / 2 + 3 * x ^ 2 / 8))
          - 3 / 4 * (u ^ 3 * v * r ^ 3) + 3 / 8 * (u ^ 5 * r ^ 4)| := by rw [hsplit]
    _ ≤ |u * ((Real.sqrt (1 + x))⁻¹ - (1 - x / 2 + 3 * x ^ 2 / 8))
          - 3 / 4 * (u ^ 3 * v * r ^ 3)| + |3 / 8 * (u ^ 5 * r ^ 4)| := abs_add_le _ _
    _ ≤ |u * ((Real.sqrt (1 + x))⁻¹ - (1 - x / 2 + 3 * x ^ 2 / 8))|
          + |3 / 4 * (u ^ 3 * v * r ^ 3)| + |3 / 8 * (u ^ 5 * r ^ 4)| := by
        linarith [abs_sub_le_add_abs
          (u * ((Real.sqrt (1 + x))⁻¹ - (1 - x / 2 + 3 * x ^ 2 / 8)))
          (3 / 4 * (u ^ 3 * v * r ^ 3))]
    _ = |u| * |(Real.sqrt (1 + x))⁻¹ - (1 - x / 2 + 3 * x ^ 2 / 8)|
          + 3 / 4 * |u| ^ 3 * |v| * |r| ^ 3 + 3 / 8 * |u| ^ 5 * |r| ^ 4 := by
        rw [abs_mul, habs3, habs4]
    _ ≤ |u| * |x| ^ 3 + 3 / 4 * |u| ^ 3 * |v| * |r| ^ 3 + 3 / 8 * |u| ^ 5 * |r| ^ 4 := by
        have hstep := mul_le_mul_of_nonneg_left
          (abs_inv_sqrt_one_add_sub_taylor3_le hx) (abs_nonneg u)
        linarith

/-- **The third-order replacement, in the shape the probability consumes.**
For `0 ≤ r ≤ 1` the error of the quadratic delta-method surrogate is `r³` times an explicit
polynomial in the two coordinates:

`|T̃ − H| ≤ r³ (4|u||v|³ + 4|u|⁷ + (3/4)|u|³|v| + (3/8)|u|⁵)`.

Combined with a second moment for the bracket — which is where truncation of the summands at
level `√n` enters, since the bracket involves powers of the coordinates beyond the fourth —
Markov's inequality at the level `λ = √n` gives `P(|T̃ − H| > n⁻¹) = O(n⁻¹)`, and the companion
anti-concentration estimate `sup_x P(H ∈ (x, x + n⁻¹]) = O(n⁻¹)` completes (M2). -/
theorem abs_studentFactor_sub_taylor3_le' (u v r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : |v * r - u ^ 2 * r ^ 2| ≤ 1 / 2) :
    |u * (Real.sqrt (1 + (v * r - u ^ 2 * r ^ 2)))⁻¹
        - (u - u * v * r / 2 + u ^ 3 * r ^ 2 / 2 + 3 * u * v ^ 2 * r ^ 2 / 8)|
      ≤ r ^ 3 * (4 * |u| * |v| ^ 3 + 4 * |u| ^ 7
          + 3 / 4 * |u| ^ 3 * |v| + 3 / 8 * |u| ^ 5) := by
  have habsr : |r| = r := abs_of_nonneg hr
  have hxle : |v * r - u ^ 2 * r ^ 2| ≤ |v| * r + u ^ 2 * r ^ 2 := by
    calc |v * r - u ^ 2 * r ^ 2| ≤ |v * r| + |u ^ 2 * r ^ 2| := abs_sub_le_add_abs _ _
      _ = |v| * r + u ^ 2 * r ^ 2 := by
          rw [abs_mul, abs_mul, habsr, abs_of_nonneg (sq_nonneg u),
            abs_of_nonneg (sq_nonneg r)]
  have hcube : |v * r - u ^ 2 * r ^ 2| ^ 3
      ≤ 4 * (|v| ^ 3 * r ^ 3 + |u| ^ 6 * r ^ 6) := by
    have h0 : (0 : ℝ) ≤ |v| * r := mul_nonneg (abs_nonneg v) hr
    have h1 : (0 : ℝ) ≤ u ^ 2 * r ^ 2 := by positivity
    have hmono : |v * r - u ^ 2 * r ^ 2| ^ 3 ≤ (|v| * r + u ^ 2 * r ^ 2) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) hxle 3
    have hconv : (|v| * r + u ^ 2 * r ^ 2) ^ 3
        ≤ 4 * ((|v| * r) ^ 3 + (u ^ 2 * r ^ 2) ^ 3) := by nlinarith [sq_nonneg (|v| * r
          - u ^ 2 * r ^ 2), h0, h1]
    have he : (|v| * r) ^ 3 + (u ^ 2 * r ^ 2) ^ 3 = |v| ^ 3 * r ^ 3 + |u| ^ 6 * r ^ 6 := by
      have hu : (u ^ 2) ^ 3 = |u| ^ 6 := by
        rw [← sq_abs u, ← pow_mul]
      rw [mul_pow, mul_pow, hu]
      ring
    calc |v * r - u ^ 2 * r ^ 2| ^ 3 ≤ (|v| * r + u ^ 2 * r ^ 2) ^ 3 := hmono
      _ ≤ 4 * ((|v| * r) ^ 3 + (u ^ 2 * r ^ 2) ^ 3) := hconv
      _ = 4 * (|v| ^ 3 * r ^ 3 + |u| ^ 6 * r ^ 6) := by rw [he]
  have hr6 : r ^ 6 ≤ r ^ 3 := pow_le_pow_of_le_one hr hr1 (by norm_num)
  have hr4 : r ^ 4 ≤ r ^ 3 := pow_le_pow_of_le_one hr hr1 (by norm_num)
  refine (abs_studentFactor_sub_taylor3_le u v r hx).trans ?_
  rw [habsr]
  have hu0 : (0 : ℝ) ≤ |u| := abs_nonneg u
  have h1 : |u| * |v * r - u ^ 2 * r ^ 2| ^ 3
      ≤ |u| * (4 * (|v| ^ 3 * r ^ 3 + |u| ^ 6 * r ^ 3)) := by
    refine mul_le_mul_of_nonneg_left (hcube.trans ?_) hu0
    have : |u| ^ 6 * r ^ 6 ≤ |u| ^ 6 * r ^ 3 :=
      mul_le_mul_of_nonneg_left hr6 (by positivity)
    linarith
  have h2 : 3 / 8 * |u| ^ 5 * r ^ 4 ≤ 3 / 8 * |u| ^ 5 * r ^ 3 :=
    mul_le_mul_of_nonneg_left hr4 (by positivity)
  nlinarith [h1, h2, hu0]

/-! ### (M2), the assembly: a distribution function is stable under a small perturbation

The split the corrected (M2) runs on, isolated as a statement about two arbitrary random
variables on a probability space: the distribution functions of `S` and `T` differ by at most
the probability that they are `δ`-apart plus the mass `T` puts on a `2δ`-window. Both halves of
what is left of (M2) — the moment bound feeding Markov's inequality on the first term, and the
anti-concentration bound on the second — are hypotheses of this lemma rather than parts of it,
so the assembly no longer has to be redone once they are available. -/

/-- **Distribution functions are stable under a small perturbation.**
`|P(S ≤ x) − P(T ≤ x)| ≤ P(|S − T| > δ) + P(x − δ < T ≤ x + δ)`, for any two measurable real
random variables and any `δ ≥ 0`. -/
theorem abs_measure_le_sub_le_of_dist_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {S T : Ω → ℝ} (hS : Measurable S) (hT : Measurable T)
    {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) :
    |(P {ω | S ω ≤ x}).toReal - (P {ω | T ω ≤ x}).toReal|
      ≤ (P {ω | δ < |S ω - T ω|}).toReal
        + (P {ω | x - δ < T ω ∧ T ω ≤ x + δ}).toReal := by
  set A : Set Ω := {ω | S ω ≤ x} with hA
  set B : Set Ω := {ω | T ω ≤ x} with hB
  set C : Set Ω := {ω | x - δ < T ω ∧ T ω ≤ x + δ} with hC
  set D : Set Ω := {ω | δ < |S ω - T ω|} with hD
  have hfin : ∀ s : Set Ω, P s ≠ ⊤ := fun s => (measure_lt_top P s).ne
  have hsub1 : A ⊆ B ∪ C ∪ D := by
    intro ω hω
    have hωx : S ω ≤ x := hω
    by_cases hd : δ < |S ω - T ω|
    · exact Or.inr hd
    · obtain ⟨hlo, _⟩ := abs_le.1 (not_lt.1 hd)
      by_cases hb : T ω ≤ x
      · exact Or.inl (Or.inl hb)
      · have hb' : x < T ω := not_le.1 hb
        have hmem : x - δ < T ω ∧ T ω ≤ x + δ := ⟨by linarith, by linarith⟩
        exact Or.inl (Or.inr hmem)
  have hsub2 : B ⊆ A ∪ C ∪ D := by
    intro ω hω
    have hωx : T ω ≤ x := hω
    by_cases hd : δ < |S ω - T ω|
    · exact Or.inr hd
    · obtain ⟨_, hhi⟩ := abs_le.1 (not_lt.1 hd)
      by_cases hc : x - δ < T ω
      · have hmem : x - δ < T ω ∧ T ω ≤ x + δ := ⟨hc, by linarith⟩
        exact Or.inl (Or.inr hmem)
      · have hc' : T ω ≤ x - δ := not_lt.1 hc
        have hmem : S ω ≤ x := by linarith
        exact Or.inl (Or.inl hmem)
  have hbound : ∀ U V W X : Set Ω, U ⊆ V ∪ W ∪ X →
      (P U).toReal ≤ (P V).toReal + (P W).toReal + (P X).toReal := by
    intro U V W X hUsub
    have h1 : P U ≤ P V + P W + P X :=
      (measure_mono hUsub).trans
        ((measure_union_le _ _).trans (add_le_add (measure_union_le V W) (le_refl (P X))))
    have hne : P V + P W + P X ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hfin V, hfin W⟩, hfin X⟩
    have h2 := ENNReal.toReal_mono hne h1
    rwa [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hfin V, hfin W⟩) (hfin X),
      ENNReal.toReal_add (hfin V) (hfin W)] at h2
  have h1 := hbound A B C D hsub1
  have h2 := hbound B A C D hsub2
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-! ### The anti-concentration hypothesis is free

Wave 14's note recorded the anti-concentration `sup_x P(H_n ∈ (x, x + n⁻¹]) = O(n⁻¹)` for the
delta-method surrogate as one of the two things left of (M2), to be obtained by "first proving a
cruder `O(n^{-1/2})` expansion and bootstrapping". **That is both unnecessary and insufficient**,
and the reason is arithmetic. A Berry–Esseen-grade bound `|P(H_n ≤ x) − Φ(x)| ≤ Cn^{-1/2}` gives
only `P(H_n ∈ (x, x + n⁻¹]) ≤ C'n⁻¹ + 2Cn^{-1/2} = O(n^{-1/2})`, one whole order short of what
the assembly consumes; a cruder expansion can never produce a finer interval bound than its own
accuracy.

What is true is better: anti-concentration at scale `n⁻¹` is a **corollary of the very expansion
the route is proving for `H_n`**, and therefore costs nothing. `measure_Ioc_le_of_abs_cdf_sub_le`
below is the observation, in the general form: if the distribution function of `T` is within `ε`
of an `A`-Lipschitz comparison function `G`, then `T` puts at most `A(b − a) + 2ε` on `(a, b]`.
Applied with `T = H_n`, `G` the Edgeworth approximant (Lipschitz uniformly in `n` by
`setIntegral_abs_edgeworthDensity_le`) and `ε = C/n` — which is exactly the conclusion of the
(M1)(b) route for `H_n`, needed anyway — it yields `A n⁻¹ + 2Cn⁻¹`, as required. There is no
circularity: the expansion for `H_n` is proved first, by characteristic functions, and the
anti-concentration is read off it afterwards. -/

/-- **Anti-concentration from an approximate distribution function.** If `|P(T ≤ x) − G(x)| ≤ ε`
uniformly and `G` has Lipschitz constant `A`, then `P(a < T ≤ b) ≤ A(b − a) + 2ε`. -/
theorem measure_Ioc_le_of_abs_cdf_sub_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {T : Ω → ℝ} (hT : Measurable T) {G : ℝ → ℝ} {A ε : ℝ}
    (hG : ∀ a b : ℝ, a ≤ b → G b - G a ≤ A * (b - a))
    (happrox : ∀ x : ℝ, |(P {ω | T ω ≤ x}).toReal - G x| ≤ ε)
    {a b : ℝ} (hab : a ≤ b) :
    (P {ω | a < T ω ∧ T ω ≤ b}).toReal ≤ A * (b - a) + 2 * ε := by
  have hSa : MeasurableSet {ω | T ω ≤ a} := hT measurableSet_Iic
  have hC : MeasurableSet {ω | a < T ω ∧ T ω ≤ b} := hT measurableSet_Ioc
  have hdisj : Disjoint {ω | T ω ≤ a} {ω | a < T ω ∧ T ω ≤ b} := by
    rw [Set.disjoint_left]
    rintro ω hω ⟨hω', -⟩
    exact absurd hω (not_le.2 hω')
  have hunion : {ω | T ω ≤ a} ∪ {ω | a < T ω ∧ T ω ≤ b} = {ω | T ω ≤ b} := by
    ext ω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (h | ⟨-, h⟩)
      · linarith
      · exact h
    · intro h
      rcases le_or_gt (T ω) a with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', h⟩
  have htoreal : (P {ω | a < T ω ∧ T ω ≤ b}).toReal
      = (P {ω | T ω ≤ b}).toReal - (P {ω | T ω ≤ a}).toReal := by
    rw [← hunion, measure_union hdisj hC,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    ring
  have h1 := abs_le.1 (happrox b)
  have h2 := abs_le.1 (happrox a)
  have h3 := hG a b hab
  rw [htoreal]
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The corrected (M2) assembly.** The anti-concentration term of
`abs_measure_le_sub_le_of_dist_le` is discharged by the approximation of `T`'s distribution
function itself: if `|P(T ≤ x) − G(x)| ≤ ε` uniformly with `G` `A`-Lipschitz, then

`|P(S ≤ x) − G(x)| ≤ P(|S − T| > δ) + 2Aδ + 3ε`.

With `T = H_n` the delta-method surrogate, `G` the Edgeworth approximant, `ε = C/n` and
`δ = n⁻¹`, every term but the first is `O(n⁻¹)` automatically — so what (M2) really needs is
*only* the tail bound `P(|T̃_n − H_n| > n⁻¹) = O(n⁻¹)`, and nothing about anti-concentration. -/
theorem abs_measure_le_sub_le_of_cdf_approx {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {S T : Ω → ℝ} (hS : Measurable S) (hT : Measurable T)
    {G : ℝ → ℝ} {A ε δ : ℝ} (hδ : 0 ≤ δ)
    (hG : ∀ a b : ℝ, a ≤ b → G b - G a ≤ A * (b - a))
    (happrox : ∀ x : ℝ, |(P {ω | T ω ≤ x}).toReal - G x| ≤ ε) (x : ℝ) :
    |(P {ω | S ω ≤ x}).toReal - G x|
      ≤ (P {ω | δ < |S ω - T ω|}).toReal + 2 * A * δ + 3 * ε := by
  have hsplit := abs_measure_le_sub_le_of_dist_le P hS hT hδ x
  have hwin : (P {ω | x - δ < T ω ∧ T ω ≤ x + δ}).toReal ≤ A * (2 * δ) + 2 * ε := by
    have h := measure_Ioc_le_of_abs_cdf_sub_le P hT hG happrox
      (a := x - δ) (b := x + δ) (by linarith)
    have harg : x + δ - (x - δ) = 2 * δ := by ring
    rwa [harg] at h
  have hT' := abs_le.1 (happrox x)
  have hS' : |(P {ω | S ω ≤ x}).toReal - G x|
      ≤ |(P {ω | S ω ≤ x}).toReal - (P {ω | T ω ≤ x}).toReal|
        + |(P {ω | T ω ≤ x}).toReal - G x| :=
    abs_sub_le _ _ _
  have hTx := happrox x
  have hnn : (0 : ℝ) ≤ (P {ω | δ < |S ω - T ω|}).toReal := ENNReal.toReal_nonneg
  linarith

/-! ### The peeled assembly: what the corrected (M2) really needs

`abs_measure_le_sub_le_of_dist_le` splits at a **single** scale `δ`, and (see the note on
`edgeworth_studentized_uniform`) that split cannot reach `O(n⁻¹)` for the studentized root under
a finite fourth moment alone: `δ` is forced down to `n⁻¹` by the anti-concentration term, and at
that scale `P(|T̃ₙ − Hₙ| > n⁻¹)` is genuinely of order `n^{-1/3}`, not `n⁻¹`, because the second
coordinate `v` of the bivariate root has only two moments and its `v³` contribution to the
Taylor remainder is heavy-tailed.

The classical repair is not a better surrogate but a better *split*: peel dyadically, and use
that the two events are nearly independent. The symmetric difference `{S ≤ x} Δ {T ≤ x}` is
contained in `{|T − x| ≤ δ}` together with the strata `{2ᵏδ < |S − T|} ∩ {|T − x| ≤ 2^{k+1}δ}`
and a final tail — because on the symmetric difference `T` is always within `|S − T|` of `x`, so
a large discrepancy *forces* `T` to be correspondingly far from `x`. Each stratum is a **joint**
event: the window mass at scale `2^{k+1}δ` times the tail of `|S − T|` at scale `2ᵏδ`. With
`δ = n⁻¹`, window mass `≈ 2ᵏδ + n⁻¹` and tail `≈ (2ᵏδ n^{3/2})^{-2/3}`, the strata sum to
`O(n⁻¹)`, which the single-scale split cannot achieve.

The lemma below is that containment, as a statement about two arbitrary real random variables;
it is a strict strengthening of `abs_measure_le_sub_le_of_dist_le` (which is the case `K = 0`
after bounding each stratum by its tail factor alone). -/

/-- The dyadic index: if `δ < d ≤ 2^K δ` then `d` sits in some dyadic window
`(2ᵏδ, 2^{k+1}δ]` with `k < K`. -/
private lemma exists_dyadic_index {d δ : ℝ} (hδ : 0 < δ) {K : ℕ}
    (hlo : δ < d) (hhi : d ≤ 2 ^ K * δ) :
    ∃ k, k < K ∧ 2 ^ k * δ < d ∧ d ≤ 2 ^ (k + 1) * δ := by
  classical
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h] at hhi
      norm_num at hhi
      linarith
    · exact h
  set s : Finset ℕ := (Finset.range K).filter (fun k => 2 ^ k * δ < d) with hs
  have h0 : (0 : ℕ) ∈ s := by
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hK, ?_⟩
    simpa using hlo
  have hne : s.Nonempty := ⟨0, h0⟩
  set k := s.max' hne with hk
  have hkmem : k ∈ s := s.max'_mem hne
  obtain ⟨hkr, hklt⟩ := Finset.mem_filter.1 hkmem
  refine ⟨k, Finset.mem_range.1 hkr, hklt, ?_⟩
  by_cases hnext : k + 1 < K
  · by_contra hcon
    have hmem : k + 1 ∈ s :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 hnext, not_le.1 hcon⟩
    have hle := s.le_max' _ hmem
    omega
  · have hkK : k + 1 = K := by
      have := Finset.mem_range.1 hkr
      omega
    rw [hkK]
    exact hhi

/-- **The dyadically peeled perturbation bound.** For any two real random variables, any
`δ > 0` and any `K`,

`|P(S ≤ x) − P(T ≤ x)| ≤ P(|T − x| ≤ δ) + ∑_{k<K} P(2ᵏδ < |S − T|, |T − x| ≤ 2^{k+1}δ)
                        + P(2^K δ < |S − T|)`.

Each middle term is a **joint** event, which is what makes the estimate strictly stronger than
the single-scale split of `abs_measure_le_sub_le_of_dist_le`: a large discrepancy `|S − T|` only
matters where it can move `T` across `x`, and there `T` is far from `x` by the same amount. -/
theorem abs_measure_le_sub_le_of_peel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {S T : Ω → ℝ} {δ : ℝ} (hδ : 0 < δ) (K : ℕ) (x : ℝ) :
    |(P {ω | S ω ≤ x}).toReal - (P {ω | T ω ≤ x}).toReal|
      ≤ (P {ω | |T ω - x| ≤ δ}).toReal
        + ∑ k ∈ Finset.range K,
            (P {ω | 2 ^ k * δ < |S ω - T ω| ∧ |T ω - x| ≤ 2 ^ (k + 1) * δ}).toReal
        + (P {ω | 2 ^ K * δ < |S ω - T ω|}).toReal := by
  classical
  have hfin : ∀ s : Set Ω, P s ≠ ⊤ := fun s => (measure_lt_top P s).ne
  set W : Set Ω := ({ω | |T ω - x| ≤ δ} : Set Ω)
      ∪ (⋃ k ∈ Finset.range K,
          {ω | 2 ^ k * δ < |S ω - T ω| ∧ |T ω - x| ≤ 2 ^ (k + 1) * δ})
      ∪ {ω | 2 ^ K * δ < |S ω - T ω|} with hW
  have hkey : ∀ ω : Ω, |T ω - x| ≤ |S ω - T ω| → ω ∈ W := by
    intro ω hω
    rw [hW]
    rcases le_or_gt |S ω - T ω| δ with hd | hd
    · exact Set.mem_union_left _ (Set.mem_union_left _ (le_trans hω hd))
    · rcases lt_or_ge (2 ^ K * δ) |S ω - T ω| with hKlt | hKge
      · exact Set.mem_union_right _ hKlt
      · obtain ⟨k, hkK, hk1, hk2⟩ := exists_dyadic_index hδ hd hKge
        exact Set.mem_union_left _ (Set.mem_union_right _
          (Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 hkK, ⟨hk1, le_trans hω hk2⟩⟩))
  have hA : {ω | S ω ≤ x} ⊆ {ω | T ω ≤ x} ∪ W := by
    intro ω hω
    by_cases hb : T ω ≤ x
    · exact Set.mem_union_left _ hb
    · refine Set.mem_union_right _ (hkey ω ?_)
      have hb' : x < T ω := not_le.1 hb
      have hSx : S ω ≤ x := hω
      rw [abs_of_pos (by linarith : (0 : ℝ) < T ω - x), abs_sub_comm,
        abs_of_pos (by linarith : (0 : ℝ) < T ω - S ω)]
      linarith
  have hB : {ω | T ω ≤ x} ⊆ {ω | S ω ≤ x} ∪ W := by
    intro ω hω
    by_cases hb : S ω ≤ x
    · exact Set.mem_union_left _ hb
    · refine Set.mem_union_right _ (hkey ω ?_)
      have hb' : x < S ω := not_le.1 hb
      have hTx : T ω ≤ x := hω
      rcases eq_or_lt_of_le hTx with heq | hlt
      · rw [heq]
        simp only [sub_self, abs_zero]
        exact abs_nonneg _
      · rw [abs_of_neg (by linarith : T ω - x < 0),
          abs_of_pos (by linarith : (0 : ℝ) < S ω - T ω)]
        linarith
  have hsumne : (∑ k ∈ Finset.range K,
      P {ω | 2 ^ k * δ < |S ω - T ω| ∧ |T ω - x| ≤ 2 ^ (k + 1) * δ}) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun k _ => hfin _
  have hWle : P W ≤ P {ω | |T ω - x| ≤ δ}
      + (∑ k ∈ Finset.range K,
          P {ω | 2 ^ k * δ < |S ω - T ω| ∧ |T ω - x| ≤ 2 ^ (k + 1) * δ})
      + P {ω | 2 ^ K * δ < |S ω - T ω|} := by
    rw [hW]
    refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
    exact (measure_union_le _ _).trans
      (add_le_add le_rfl (measure_biUnion_finset_le _ _))
  have hWtoReal : (P W).toReal ≤ (P {ω | |T ω - x| ≤ δ}).toReal
      + ∑ k ∈ Finset.range K,
          (P {ω | 2 ^ k * δ < |S ω - T ω| ∧ |T ω - x| ≤ 2 ^ (k + 1) * δ}).toReal
      + (P {ω | 2 ^ K * δ < |S ω - T ω|}).toReal := by
    have hne : (P {ω | |T ω - x| ≤ δ}
        + (∑ k ∈ Finset.range K,
            P {ω | 2 ^ k * δ < |S ω - T ω| ∧ |T ω - x| ≤ 2 ^ (k + 1) * δ})
        + P {ω | 2 ^ K * δ < |S ω - T ω|}) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hfin _, hsumne⟩, hfin _⟩
    have h := ENNReal.toReal_mono hne hWle
    rwa [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hfin _, hsumne⟩) (hfin _),
      ENNReal.toReal_add (hfin _) hsumne,
      ENNReal.toReal_sum (fun k _ => hfin _)] at h
  have hbound : ∀ U V : Set Ω, U ⊆ V ∪ W →
      (P U).toReal ≤ (P V).toReal + (P W).toReal := by
    intro U V hUsub
    have h1 : P U ≤ P V + P W := (measure_mono hUsub).trans (measure_union_le _ _)
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin V, hfin W⟩) h1
    rwa [ENNReal.toReal_add (hfin V) (hfin W)] at h2
  have h1 := hbound _ _ hA
  have h2 := hbound _ _ hB
  rw [abs_sub_le_iff]
  constructor <;> linarith

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

/-! ## Anti-concentration of the centred root, at the `O(n⁻¹)` accuracy

The corrected (M2) needs, besides a moment bound, that the surrogate put `O(δ + n⁻¹)` mass on
an interval of length `δ`. For the *centred* root that is a corollary of the closed
`edgeworth_mean_uniform` and costs nothing beyond the Lipschitz modulus of the approximant,
which `setIntegral_abs_edgeworthDensity_le` already supplies with a constant independent of
`n`. This is the half of the anti-concentration companion that is not circular: the surrogate
of the studentized problem is a perturbation of this root, and what a later wave has to add is
only the transfer across that perturbation. -/

/-- **The Edgeworth approximant is Lipschitz, with a constant independent of `n`.**
`edgeworthCDF γ n b − edgeworthCDF γ n a ≤ (2π)^{-1/2}(1 + 66|γ|)(b − a)` for `a ≤ b`.

The approximant is the `densityCDF` of `edgeworthDensity` (`densityCDF_edgeworthDensity`), so
the increment is the integral of that density over `(a, b]`, and
`setIntegral_abs_edgeworthDensity_le` bounds it. -/
theorem edgeworthCDF_sub_le (γ : ℝ) {n : ℕ} (hn : 1 ≤ n) {a b : ℝ} (hab : a ≤ b) :
    edgeworthCDF γ n b - edgeworthCDF γ n a
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |γ|) * (b - a) := by
  have hint := integrable_edgeworthDensity γ n
  have hsplit : Set.Iic b = Set.Iic a ∪ Set.Ioc a b := by
    rw [Set.Iic_union_Ioc_eq_Iic hab]
  have hdisj : Disjoint (Set.Iic a) (Set.Ioc a b) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx' (by simp [Set.mem_Iic.1 hx])
  have hincr : edgeworthCDF γ n b - edgeworthCDF γ n a
      = ∫ y in Set.Ioc a b, edgeworthDensity γ n y := by
    rw [← densityCDF_edgeworthDensity, ← densityCDF_edgeworthDensity, densityCDF, densityCDF,
      hsplit, setIntegral_union hdisj measurableSet_Ioc hint.integrableOn hint.integrableOn]
    ring
  rw [hincr]
  calc ∫ y in Set.Ioc a b, edgeworthDensity γ n y
      ≤ ∫ y in Set.Ioc a b, |edgeworthDensity γ n y| :=
        integral_mono hint.integrableOn hint.abs.integrableOn fun y => le_abs_self _
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |γ|) * (b - a) :=
        setIntegral_abs_edgeworthDensity_le γ hn hab

/-- **Anti-concentration of the centred sample-mean root, to `O(n⁻¹)`.**
The root puts at most `C(b − a) + C/n` mass on `(a, b]`, uniformly in the interval and in `n`.

This is `edgeworth_mean_uniform` at the two endpoints plus `edgeworthCDF_sub_le`; the point is
that the additive term is `O(n⁻¹)` and not `O(n^{-1/2})`, which is what the corrected (M2)
consumes at the scale `δ = n⁻¹`. A Berry–Esseen bound would only give `O(n^{-1/2})` here and
would be useless for a one-term expansion. -/
theorem meanRootCDF_sub_le [IsProbabilityMeasure F]
    -- USER-INPUT: finite fourth moment of the sampling law
    (hF4 : MemLp (fun t : ℝ => t) 4 F)
    -- USER-INPUT: nonzero variance
    (hFvar : 0 < Var[fun t : ℝ => t; F])
    -- USER-INPUT: Cramér's condition
    (hCramer : CramerCondition F) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ a b : ℝ, a ≤ b →
      meanRootCDF F n b - meanRootCDF F n a ≤ C * (b - a) + C / n := by
  obtain ⟨C₀, hC₀, hC⟩ := edgeworth_mean_uniform hF4 hFvar hCramer
  set σ : ℝ := Real.sqrt Var[fun t : ℝ => t; F] with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hFvar
  set K : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * (1 + 66 * |skewness F|) with hKdef
  have hK0 : 0 < K := edgeworthTV_pos (skewness F)
  refine ⟨K / σ + 2 * C₀, by positivity, fun n hn a b hab => ?_⟩
  have hn1 : 1 ≤ n := hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have ha := hC n hn a
  have hb := hC n hn b
  rw [← edgeworthCDF_eq_approx F hFvar n a] at ha
  rw [← edgeworthCDF_eq_approx F hFvar n b] at hb
  have hAa := (abs_le.1 ha).1
  have hAb := (abs_le.1 hb).2
  have hlip : edgeworthCDF (skewness F) n (b / σ) - edgeworthCDF (skewness F) n (a / σ)
      ≤ K * (b / σ - a / σ) :=
    edgeworthCDF_sub_le (skewness F) hn1 (by gcongr)
  have hdiff : b / σ - a / σ = (b - a) / σ := by ring
  rw [hdiff] at hlip
  have hdivle : K * ((b - a) / σ) = K / σ * (b - a) := by ring
  rw [hdivle] at hlip
  have hmono : K / σ * (b - a) ≤ (K / σ + 2 * C₀) * (b - a) := by
    have hba : (0 : ℝ) ≤ b - a := by linarith
    nlinarith [hba, hC₀]
  have hcn : 2 * (C₀ / (n : ℝ)) ≤ (K / σ + 2 * C₀) / (n : ℝ) := by
    have h1 : 2 * (C₀ / (n : ℝ)) = 2 * C₀ / (n : ℝ) := by ring
    have h2 : (0 : ℝ) < K / σ := by positivity
    rw [h1]
    gcongr
    linarith
  linarith [hAa, hAb, hlip, hmono, hcn]

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
not proved here. It is strictly harder than `edgeworth_mean_uniform`, whose (E1)–(E4) are all
closed.

**Status after the wave-12 re-derivation: the bivariate expansion is no longer missing, and
the residual obstruction is smaller and different from the one recorded before.** Two pieces
of the route are now PROVED, and the earlier verdict "the bivariate Edgeworth expansion is the
single missing estimate" is superseded.

* (S1) **The bivariate expansion — CLOSED.** `ForMathlib/BivariateEdgeworth.lean` proves it
  axiom-clean, in an arbitrary real inner product space and hence in `ℝ²`:
  `charFun_vecRootLaw` (`φ_{vecRootLaw F Z n}(t) = φ_{F ∘ Z⁻¹}(n^{-1/2} • t)ⁿ`, direct on
  `Measure.pi` exactly as `charFun_meanRootLaw`), `norm_charFun_smul_le_exp_neg_sq` (the
  Gaussian window majorant) and `norm_charFun_smul_pow_sub_edgeworth_le` (the damped one-term
  expansion), assembled into `norm_charFun_vecRootLaw_sub_edgeworth_le`:
  `‖φ_{vecRootLaw}(t) − e^{−v(t)/2}(1 − i m₃(t) n^{-1/2}/6)‖ ≤ (damped remainder)`.
  *The recorded route is superseded, in the direction of being easier.* The note said this
  "needs a two-dimensional analogue of `norm_charFun_le_exp_neg_sq`". No two-dimensional
  argument is needed at all: `charFun_smul_eq_charFun_map_inner` shows that the restriction of
  `φ_μ` to the ray `s ↦ s • t` **is** the characteristic function of the one-dimensional
  projected law `μ ∘ ⟪·,t⟫⁻¹`, so every hypothesis and every conclusion of the one-dimensional
  theorems transfers verbatim, with the moments replaced by the directional moments
  `∫⟪x,t⟫^k` — which are precisely the contractions of the cumulant tensors with `t`. The one
  thing the note got right is that nondegeneracy is used: the window conditions are
  direction-dependent through `v(t) = ⟪Σt,t⟫`, and making the window uniform over directions
  needs `v(t) ≥ λ_min ‖t‖²`, i.e. a nonsingular covariance of `(X, X²)`.
* (S2) **The reduction of the studentized root to that bivariate mean — CLOSED, and exact.**
  `studentizedRootCDF_eq_vecRootLaw` above proves
  `studentizedRootCDF F n x = ρ_n{w : w₀/√(σ² + w₁ n^{-1/2} − w₀² n^{-1}) ≤ x}` with
  `ρ_n = vecRootLaw F (studentPair F) n` the law of the bivariate root of
  `Z(x) = (x − μ, (x − μ)² − σ²)`. There is no approximation in this step: it is the algebraic
  identity `n⁻¹∑(yᵢ − ȳ)² = n⁻¹∑(yᵢ − m)² − (ȳ − m)²` (`sampleVariance_eq_sub`) together with
  `sqrt_mul_sub_mean_eq`. So the delta-method function `(u, v) ↦ u/√(v − u²)` is not an
  approximation either; it is the exact statistic. `inner_studentPair` and
  `integral_inner_studentPair` supply the first of the hypotheses (S1) consumes for this pair:
  the directional expansion `⟪Z(x), t⟫ = t₀(x − μ) + t₁((x − μ)² − σ²)` and the fact that it is
  centred, `∫⟪w, t⟫ dρ = 0`, in **every** direction `t`.

**Re-derivation: what is left is three estimates, all of them about turning (S1) into a
statement about the curved region of (S2).** The following also re-confirms two facts that do
not change.

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

**Status after the wave-13 re-derivation.** Of the three estimates (M1), (M2), (M3) recorded
by wave 12, the two pieces that wave singled out as "the smallest genuinely missing one" and
"the compactness argument over the circle" are now PROVED, together with the whole
deterministic half of (M2). What survives is exactly three *probabilistic* items, listed at the
end. As before, two facts do not change and are re-confirmed:

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

The three estimates, and what is now proved of each:

* (M1) **The scalar route — (b) CLOSED, and (a) is confirmed not to be needed.** (S1) controls
  `φ_{ρ_n}` on rays, while (S2) asks for `ρ_n(R_n(x))` with `R_n(x)` a *curved* planar region.
  Wave 12 offered two ways across: *(a)* a multidimensional smoothing inequality
  (Bhattacharya–Rao) with a boundary-shell estimate over a non-convex region — still absent, and
  still not needed; *(b)* returning to the line by expanding the characteristic function of the
  scalar statistic, whose one missing ingredient was an expansion of `∂_s ψ_n(θ, s)|_{s=0}`,
  equivalently of `E[V e^{iθU}]`, which cannot be obtained by differentiating the (S1)
  inequality.
  *That ingredient is now proved*, in `ForMathlib/BivariateEdgeworth.lean`, and it turned out to
  be *easier* than (S1) rather than harder. The quantity is `mixCharFun μ b t = ∫ ⟪w,b⟫e^{i⟪w,t⟫}`,
  and it factorises **exactly** on a vector root (`mixCharFun_vecRootLaw`): the weight
  `n^{-1/2}∑ᵢ⟪Z(yᵢ),b⟫` is a sum, so the integrand splits into `n` products over the coordinates
  each with a single distinguished factor, and `integral_fintype_prod_eq_prod` evaluates every
  one of them. A first-order Taylor bound on the distinguished factor
  (`norm_mixCharFun_sub_mul_I_le`, costing exactly the one extra moment `∫|⟪x,b⟫|⟪x,t⟫²` that
  wave 12 predicted) then gives `norm_mixCharFun_vecRootLaw_sub_le`:
  `‖mix_{ρ_n}(b,a) − i κ φ(n^{-1/2}a)^{n−1}‖ ≤ 3M/(2√n)`, with `κ = ∫⟪x,b⟫⟪x,a⟫`.
  Note what the arithmetic says: the `√n` of the factorisation cancels the `n^{-1/2}` of the
  covariance in the rescaled direction, so the mixed quantity has a *nonvanishing* limit
  `iκe^{−v/2}` — this is the analytic source of the studentized coefficient
  `(1/6)γ(2t² + 1)` and of its difference from the centred one. **What is left of (M1)(b)** is
  only the replacement of `φ(n^{-1/2}a)^{n−1}` by `e^{−v/2}`: a Berry–Esseen-level estimate for
  an `(n−1)`-st power at the argument `n^{-1/2}`, off by one factor from
  `norm_charFun_smul_pow_sub_edgeworth_le`, plus the assembly of the two expansions into a
  smoothing inequality on the line.
* (M2) **The uniform polynomial replacement — the deterministic half CLOSED.** The target is
  `|P(H_n ≤ x) − P(T̃_n ≤ x)| ≤ C/n` uniformly in `x`, and it needs (i) a pointwise/tail bound
  on `H_n − T̃_n` and (ii) anti-concentration for `T̃_n`.
  *The deterministic content of (i) is now proved.* `abs_inv_sqrt_one_add_sub_le` gives the
  **uniform** second-order bound `|(1+x)^{-1/2} − (1 − x/2)| ≤ x²` on `|x| ≤ 1/2` — proved
  purely algebraically by substituting `a = √(1+x)`, which turns the remainder into
  `(a−1)²(a+2)/(2a)` and `x²` into `(a−1)²(a+1)²`, so that the whole claim is the elementary
  `(a+2)/(2a) ≤ (a+1)²` on `a ≥ 0.7`. No calculus and no Lagrange remainder are involved, and
  uniformity in `x` — the property (M2) actually needs — is manifest.
  `abs_studentFactor_sub_taylor_le` reads off, for `r = n^{-1/2}` and `x = vr − u²r²`,
  `|u(1+x)^{-1/2} − (u − uvr/2)| ≤ |u|³r²/2 + |u|x²`: an explicit `O(n⁻¹)` times a polynomial in
  the two coordinates, whose first term is precisely the cubic correction the surrogate
  discards. **What is left of (M2)** is the probability: the tail estimate
  `P(|u|³r²/2 + |u|x² > εn⁻¹) = O(n⁻¹)` for the bivariate root, which under a fourth moment only
  needs truncation of the summands at level `√n` (the classical delicate step;
  `ForMathlib/CombinatorialCLT` is the model), and the anti-concentration of `T̃_n`, for which
  the circularity is broken by first proving a cruder `O(n^{-1/2})` expansion.
* (M3) **The Cramér tail — the direction-uniformity CLOSED.** For the centred root the outer
  range was free because `|φ_{P_n}(ξ)| = |φ_{F₀}(ξ/√n)|ⁿ ≤ cⁿ` (`edgeworthGap_tail_le`); the
  studentized root's characteristic function is not a power, so `exists_bound_lt_one_of_cramer`
  does not apply. The bivariate law `ρ_n` *is* a normalised sum, and wave 12 recorded two gaps
  in exploiting that: uniformity in the direction on `‖t‖ ≥ ε`, and the transfer from `ρ_n` to
  the law of `H_n(W_n)`.
  *The first gap is now closed*, in the `VecCramer` section above. `VecCramerCondition` is the
  verbatim analogue of `CramerCondition` with `cocompact ℝ` replaced by `cocompact E`;
  `norm_charFun_lt_one_of_projLaw_cramer` shows the strict bound at a single nonzero direction
  is purely one-dimensional (`φ_μ(t) = φ_{projLaw μ t}(1)` at `s = 1 ≠ 0`); and
  `exists_bound_lt_one_of_vecCramer` runs the compactness argument — off a compact `K` the bound
  is the cocompact one, and on the compact `K ∩ {ε ≤ ‖t‖}` the continuous `‖φ_μ‖` attains a
  maximum at a point that is nonzero, hence `< 1`. This is the "compactness argument over the
  circle", in the form that is actually needed (over a compact annulus, which avoids controlling
  the radius separately). `cramerCondition_of_absolutelyContinuous` additionally supplies the
  Riemann–Lebesgue bridge `F ≪ volume → CramerCondition F`, so this theorem's hypothesis set is
  now formally stronger than `edgeworth_mean_uniform`'s.
  **What is left of (M3)** is (i) `VecCramerCondition` for the *specific* law of
  `studentPair F`. Wave 12's parenthetical "`hFac` supplies it because a nonconstant quadratic
  image of an absolutely continuous law is absolutely continuous" is **only correct for the
  directionwise conditions**, and multivariate Cramér is strictly stronger than Cramér in every
  direction: the law of `(X − μ, (X − μ)² − σ²)` is carried by a parabola and is singular in
  `ℝ²` however smooth `F` is, so Riemann–Lebesgue does not apply to it. On the axis `t₁ = 0` the
  condition is the one-dimensional one for `F`; for `t₁` away from `0` the phase `t₀y + t₁y²` is
  genuinely quadratic and the decay is a van der Corput second-derivative estimate; uniformity
  across the transition is the real content. And (ii) the transfer from `ρ_n` to the law of
  `H_n(W_n)` — Hall's device of conditioning on `n − k` of the coordinates.

In short: what wave 12 called "the smallest genuinely missing piece" (M1)(b), the compactness
half of (M3), and the whole deterministic half of (M2) are proved and axiom-clean. The residue
is three items that are all genuinely probabilistic — a one-factor Berry–Esseen bookkeeping for
`φ^{n−1}`, a truncation-based tail bound with its anti-concentration companion, and the
multivariate Cramér condition for a parabola-carried law together with Hall's conditioning.

**Status after the wave-14 re-derivation.** Of the three probabilistic residues wave 13 left,
the first is now CLOSED, the third has one of its two halves CLOSED and the other reduced to a
single named analytic fact, and the second has been found to be **stated falsely** and has been
replaced by a correct version whose deterministic half and whose assembly are both closed.

* (R1) **The one-factor bookkeeping for `φ^{n−1}` — CLOSED.** The `OneFactor` section of
  `ForMathlib/BivariateEdgeworth.lean` proves it axiom-clean and it is entirely elementary.
  `norm_charFun_sub_one_le` gives `‖φ_μ(t) − 1‖ ≤ (3/2)∫⟪x,t⟫²` for a law centred in the
  direction `t` — the centring is what makes this quadratic rather than linear, and hence what
  makes the whole correction `O(n⁻¹)` rather than `O(n^{-1/2})`, which at `O(n^{-1/2})` would
  have swamped the very coefficient the studentized expansion exists to produce. With
  `‖z^{n−1} − z^n‖ = ‖z‖^{n−1}‖1 − z‖ ≤ ‖1 − z‖` (`norm_pow_sub_pow_succ_le`) and the rescaled
  argument `c = n^{-1/2}a`, `norm_charFun_pow_sub_charFun_vecRootLaw_le` reads
  `‖φ(n^{-1/2}a)^{n−1} − φ_{ρ_n}(a)‖ ≤ (3/2)v/n`, and
  `norm_mixCharFun_vecRootLaw_sub_charFun_le` restates (M1)(b) against `φ_{ρ_n}(a)` itself:
  `‖mix_{ρ_n}(b,a) − iκ φ_{ρ_n}(a)‖ ≤ 3M/(2√n) + (3/2)|κ|v/n`. The surviving factor is now
  exactly the quantity `norm_charFun_vecRootLaw_sub_edgeworth_le` estimates, so the damped
  expansion applies to it verbatim and the two expansions add.
* (R2) **The truncation tail bound — the statement wave 13 recorded is FALSE, and the correct
  one needs a third-order surrogate, whose deterministic half and assembly are CLOSED.**
  Wave 13 asked for `P(|u|³r²/2 + |u|x² > εn⁻¹) = O(n⁻¹)`. With `r = n^{-1/2}` the first term
  is `|u|³/(2n)`, so that event is `{|u|³ > 2ε}`, whose probability converges to
  `P(|N(0,σ²)|³ > 2ε) > 0`. The failure is at the level of the limit law, so **no truncation of
  the summands can repair it**; the claim is false as stated for every fixed `ε > 0`.
  The arithmetic of the split explains what is really required. If `|T̃ₙ − Hₙ| ≤ Q n^{-α}` with
  `Q` having `p` moments, the two terms of `abs_measure_le_sub_le_of_dist_le` at scale
  `δ = λn⁻¹` are `≈ λ^{-p} n^{p(1−α)}` and `≈ λn⁻¹`, and their sum is `O(n⁻¹)` only when
  `α > 1`. The second-order surrogate has `α = 1` *exactly*, and no choice of `λ` works. The
  third-order surrogate has `α = 3/2`, and then `λ = √n` with `p = 2` gives `O(n⁻¹)` on both
  sides. This is exactly why Hall retains the quadratic term of the delta-method Taylor
  polynomial even for a *one-term* expansion; wave 13's second-order surrogate was one order
  too coarse for the accuracy claimed.
  Closed here, axiom-clean: `abs_inv_sqrt_one_add_sub_taylor3_le`
  (`|(1+x)^{-1/2} − (1 − x/2 + 3x²/8)| ≤ |x|³` on `|x| ≤ 1/2`, by the same purely algebraic
  substitution `a = √(1+x)`, the remainder coming out as `−(a−1)³(3a²+9a+8)/(8a)`),
  `abs_studentFactor_sub_taylor3_le` and `abs_studentFactor_sub_taylor3_le'` (the same in the
  shape the probability consumes, `|T̃ₙ − Hₙ| ≤ r³(4|u||v|³ + 4|u|⁷ + (3/4)|u|³|v| +
  (3/8)|u|⁵)`), and `abs_measure_le_sub_le_of_dist_le` (the assembly, for arbitrary random
  variables). **What is left of (M2)** is precisely the two hypotheses of the last of these: a
  second moment for that bracket — this is where truncation of the summands at level `√n`
  genuinely enters, the bracket carrying powers of the coordinates beyond the fourth — and the
  anti-concentration `sup_x P(Hₙ ∈ (x, x + n⁻¹]) = O(n⁻¹)`.
  Of the anti-concentration, the non-circular half is closed here too: `edgeworthCDF_sub_le`
  (the approximant is Lipschitz with a constant independent of `n`, read off from
  `setIntegral_abs_edgeworthDensity_le`) and `meanRootCDF_sub_le` give
  `P(root ∈ (a,b]) ≤ C(b − a) + C/n` for the **centred** root, uniformly in the interval and in
  `n`. That the additive term is `O(n⁻¹)` and not `O(n^{-1/2})` is the whole point, and it is
  what makes `edgeworth_mean_uniform` — rather than a Berry–Esseen bound, which would be
  useless here — the right input. What a later wave must add is only the transfer of this
  estimate across the `O_p(n^{-1/2})` perturbation `Hₙ − u`, and that is where the note's
  "break the circularity with a cruder `O(n^{-1/2})` expansion" belongs.
* (R3) **The Cramér residue — Hall's conditioning is NOT needed, and the remaining half is a
  single uniformity statement.** `norm_charFun_vecRootLaw_le_pow` shows that a uniform bound
  `‖φ_{F∘Z⁻¹}(t)‖ ≤ c` on `ε ≤ ‖t‖` transfers to `‖φ_{ρ_n}(t)‖ ≤ cⁿ` on `ε√n ≤ ‖t‖`, by
  `charFun_vecRootLaw` and nothing else: `ρ_n` *is* a normalised sum, so its characteristic
  function *is* an `n`-th power. **This overturns (M3)(ii).** Conditioning on `n − k`
  coordinates would be needed only for the law of a *nonlinear* functional of the root, and the
  (M1)(b) route never forms one — it works throughout with `charFun ρ_n` and `mixCharFun ρ_n`,
  both of which factorise exactly.
  For (M3)(i), `vecCramerCondition_of_uniform_sphere` writes the projection identity in polar
  form: `VecCramerCondition μ` follows from `‖φ_{projLaw μ θ}(R)‖ ≤ c < 1` for all unit `θ` and
  all large `R`. Since each projected law `ν_θ` is a nonconstant polynomial image of an
  absolutely continuous law and hence absolutely continuous, Riemann–Lebesgue gives the decay
  for every **fixed** direction. **What is left of (M3) is exactly that the decay be uniform
  over the compact sphere of directions** — a statement about a two-parameter oscillatory
  integral, provable either by the two-regime van der Corput argument or by total-variation
  continuity of `θ ↦ ν_θ` plus the uniformity of Riemann–Lebesgue on totally bounded subsets of
  `L¹`. Both routes give `limsup = 0`, strictly stronger than the `< 1` needed. Neither is
  available in Mathlib at present; this is the only genuinely analytic item left in the whole
  route.

Net after wave 14, the residue is two items rather than three, and neither is a bookkeeping
step: (i) a second moment for an explicit polynomial in the bivariate root together with the
anti-concentration of its surrogate, and (ii) uniform Riemann–Lebesgue over the sphere for the
parabola-carried law. Everything else in the chain — (S1), (S2), (M1)(a-not-needed), (M1)(b)
including the one-factor bookkeeping, the deterministic core and the assembly of (M2), and both
the direction-uniformity and the root transfer of (M3) — is proved and axiom-clean. -/
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
`edgeworth_studentized_uniform` — which, after the wave-14 re-derivation, is **two** items, not
three:

* a second moment for the explicit polynomial bracket of `abs_studentFactor_sub_taylor3_le'`
  (this is where truncation of the summands at level `√n` enters) together with the
  anti-concentration of the quadratic delta-method surrogate at scale `n⁻¹`;
* uniform Riemann–Lebesgue over the compact sphere of directions for the parabola-carried
  bivariate law, i.e. the hypothesis of `vecCramerCondition_of_uniform_sphere`.

Closed and axiom-clean over there: (S1) the bivariate expansion, (S2) the exact reduction of
the studentized root to a bivariate mean, (M1)(b) the mixed-characteristic-function expansion
*together with* the one-factor `φ^{n−1}` bookkeeping (`norm_mixCharFun_vecRootLaw_sub_charFun_le`),
the deterministic core and the assembly of (M2) in their corrected third-order form, the
direction-uniformity of (M3), and the transfer of the Cramér tail to the vector root
(`norm_charFun_vecRootLaw_le_pow`, which removes the need for Hall's conditioning device
altogether). -/
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
