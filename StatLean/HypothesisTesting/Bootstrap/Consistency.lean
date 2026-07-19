import StatLean.HypothesisTesting.Bootstrap.Defs
import StatLean.HypothesisTesting.ForMathlib.PolyaUniformCDF
import StatLean.HypothesisTesting.ForMathlib.QuantileFunction
import StatLean.HypothesisTesting.ForMathlib.LindebergCLT
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Bootstrap consistency: the sequence-class criterion

The bootstrap replaces the unknown law `P` by an estimate `Phat n` (typically the empirical
measure of the sample) inside the sampling distribution `J n` of a root. Consistency asks
that this substitution be asymptotically harmless. Following the sequence-class approach,
smoothness of `J` in its measure argument is expressed by a set of sequences `C_P` of laws:
along **every** sequence in `C_P` the sampling distribution functions converge to one and the
same continuous limit `Jlim`. The only stochastic ingredient is then that the estimated
sequence `n ↦ Phat n ω` belongs to `C_P` for almost every `ω`.

This file contains:

* `IsCDF` — the distribution-function predicate every `J n Q` is assumed to satisfy;
* `StrictIncAt` — strict increase of a distribution function at a point;
* `normalCDF`, `stdNormalCDF`, `stdNormalQuantile` — the Gaussian limit-law vocabulary used
  throughout the bootstrap cluster;
* `tendsto_supCDFDist_bootstrap` — almost sure uniform closeness of the bootstrap sampling
  distribution to the true one;
* `tendsto_bootstrapQuantile` — almost sure convergence of the bootstrap quantile;
* `tendsto_bootstrapCoverage` — asymptotic coverage of the bootstrap confidence set;
* `tendstoInMeasure_rowMean_triangular` — the triangular-array weak law used by the
  nonparametric-mean applications downstream.

**Reference.** Classical bootstrap consistency theory; original sources in the bibliographic
comments below.

**Designed deviation (metric-free formulation).** The reference tradition often describes
smoothness of `J` in `P` through a metric `d` on the space of laws (`d(P_n, P) → 0` implies
`J_n(P_n) ⇒ J(P)`). We deliberately keep the **sequence-class** form: `C_P` is an abstract set
of sequences, supplied as data together with its defining convergence property. This is the
weaker and more general of the two devices (any metric criterion produces such a class), it
avoids committing the library to one metric on measures, and it removes every measurability
requirement in the measure argument of `J`.

**Proof formalization notes.**
* The sampling-CDF field `J : ℕ → Measure 𝓧 → ℝ → ℝ` is theorem-level data. Its distribution
  function properties enter as the hypothesis `∀ n Q, IsCDF (J n Q)`; no measurability of
  `Q ↦ J n Q x` is ever assumed, which is what makes the almost-sure statements meaningful
  for a random `Phat n ω`.
* The uniform conclusion is the Polya step: pointwise convergence of distribution functions to
  a **continuous** limit upgrades to convergence in sup-distance. That upgrade is the sibling
  `PolyaUniformCDF` brick of this area (uniform convergence of monotone functions to a
  continuous limit); it is applied here to each fixed sequence in `C_P` and then transported
  to the random sequence on the almost sure event.
* The confidence set is the one attached to the root: `θ(P)` is covered exactly when the root
  evaluated at the true parameter does not exceed the estimated `1 − α` quantile. The coverage
  statement is phrased directly in that form, so no separate parameter-set machinery is needed.
* `IsCDF` deliberately omits `[0,1]`-valuedness: monotonicity together with the two tail limits
  forces it, so recording it as a field would be redundant.

**Bibliographic comments.** The bootstrap is due to B. Efron ("Bootstrap methods: another look
at the jackknife," *Ann. Statist.* **7** (1979), 1–26). Its first consistency theory is due to
P. J. Bickel and D. A. Freedman ("Some asymptotic theory for the bootstrap," *Ann. Statist.*
**9** (1981), 1196–1217) and K. Singh ("On the asymptotic accuracy of Efron's bootstrap,"
*Ann. Statist.* **9** (1981), 1187–1195). The formulation of consistency through classes of
converging sequences of laws follows R. Beran ("Bootstrap methods in statistics," *Jahresber.
Deutsch. Math.-Verein.* **86** (1984), 14–30) and D. N. Politis, J. P. Romano and M. Wolf,
*Subsampling*, Springer, 1999.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace StatLean.HypothesisTesting

variable {𝓧 Ω : Type*} [MeasurableSpace 𝓧] [MeasurableSpace Ω]

/-! ## Distribution-function vocabulary -/

/-- A real function is a **distribution function**: nondecreasing, right-continuous, with
limit `0` at `−∞` and limit `1` at `+∞`. (`[0,1]`-valuedness is a consequence, not a field.) -/
structure IsCDF (F : ℝ → ℝ) : Prop where
  /-- Constitutive: a distribution function is nondecreasing. -/
  mono : Monotone F
  /-- Constitutive: a distribution function is right-continuous. -/
  right_continuous : ∀ x : ℝ, ContinuousWithinAt F (Set.Ici x) x
  /-- Constitutive: a distribution function vanishes at `−∞`. -/
  tendsto_atBot : Tendsto F atBot (𝓝 0)
  /-- Constitutive: a distribution function tends to `1` at `+∞`. -/
  tendsto_atTop : Tendsto F atTop (𝓝 1)

/-- `F` is **strictly increasing at** `x₀`: strictly smaller to the left, strictly larger to
the right. This is the exact regularity that makes the `x₀`-level quantile unique, and it is
what quantile convergence needs on top of continuity of the limit law. -/
def StrictIncAt (F : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  (∀ y, y < x₀ → F y < F x₀) ∧ (∀ z, x₀ < z → F x₀ < F z)

/-- The **normal distribution function** with mean `m` and variance `v`. -/
noncomputable def normalCDF (m : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (gaussianReal m v (Set.Iic x)).toReal

/-- The **standard normal distribution function** `Φ`. -/
noncomputable def stdNormalCDF (x : ℝ) : ℝ := normalCDF 0 1 x

/-- The **standard normal quantile** `z_p = Φ⁻¹(p)`, via the generalized inverse. -/
noncomputable def stdNormalQuantile (p : ℝ) : ℝ := cdfPseudoInverse stdNormalCDF p

/-! ## Sup-CDF distance: elementary calculus -/

section SupCDFDist

variable {F G H : ℝ → ℝ}

/-- A distribution function takes values in `[0,1]` (a consequence of the fields, recorded
here for the boundedness estimates below). -/
private theorem IsCDF.mem_Icc (h : IsCDF F) (t : ℝ) : F t ∈ Set.Icc (0 : ℝ) 1 :=
  mem_Icc_of_monotone_of_tendsto h.mono h.tendsto_atBot h.tendsto_atTop t

/-- The pointwise `|F − G|` of two distribution functions is bounded above by `1`, hence the
sup defining `supCDFDist` is a genuine supremum. -/
private theorem bddAbove_absSub (hF : IsCDF F) (hG : IsCDF G) :
    BddAbove (Set.range fun t => |F t - G t|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hf := hF.mem_Icc t
  have hg := hG.mem_Icc t
  exact abs_le.mpr ⟨by linarith [hf.1, hf.2, hg.1, hg.2], by linarith [hf.1, hf.2, hg.1, hg.2]⟩

/-- `supCDFDist` is symmetric. -/
private theorem supCDFDist_comm (F G : ℝ → ℝ) : supCDFDist F G = supCDFDist G F := by
  unfold supCDFDist
  congr 1
  ext t
  rw [abs_sub_comm]

/-- Nonnegativity of the sup-CDF distance between two distribution functions. -/
private theorem supCDFDist_nonneg (hF : IsCDF F) (hG : IsCDF G) : 0 ≤ supCDFDist F G :=
  le_trans (abs_nonneg _) (le_ciSup (bddAbove_absSub hF hG) 0)

/-- Triangle inequality for the sup-CDF distance among distribution functions. -/
private theorem supCDFDist_triangle (hF : IsCDF F) (hG : IsCDF G) (hH : IsCDF H) :
    supCDFDist F H ≤ supCDFDist F G + supCDFDist G H := by
  refine ciSup_le (fun t => ?_)
  have h1 : |F t - G t| ≤ supCDFDist F G := le_ciSup (bddAbove_absSub hF hG) t
  have h2 : |G t - H t| ≤ supCDFDist G H := le_ciSup (bddAbove_absSub hG hH) t
  calc |F t - H t| ≤ |F t - G t| + |G t - H t| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-- **Pólya, sup-distance form.** If distribution functions `Fn` converge pointwise to a
continuous distribution function `F`, then their sup-CDF distance to `F` tends to `0`. -/
private theorem tendsto_supCDFDist_zero {Fn : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hFn : ∀ n, IsCDF (Fn n)) (hFcont : Continuous F) (hFcdf : IsCDF F)
    (hconv : ∀ x : ℝ, Tendsto (fun n => Fn n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => supCDFDist (Fn n) F) atTop (𝓝 0) := by
  have hunif : TendstoUniformly Fn F atTop :=
    tendstoUniformly_of_monotone_of_continuous (fun n => (hFn n).mono)
      (fun n => (hFn n).tendsto_atBot) (fun n => (hFn n).tendsto_atTop) hFcont
      hFcdf.tendsto_atBot hFcdf.tendsto_atTop hconv
  rw [Metric.tendstoUniformly_iff] at hunif
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hunif (ε / 2) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  have hn' := hN n hn
  have hle : supCDFDist (Fn n) F ≤ ε / 2 := by
    refine ciSup_le (fun t => ?_)
    have := hn' t
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  have hnn : 0 ≤ supCDFDist (Fn n) F := supCDFDist_nonneg (hFn n) hFcdf
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

end SupCDFDist

/-! ## Quantile of a continuous distribution function -/

section QuantileCDF

variable {F : ℝ → ℝ}

/-- Nonemptiness of the sublevel set `{t | p ≤ F t}` for a distribution function and a level
strictly below `1`: the total-mass-`1` tail eventually clears the level. -/
private theorem sublevel_nonempty (hF : IsCDF F) {p : ℝ} (hp : p < 1) :
    {t : ℝ | p ≤ F t}.Nonempty := by
  obtain ⟨y, hy⟩ := (hF.tendsto_atTop.eventually_const_lt hp).exists
  exact ⟨y, hy.le⟩

/-- Bounded-belowness of the sublevel set `{t | p ≤ F t}` for a distribution function and a
level strictly above `0`: the vanishing left tail keeps the set away from `−∞`. -/
private theorem sublevel_bddBelow (hF : IsCDF F) {p : ℝ} (hp : 0 < p) :
    BddBelow {t : ℝ | p ≤ F t} := by
  obtain ⟨b, hb⟩ := eventually_atBot.mp (hF.tendsto_atBot.eventually_lt_const hp)
  refine ⟨b, fun y hy => ?_⟩
  by_contra h
  push_neg at h
  simp only [Set.mem_setOf_eq] at hy
  exact absurd (hb y h.le) (not_lt.mpr hy)

/-- For a continuous distribution function `F` and a level `p ∈ (0,1)`, the generalized inverse
attains the level exactly: `F (cdfPseudoInverse F p) = p`. -/
private theorem cdf_quantile_eq (hF : IsCDF F) (hcont : Continuous F) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) : F (cdfPseudoInverse F p) = p := by
  set q := cdfPseudoInverse F p with hq
  have hne : {t : ℝ | p ≤ F t}.Nonempty := sublevel_nonempty hF hp1
  have hbdd : BddBelow {t : ℝ | p ≤ F t} := sublevel_bddBelow hF hp0
  have hglb : IsGLB {t : ℝ | p ≤ F t} q := Real.isGLB_sInf hne hbdd
  -- `p ≤ F q`, since `q` lies in the (closed) sublevel set.
  have hge : p ≤ F q := by
    have hmem : q ∈ closure {t : ℝ | p ≤ F t} := hglb.mem_closure hne
    have hclosed : IsClosed {t : ℝ | p ≤ F t} :=
      isClosed_le continuous_const hcont
    rw [hclosed.closure_eq] at hmem
    exact hmem
  -- `F q ≤ p`: otherwise continuity yields points below `q` still in the set.
  refine le_antisymm ?_ hge
  by_contra hlt
  push_neg at hlt
  have hopen : IsOpen {y : ℝ | p < F y} := isOpen_lt continuous_const hcont
  have hev : ∀ᶠ y in 𝓝 q, p < F y := hopen.mem_nhds hlt
  have hev' : ∀ᶠ y in 𝓝[<] q, p < F y := hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨y, hyF, hylt⟩ := (hev'.and self_mem_nhdsWithin).exists
  exact absurd (hglb.1 hyF.le) (not_le.mpr hylt)

/-- **Deterministic quantile convergence at a point of strict increase.** If nondecreasing
`Fn` converge pointwise to `F` and `F` is strictly increasing at `q` with `F q = p`, then the
generalized inverses at level `p` converge to `q`. (A `StrictIncAt`-localized twin of the
brick `tendsto_quantile_of_tendsto`, which needs global strict monotonicity.) -/
private theorem tendsto_cdfPseudoInverse_of_tendsto {Fn : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {p q : ℝ}
    (hmono : ∀ n, Monotone (Fn n)) (hstrict : StrictIncAt F q) (hq : F q = p)
    (hconv : ∀ x : ℝ, Tendsto (fun n => Fn n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => cdfPseudoInverse (Fn n) p) atTop (𝓝 q) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e := ε / 2 with he
  have hepos : 0 < e := by positivity
  have he1 : F (q - e) < p := by rw [← hq]; exact hstrict.1 _ (by linarith)
  have he2 : p < F (q + e) := by rw [← hq]; exact hstrict.2 _ (by linarith)
  have hlowev : ∀ᶠ n in atTop, Fn n (q - e) < p := (hconv (q - e)).eventually_lt_const he1
  have hupev : ∀ᶠ n in atTop, p < Fn n (q + e) := (hconv (q + e)).eventually_const_lt he2
  rw [Filter.eventually_atTop] at hlowev hupev
  obtain ⟨N₁, hN₁⟩ := hlowev
  obtain ⟨N₂, hN₂⟩ := hupev
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hlow : Fn n (q - e) < p := hN₁ n (le_of_max_le_left hn)
  have hup : p < Fn n (q + e) := hN₂ n (le_of_max_le_right hn)
  have hlb : q - e ∈ lowerBounds {x : ℝ | p ≤ Fn n x} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    by_contra h
    push_neg at h
    exact absurd ((hmono n) h.le) (not_le.mpr (lt_of_lt_of_le hlow hx))
  have hmemup : (q + e) ∈ {x : ℝ | p ≤ Fn n x} := hup.le
  have h1 : q - e ≤ cdfPseudoInverse (Fn n) p := le_csInf ⟨q + e, hmemup⟩ hlb
  have h2 : cdfPseudoInverse (Fn n) p ≤ q + e := csInf_le ⟨q - e, hlb⟩ hmemup
  rw [Real.dist_eq]
  have hb : |cdfPseudoInverse (Fn n) p - q| ≤ e := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

end QuantileCDF

/-! ## Consistency of the bootstrap sampling distribution -/

section Consistency

variable {Pr : Measure Ω} {P : Measure 𝓧} {J : ℕ → Measure 𝓧 → ℝ → ℝ}
  {C_P : Set (ℕ → Measure 𝓧)} {Jlim : ℝ → ℝ} {Phat : ℕ → Ω → Measure 𝓧} {R : ℕ → Ω → ℝ} {α : ℝ}

/-- **Bootstrap consistency, uniform (sup-distance) form.**

If the sampling distribution functions converge, along every sequence of the class `C_P`, to a
common continuous limit `Jlim`, if the constant sequence at the true law `P` belongs to `C_P`,
and if the estimated sequence `n ↦ Phat n ω` belongs to `C_P` for almost every `ω`, then the
bootstrap sampling distribution is uniformly close to the true one, almost surely:
`sup_x |J n P x − J n (Phat n ω) x| → 0`. -/
theorem tendsto_supCDFDist_bootstrap
    -- USER-INPUT: the constant sequence at the data-generating law belongs to the class; this
    -- is what ties the class to the law actually generating the sample
    (hP_mem : (fun _ => P) ∈ C_P)
    -- USER-INPUT: along every sequence of the class the sampling distribution functions
    -- converge pointwise to the common limit
    (hJconv : ∀ Q ∈ C_P, ∀ x : ℝ, Tendsto (fun n => J n (Q n) x) atTop (𝓝 (Jlim x)))
    -- USER-INPUT: the common limit law is continuous; this is the exact continuity requirement
    -- that turns pointwise convergence into uniform convergence
    (hJlim_cont : Continuous Jlim)
    -- USER-INPUT: the common limit is a distribution function
    (hJlim_cdf : IsCDF Jlim)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hJcdf : ∀ (n : ℕ) (Q : Measure 𝓧), IsCDF (J n Q))
    -- USER-INPUT: the estimated sequence of laws belongs to the class almost surely; the only
    -- stochastic ingredient of the criterion
    (hPhat_mem : ∀ᵐ ω ∂Pr, (fun n => Phat n ω) ∈ C_P) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n => supCDFDist (J n P) (J n (Phat n ω))) atTop (𝓝 0) := by
  filter_upwards [hPhat_mem] with ω hω
  -- Both `J n P` and `J n (Phat n ω)` converge pointwise to the continuous limit `Jlim`.
  have hPconv : ∀ x, Tendsto (fun n => J n P x) atTop (𝓝 (Jlim x)) := hJconv _ hP_mem
  have hHconv : ∀ x, Tendsto (fun n => J n (Phat n ω) x) atTop (𝓝 (Jlim x)) := hJconv _ hω
  have hA : Tendsto (fun n => supCDFDist (J n P) Jlim) atTop (𝓝 0) :=
    tendsto_supCDFDist_zero (fun n => hJcdf n P) hJlim_cont hJlim_cdf hPconv
  have hB : Tendsto (fun n => supCDFDist Jlim (J n (Phat n ω))) atTop (𝓝 0) := by
    have h := tendsto_supCDFDist_zero (fun n => hJcdf n (Phat n ω)) hJlim_cont hJlim_cdf hHconv
    simpa only [supCDFDist_comm] using h
  -- Squeeze between `0` and `supCDFDist (J n P) Jlim + supCDFDist Jlim (J n Phat)`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
    (h := fun n => supCDFDist (J n P) Jlim + supCDFDist Jlim (J n (Phat n ω)))
    tendsto_const_nhds (by simpa using hA.add hB) (fun n => ?_) (fun n => ?_)
  · exact supCDFDist_nonneg (hJcdf n P) (hJcdf n (Phat n ω))
  · exact supCDFDist_triangle (hJcdf n P) hJlim_cdf (hJcdf n (Phat n ω))

/-- **Bootstrap quantile consistency.**

Under the hypotheses of `tendsto_supCDFDist_bootstrap`, if the limit law is in addition
strictly increasing at its `1 − α` quantile, then the estimated `1 − α` quantile converges
almost surely to the quantile of the limit law. -/
theorem tendsto_bootstrapQuantile
    -- USER-INPUT: the constant sequence at the data-generating law belongs to the class
    (hP_mem : (fun _ => P) ∈ C_P)
    -- USER-INPUT: convergence of the sampling distribution functions along the class
    (hJconv : ∀ Q ∈ C_P, ∀ x : ℝ, Tendsto (fun n => J n (Q n) x) atTop (𝓝 (Jlim x)))
    -- USER-INPUT: continuity of the common limit law
    (hJlim_cont : Continuous Jlim)
    -- USER-INPUT: the common limit is a distribution function
    (hJlim_cdf : IsCDF Jlim)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hJcdf : ∀ (n : ℕ) (Q : Measure 𝓧), IsCDF (J n Q))
    -- USER-INPUT: almost sure membership of the estimated sequence in the class
    (hPhat_mem : ∀ᵐ ω ∂Pr, (fun n => Phat n ω) ∈ C_P)
    -- USER-INPUT: nominal level strictly between `0` and `1`
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    -- USER-INPUT: the limit law is strictly increasing at the quantile being estimated; without
    -- it the quantile is not uniquely determined and need not converge
    (hstrict : StrictIncAt Jlim (cdfPseudoInverse Jlim (1 - α))) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n => cdfPseudoInverse (J n (Phat n ω)) (1 - α)) atTop
      (𝓝 (cdfPseudoInverse Jlim (1 - α))) := by
  set q := cdfPseudoInverse Jlim (1 - α) with hqdef
  have hq : Jlim q = 1 - α :=
    cdf_quantile_eq hJlim_cdf hJlim_cont (by linarith [hα.2]) (by linarith [hα.1])
  filter_upwards [hPhat_mem] with ω hω
  have hHconv : ∀ x, Tendsto (fun n => J n (Phat n ω) x) atTop (𝓝 (Jlim x)) := hJconv _ hω
  exact tendsto_cdfPseudoInverse_of_tendsto (fun n => (hJcdf n (Phat n ω)).mono) hstrict hq hHconv

/-- **Asymptotic coverage of the bootstrap confidence set.**

The bootstrap confidence set for the parameter of interest consists of those parameter values
whose root does not exceed the estimated `1 − α` quantile; the true parameter is covered
exactly when `R n ω ≤ cdfPseudoInverse (J n (Phat n ω)) (1 − α)`, where `R n` is the root
evaluated at the true parameter. Its coverage probability converges to the nominal level. -/
theorem tendsto_bootstrapCoverage [IsProbabilityMeasure Pr]
    -- USER-INPUT: the constant sequence at the data-generating law belongs to the class
    (hP_mem : (fun _ => P) ∈ C_P)
    -- USER-INPUT: convergence of the sampling distribution functions along the class
    (hJconv : ∀ Q ∈ C_P, ∀ x : ℝ, Tendsto (fun n => J n (Q n) x) atTop (𝓝 (Jlim x)))
    -- USER-INPUT: continuity of the common limit law
    (hJlim_cont : Continuous Jlim)
    -- USER-INPUT: the common limit is a distribution function
    (hJlim_cdf : IsCDF Jlim)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hJcdf : ∀ (n : ℕ) (Q : Measure 𝓧), IsCDF (J n Q))
    -- USER-INPUT: almost sure membership of the estimated sequence in the class
    (hPhat_mem : ∀ᵐ ω ∂Pr, (fun n => Phat n ω) ∈ C_P)
    -- USER-INPUT: nominal level strictly between `0` and `1`
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    -- USER-INPUT: strict increase of the limit law at the estimated quantile
    (hstrict : StrictIncAt Jlim (cdfPseudoInverse Jlim (1 - α)))
    -- USER-INPUT: at the data-generating law the field `J` is the exact sampling distribution
    -- function of the root; this is what makes `J` the object being bootstrapped
    (hJP : ∀ (n : ℕ) (x : ℝ), J n P x = (Pr {ω | R n ω ≤ x}).toReal)
    -- LEAN-ONLY: the root is measurable; needed for the coverage event to carry its measure
    (hRmeas : ∀ n, Measurable (R n))
    -- LEAN-ONLY: the estimated critical value is measurable in the sample; no measurability in
    -- the measure argument of `J` is assumed, so this is recorded directly
    (hqmeas : ∀ n, Measurable fun ω => cdfPseudoInverse (J n (Phat n ω)) (1 - α)) :
    Tendsto (fun n => (Pr {ω | R n ω ≤ cdfPseudoInverse (J n (Phat n ω)) (1 - α)}).toReal)
      atTop (𝓝 (1 - α)) := by
  set q := cdfPseudoInverse Jlim (1 - α) with hqdef
  have hq : Jlim q = 1 - α :=
    cdf_quantile_eq hJlim_cdf hJlim_cont (by linarith [hα.2]) (by linarith [hα.1])
  set qn : ℕ → Ω → ℝ := fun n ω => cdfPseudoInverse (J n (Phat n ω)) (1 - α) with hqndef
  -- The bootstrap critical values converge in probability to the limit quantile `q`.
  have hquant : ∀ᵐ ω ∂Pr, Tendsto (fun n => qn n ω) atTop (𝓝 q) :=
    tendsto_bootstrapQuantile hP_mem hJconv hJlim_cont hJlim_cdf hJcdf hPhat_mem hα hstrict
  have hInMeas : TendstoInMeasure Pr qn atTop (fun _ => q) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hqmeas n).aestronglyMeasurable) hquant
  show Tendsto (fun n => (Pr {ω | R n ω ≤ qn n ω}).toReal) atTop (𝓝 (1 - α))
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Continuity of `Jlim` at `q` fixes a window `δ` on which `Jlim` stays within `ε/4` of `1−α`.
  have hcont : ContinuousAt Jlim q := hJlim_cont.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ', hδ'pos, hδ'⟩ := hcont (ε / 4) (by positivity)
  set δ := δ' / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have hupabs : |Jlim (q + δ) - (1 - α)| < ε / 4 := by
    have hd : dist (q + δ) q < δ' := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hδpos]; linarith
    have := hδ' hd; rwa [Real.dist_eq, hq] at this
  have hloabs : |Jlim (q - δ) - (1 - α)| < ε / 4 := by
    have hd : dist (q - δ) q < δ' := by
      rw [Real.dist_eq]
      have hne : q - δ - q = -δ := by ring
      rw [hne, abs_neg, abs_of_pos hδpos]; linarith
    have := hδ' hd; rwa [Real.dist_eq, hq] at this
  rw [abs_lt] at hupabs hloabs
  -- `Dp ⊆ S` and `Dm ⊆ S`, where `S` is the "quantile off by `δ`" event whose measure vanishes.
  have hSconv : Tendsto (fun n => (Pr {ω | ENNReal.ofReal δ ≤ edist (qn n ω) q}).toReal)
      atTop (𝓝 0) := by
    have h := hInMeas (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδpos)
    simpa using (ENNReal.tendsto_toReal (by simp)).comp h
  have hDplus : ∀ n, {ω | q + δ < qn n ω} ⊆ {ω | ENNReal.ofReal δ ≤ edist (qn n ω) q} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [edist_dist, Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < qn n ω - q)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hDminus : ∀ n, {ω | qn n ω < q - δ} ⊆ {ω | ENNReal.ofReal δ ≤ edist (qn n ω) q} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [edist_dist, Real.dist_eq, abs_of_neg (by linarith : qn n ω - q < 0)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Coupling inclusions.
  have hUp : ∀ n, {ω | R n ω ≤ qn n ω} ⊆
      {ω | R n ω ≤ q + δ} ∪ {ω | q + δ < qn n ω} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases le_or_gt (qn n ω) (q + δ) with h | h
    · exact Or.inl (le_trans hω h)
    · exact Or.inr h
  have hLo : ∀ n, {ω | R n ω ≤ q - δ} ⊆
      {ω | R n ω ≤ qn n ω} ∪ {ω | qn n ω < q - δ} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases lt_or_ge (qn n ω) (q - δ) with h | h
    · exact Or.inr h
    · exact Or.inl (le_trans hω h)
  -- Assemble on the eventual event.
  have e1 : ∀ᶠ n in atTop, J n P (q + δ) < 1 - α + ε / 2 :=
    (hJconv (fun _ => P) hP_mem (q + δ)).eventually_lt_const (by linarith [hupabs.2])
  have e2 : ∀ᶠ n in atTop, 1 - α - ε / 2 < J n P (q - δ) :=
    (hJconv (fun _ => P) hP_mem (q - δ)).eventually_const_lt (by linarith [hloabs.1])
  have e3 : ∀ᶠ n in atTop, (Pr {ω | ENNReal.ofReal δ ≤ edist (qn n ω) q}).toReal < ε / 2 :=
    hSconv.eventually_lt_const (by positivity)
  rw [Filter.eventually_atTop] at e1 e2 e3
  obtain ⟨N₁, hN₁⟩ := e1
  obtain ⟨N₂, hN₂⟩ := e2
  obtain ⟨N₃, hN₃⟩ := e3
  refine ⟨max (max N₁ N₂) N₃, fun n hn => ?_⟩
  have hn1 := hN₁ n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn)
  have hn2 := hN₂ n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
  have hn3 := hN₃ n (le_trans (le_max_right _ _) hn)
  -- Real forms of the two measure inequalities.
  have hSfin : (Pr {ω | ENNReal.ofReal δ ≤ edist (qn n ω) q}) ≠ ⊤ := measure_ne_top _ _
  have hdp : (Pr {ω | q + δ < qn n ω}).toReal ≤
      (Pr {ω | ENNReal.ofReal δ ≤ edist (qn n ω) q}).toReal :=
    ENNReal.toReal_mono hSfin (measure_mono (hDplus n))
  have hdm : (Pr {ω | qn n ω < q - δ}).toReal ≤
      (Pr {ω | ENNReal.ofReal δ ≤ edist (qn n ω) q}).toReal :=
    ENNReal.toReal_mono hSfin (measure_mono (hDminus n))
  have hcn_up : (Pr {ω | R n ω ≤ qn n ω}).toReal ≤
      J n P (q + δ) + (Pr {ω | q + δ < qn n ω}).toReal := by
    have hle : Pr {ω | R n ω ≤ qn n ω} ≤
        Pr {ω | R n ω ≤ q + δ} + Pr {ω | q + δ < qn n ω} :=
      le_trans (measure_mono (hUp n)) (measure_union_le _ _)
    have := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hle
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← hJP n (q + δ)] at this
    exact this
  have hcn_lo : J n P (q - δ) ≤
      (Pr {ω | R n ω ≤ qn n ω}).toReal + (Pr {ω | qn n ω < q - δ}).toReal := by
    have hle : Pr {ω | R n ω ≤ q - δ} ≤
        Pr {ω | R n ω ≤ qn n ω} + Pr {ω | qn n ω < q - δ} :=
      le_trans (measure_mono (hLo n)) (measure_union_le _ _)
    have := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hle
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← hJP n (q - δ)] at this
    exact this
  rw [Real.dist_eq, abs_lt]
  constructor <;> [linarith; linarith]

end Consistency

/-! ## A weak law of large numbers for triangular arrays -/

/-- **Weak law of large numbers for a triangular array.**

Let `Y n 0, …, Y n (n−1)` be a triangular array of independent random variables, the entries of
row `n` all having distribution function `G n`. If `G n` converges in distribution to the law
`ν` (with distribution function `Glim`) and the first absolute moments converge to the — finite
— first absolute moment of `ν`, then the row averages converge in probability to the mean of
`ν`. This is the moment-convergence tool behind the nonparametric-mean applications. -/
theorem tendstoInMeasure_rowMean_triangular {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {Y : ℕ → ℕ → Ω → ℝ} {G : ℕ → ℝ → ℝ} {Glim : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    -- LEAN-ONLY: the array entries are measurable; the distribution-function hypotheses below
    -- would otherwise refer to outer measures of non-measurable sets
    (hYmeas : ∀ n i, Measurable (Y n i))
    -- USER-INPUT: the entries within each row are independent
    (hindep : ∀ n : ℕ, iIndepFun (fun i : Fin n => Y n i) Pr)
    -- USER-INPUT: the entries of row `n` all have distribution function `G n`
    (hGrow : ∀ n : ℕ, ∀ i < n, ∀ x : ℝ, G n x = (Pr {ω | Y n i ω ≤ x}).toReal)
    -- USER-INPUT: `Glim` is the distribution function of the limit law `ν`
    (hGlim : ∀ x : ℝ, Glim x = (ν (Set.Iic x)).toReal)
    -- USER-INPUT: the row laws converge in distribution to `ν`, i.e. their distribution
    -- functions converge at every continuity point of the limit
    (hGconv : ∀ x : ℝ, ContinuousAt Glim x → Tendsto (fun n => G n x) atTop (𝓝 (Glim x)))
    -- USER-INPUT: the limit law has a finite first absolute moment
    (hint : Integrable (fun t : ℝ => t) ν)
    -- USER-INPUT: convergence of the first absolute moments to that of the limit law; this is
    -- the uniform-integrability substitute that upgrades weak convergence to a weak law
    (habs : Tendsto (fun n => ∫ ω, |Y n 0 ω| ∂Pr) atTop (𝓝 (∫ t, |t| ∂ν))) :
    TendstoInMeasure Pr (fun (n : ℕ) ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, Y n i ω)) atTop
      (fun _ => ∫ t, t ∂ν) := by
  sorry

end StatLean.HypothesisTesting
