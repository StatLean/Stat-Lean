import StatLean.MultipleTesting.ForMathlib.EmpiricalCDF
import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
import StatLean.AsymptoticStatistics.EmpiricalProcess.DonskerBracketing
import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.CDF

/-!
# Higher Criticism and the detection boundary (Candès, Lecture 3, §3.3.3, Theorem 3)

Tukey's Higher-Criticism statistic and the Ingster–Donoho–Jin **detection boundary** for sparse
Gaussian mixtures (Candès, Lecture 3, §3.3.3). For the sparse mixture
`Xᵢ ∼ (1−εₙ)·N(0,1) + εₙ·N(μₙ,1)` with sparsity `εₙ = n^{−β}` (`1/2 < β < 1`) and signal
`μₙ = √(2r log n)`, the detection boundary is

`ρ*(β) = β − 1/2`           for `1/2 < β < 3/4`,
`ρ*(β) = (1 − √(1−β))²`     for `3/4 ≤ β ≤ 1`.

We formalize the two genuinely formalizable ingredients:

* `rhoStar β` — the detection boundary, a concrete piecewise function, with its basic properties
  (`rhoStar_continuous_at_junction`, `rhoStar_nonneg`, `rhoStar_one`);
* `hcStat p α₀ ω` — the Higher-Criticism statistic `max_{0<α≤α₀} (F̂ₙ(α) − α)/√(α(1−α)/n)`.

## Deferred: the detection theorem (Donoho–Jin 2004) — research target, NOT stated as Lean

**Theorem 3 (Donoho & Jin).** *Above the boundary* (`r > ρ*(β)`), the Higher-Criticism test that
rejects when `HC*ₙ ≥ √((1+δ)·2 log log n)` has total error `P₀(type I) + P₁(type II) → 0` as
`n → ∞`; *below* it (`r ≤ ρ*(β)`) every test has `liminf (P₀ + P₁) ≥ 1` (Ingster).

This is **not** stated as a Lean theorem here, deliberately: a faithful statement is an asymptotic
over a sequence of sparse-mixture models, and encoding it now would require laundering unproven
asymptotics through hypotheses (CLAUDE.md §2 forbids this). What the proof needs, and its status:

* **Donsker invariance** (`√n(F̂ₙ−F) ⇒` Brownian bridge) — **now formalized here**:
  `halfLine_isPDonsker` proves the half-line indicator class
  `F_cdf = {𝟙(−∞,t] : t ∈ ℝ}` is `P`-Donsker for every law `P` on `ℝ`, via the project's
  `isPDonsker_of_finite_bracketing_entropy_integral` and the new half-line bracketing-entropy
  bound `N_[](ε) ≲ 1/ε²` (`halfLineClass_bracketingEntropyIntegral_lt_top`). So the `H₀`
  empirical-process convergence underlying `hcStat` is in the library. Residual debts there are the
  half-line bracketing-entropy lemma (the quantile-grid construction) and the framework's own
  inherited maximal-inequality / positivity inputs — none of them the detection theorem.
* **Empirical-process LIL** (`max_{1/n≤t≤α₀} Wₙ(t)/√(2 log log n) →ᵈ 1`, calibrating the
  `√(2 log log n)` threshold) — **not yet available**; finer than Donsker (an iterated-logarithm /
  extreme-value statement for the normalized process near `0`). This is the threshold-calibration
  gap remaining after `halfLine_isPDonsker`.
* **Sparse-mixture large deviations** (the `H₁` detection above `ρ*(β)`) — **not yet available**.

With the H₀ empirical-process convergence now in the library (`halfLine_isPDonsker`), the *only*
residual gaps for Theorem 3 are (i) the empirical-process LIL threshold calibration and (ii) the
`H₁` sparse-mixture large-deviation analysis. Recorded as the TODO §"Batch 8" research target.
-/

open MeasureTheory
open AsymptoticStatistics.EmpiricalProcess
open ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : ℕ}

/-- The **Ingster–Donoho–Jin detection boundary** `ρ*(β)` for sparse Gaussian mixtures
(Candès, Lecture 3, §3.3.3): `β − 1/2` for `1/2 < β < 3/4`, and `(1 − √(1−β))²` for `3/4 ≤ β ≤ 1`. -/
noncomputable def rhoStar (β : ℝ) : ℝ :=
  if β < 3 / 4 then β - 1 / 2 else (1 - Real.sqrt (1 - β)) ^ 2

/-- The two pieces of `rhoStar` agree at the junction `β = 3/4`
(`3/4 − 1/2 = 1/4 = (1 − √(1/4))²`): the boundary is continuous there. -/
theorem rhoStar_continuous_at_junction :
    (3 / 4 : ℝ) - 1 / 2 = (1 - Real.sqrt (1 - 3 / 4)) ^ 2 := by
  have h : Real.sqrt (1 - 3 / 4) = 1 / 2 := by
    rw [show (1 - 3 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]; norm_num

/-- The detection boundary is nonnegative on the sparse range `1/2 < β ≤ 1`. -/
theorem rhoStar_nonneg {β : ℝ} (hβ0 : 1 / 2 < β) (hβ1 : β ≤ 1) : 0 ≤ rhoStar β := by
  unfold rhoStar
  split_ifs
  · linarith
  · exact sq_nonneg _

/-- At the densest sparse endpoint `β = 1`, `ρ*(1) = 1` (the Bonferroni detection threshold). -/
theorem rhoStar_one : rhoStar 1 = 1 := by
  unfold rhoStar
  rw [if_neg (by norm_num), show (1 - 1 : ℝ) = 0 by norm_num, Real.sqrt_zero]
  norm_num

/-- The **Higher-Criticism statistic** `HC*ₙ = max_{0<α≤α₀} (F̂ₙ(α) − α)/√(α(1−α)/n)` (Candès,
Lecture 3, §3.3.3; `F̂ₙ` is the empirical CDF `empiricalCDF p`). -/
noncomputable def hcStat (p : Fin n → Ω → ℝ) (α₀ : ℝ) (ω : Ω) : ℝ :=
  ⨆ α ∈ Set.Ioc (0 : ℝ) α₀,
    (empiricalCDF p α ω - α) / Real.sqrt (α * (1 - α) / (n : ℝ))

/-! ## The H₀ empirical-process half: the half-line indicator class is `P`-Donsker

This is the genuinely formalizable empirical-process content behind `hcStat`. The
Higher-Criticism statistic is a functional of the empirical CDF process
`Gₙ(t) = √n(F̂ₙ(t) − F(t))`, indexed by the half-line indicator class
`F_cdf = { 𝟙_{(−∞,t]} : t ∈ ℝ }`. The classical fact that this process converges
to a Gaussian limit (the `F`-time-changed Brownian bridge) is exactly the
statement that `F_cdf` is `P`-Donsker, which we obtain from the project's
bracketing-entropy Donsker theorem
(`isPDonsker_of_finite_bracketing_entropy_integral`, vdV §19.2 Thm 19.5).

The new, half-line-specific reachable content is the **bracketing-entropy bound**
`N_[](ε, F_cdf, L²(P)) ≲ 1/ε²`, hence `J_[](1, F_cdf, L²(P)) < ∞`
(`halfLineClass_bracketingEntropyIntegral_lt_top`), together with measurability of
the class (`halfLineClass_measurable`, 0-sorry). The assembly into `IsPDonsker`
additionally consumes the framework theorem's own (pre-existing, NOT half-line-
specific) inputs — the vdV Lemma 19.34 maximal/chaining inequality and the
bracketing-integral positivity regularity — which are inherited here as named
debts (`halfLineClass_chain_bound`, `halfLineClass_J_pos`), since the chaining
brick is `private` in `Maximal.lean` and cannot be threaded across files. -/

/-- The **half-line indicator class** `F_cdf = { 𝟙_{(−∞,t]} : t ∈ ℝ }` on `ℝ`
(Candès, Lecture 3; vdV §19.2 Example) — the index class of the empirical-CDF
process. Each member is the indicator `Set.indicator (Set.Iic t) 1` of a left-
infinite half-line; the class is the union over the threshold `t ∈ ℝ`. -/
def halfLineClass : Set (ℝ → ℝ) :=
  {f | ∃ t : ℝ, f = Set.indicator (Set.Iic t) (fun _ => (1 : ℝ))}

/-- Every member of `halfLineClass` is measurable: `𝟙_{(−∞,t]}` is the indicator
of the measurable set `Set.Iic t` of a measurable (constant) function. -/
theorem halfLineClass_measurable {f : ℝ → ℝ} (hf : f ∈ halfLineClass) : Measurable f := by
  obtain ⟨t, rfl⟩ := hf
  exact measurable_const.indicator measurableSet_Iic

/-! ### Helper lemmas for the half-line bracketing analysis -/

/-- The integrand of `bracketingEntropyIntegral` for the half-line class at scale
`ε`: `√(log N_[](ε))`, with the `⊤` convention when `N_[](ε) = ⊤`. -/
private noncomputable def bracketIntegrand (P : Measure ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ENat.recTopCoe (⊤ : ℝ≥0∞)
    (fun n : ℕ => ENNReal.ofReal (Real.sqrt (Real.log (n : ℝ))))
    (bracketingNumber ε halfLineClass 2 P)

private lemma bracketingEntropyIntegral_eq (P : Measure ℝ) (δ : ℝ) :
    bracketingEntropyIntegral δ halfLineClass P
      = ∫⁻ ε in Set.Ioc (0 : ℝ) δ, bracketIntegrand P ε ∂volume := rfl


/-- The difference of two half-line indicators is the indicator of the in-between
half-open interval: `𝟙_{(−∞,t]} − 𝟙_{(−∞,s]} = 𝟙_{(s,t]}` for `s ≤ t`. -/
private lemma indicator_Iic_sub (s t : ℝ) (h : s ≤ t) :
    (Set.indicator (Set.Iic t) (fun _ => (1 : ℝ)))
        - (Set.indicator (Set.Iic s) (fun _ => (1 : ℝ)))
      = Set.indicator (Set.Ioc s t) (fun _ => (1 : ℝ)) := by
  funext x
  simp only [Pi.sub_apply, Set.indicator_apply, Set.mem_Iic, Set.mem_Ioc]
  by_cases hxt : x ≤ t
  · by_cases hxs : x ≤ s
    · simp [hxt, hxs, not_lt.2 hxs]
    · simp [hxt, hxs, not_le.1 hxs]
  · have hns : ¬ x ≤ s := fun hxs => hxt (hxs.trans h)
    simp [hxt, hns]

/-- The `L²(P)`-size of the half-line bracket `[𝟙_{(−∞,s]}, 𝟙_{(−∞,t]}]` is the
square root of the `P`-mass of the in-between interval: `√(P((s,t]))`. -/
private lemma eLpNorm_indicator_Iic_diff (P : Measure ℝ) {s t : ℝ} (hst : s ≤ t) :
    eLpNorm (fun x => Set.indicator (Set.Iic s) (fun _ => (1 : ℝ)) x
                    - Set.indicator (Set.Iic t) (fun _ => (1 : ℝ)) x) 2 P
      = (P (Set.Ioc s t)) ^ (1 / 2 : ℝ) := by
  have hfun : (fun x => Set.indicator (Set.Iic s) (fun _ => (1 : ℝ)) x
                      - Set.indicator (Set.Iic t) (fun _ => (1 : ℝ)) x)
            = -(Set.indicator (Set.Ioc s t) (fun _ => (1 : ℝ))) := by
    funext x
    have := congrFun (indicator_Iic_sub s t hst) x
    simp only [Pi.sub_apply, Pi.neg_apply] at this ⊢
    linarith [this]
  rw [hfun, eLpNorm_neg,
      eLpNorm_indicator_const measurableSet_Ioc (by norm_num) (by norm_num)]
  simp

/-- There exist `s < t` with `P((s,t]) > 0`: a probability measure on `ℝ` cannot be
null on every bounded half-open interval (they exhaust `ℝ`). -/
private lemma exists_Ioc_pos (P : Measure ℝ) [IsProbabilityMeasure P] :
    ∃ s t : ℝ, s < t ∧ 0 < P (Set.Ioc s t) := by
  have huniv : (⋃ n : ℕ, Set.Ioc (-(n : ℝ) - 1) ((n : ℝ) + 1)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    refine ⟨n, ?_, ?_⟩
    · have : -x ≤ (n : ℝ) := (neg_le_abs x).trans hn
      linarith
    · exact (le_abs_self x).trans (hn.trans (by linarith))
  have hne : P (⋃ n : ℕ, Set.Ioc (-(n : ℝ) - 1) ((n : ℝ) + 1)) ≠ 0 := by
    rw [huniv, measure_univ]; exact one_ne_zero
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hne
  exact ⟨_, _, by linarith [Nat.cast_nonneg (α := ℝ) n], hn⟩

/-- **Lower bound on the bracketing number.** If `P((s,t]) > 0` and
`ε ≤ √(P((s,t]))` (so the indicators `𝟙_{(−∞,s]}` and `𝟙_{(−∞,t]}` are
`ε`-separated in `L²(P)`), then no single `ε`-bracket can cover both, forcing
`N_[](ε, F_cdf, L²(P)) ≥ 2`. -/
private lemma two_le_bracketingNumber_of_Ioc_pos
    (P : Measure ℝ) {ε : ℝ} {s t : ℝ} (hst : s < t)
    (hsep : ENNReal.ofReal ε ≤ (P (Set.Ioc s t)) ^ (1 / 2 : ℝ)) :
    2 ≤ bracketingNumber ε halfLineClass 2 P := by
  rw [bracketingNumber]
  refine le_iInf fun k => le_iInf fun hk => ?_
  obtain ⟨l, u, hbr, hcov⟩ := hk
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · exfalso
    obtain ⟨i, hi⟩ := hcov _ ⟨s, rfl⟩
    obtain ⟨j, hj⟩ := hcov _ ⟨t, rfl⟩
    have hij : i = j := by
      have h1 := i.isLt; have h2 := j.isLt; exact Fin.ext (by omega)
    subst hij
    have hbnd : ∀ x, ‖Set.indicator (Set.Iic s) (fun _ => (1 : ℝ)) x
                      - Set.indicator (Set.Iic t) (fun _ => (1 : ℝ)) x‖ₑ
                 ≤ ‖u i x - l i x‖ₑ := by
      intro x
      obtain ⟨hls, hsu⟩ := hi x
      obtain ⟨hlt, htu⟩ := hj x
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u i x - l i x)]
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hmono := eLpNorm_mono_enorm (p := 2) (μ := P) hbnd
    rw [eLpNorm_indicator_Iic_diff P hst.le] at hmono
    have hsize := (hbr i).size_lt
    exact absurd (lt_of_le_of_lt (hsep.trans hmono) hsize) (lt_irrefl _)
  · exact_mod_cast hk2

/-- **Bracketing-integral positivity for the empirical-CDF class** (inherited
framework regularity input of `isPDonsker_of_finite_bracketing_entropy_integral`,
vdV §19.2). For the half-line class this is genuinely *true* (not vacuous): pick
`s < t` with `P((s,t]) > 0`; then for `ε ≤ √(P((s,t]))` no single `ε`-bracket can
cover both `𝟙_{(−∞,s]}` and `𝟙_{(−∞,t]}`, so `N_[](ε) ≥ 2`, whence the integrand
`√(log N_[](ε)) ≥ √(log 2) > 0` on a sub-interval of positive Lebesgue measure and
the integral is positive. -/
private theorem halfLineClass_J_pos (P : Measure ℝ) [IsProbabilityMeasure P] :
    ∀ δ' : ℝ, 0 < δ' → 0 < bracketingEntropyIntegral δ' halfLineClass P := by
  intro δ' hδ'
  obtain ⟨s, t, hst, hpos⟩ := exists_Ioc_pos P
  set c : ℝ≥0∞ := P (Set.Ioc s t) with hc
  have hc_top : c ≠ ⊤ := measure_ne_top P _
  set cr : ℝ := c.toReal with hcr
  have hcr_pos : 0 < cr := ENNReal.toReal_pos hpos.ne' hc_top
  set ε₀ : ℝ := min δ' (Real.sqrt cr) with hε₀
  have hε₀_pos : 0 < ε₀ := lt_min hδ' (Real.sqrt_pos.2 hcr_pos)
  have hε₀_le : ε₀ ≤ δ' := min_le_left _ _
  have hkey : ∀ ε : ℝ, ε ≤ ε₀ → ENNReal.ofReal ε ≤ c ^ (1 / 2 : ℝ) := by
    intro ε hε
    have h2 : ENNReal.ofReal (Real.sqrt cr) = c ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hcr_pos.le (by norm_num),
          hcr, ENNReal.ofReal_toReal hc_top]
    rw [← h2]; exact ENNReal.ofReal_le_ofReal (hε.trans (min_le_right _ _))
  have hlb : ∀ ε ∈ Set.Ioc (0 : ℝ) ε₀,
      ENNReal.ofReal (Real.sqrt (Real.log 2)) ≤ bracketIntegrand P ε := by
    intro ε hε
    have h2 := two_le_bracketingNumber_of_Ioc_pos P hst (hkey ε hε.2)
    unfold bracketIntegrand
    generalize hm : bracketingNumber ε halfLineClass 2 P = m at h2 ⊢
    induction m using ENat.recTopCoe with
    | top => simp
    | coe n =>
      simp only [ENat.recTopCoe_coe]
      have hn2 : (2 : ℕ) ≤ n := by exact_mod_cast h2
      exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt
        (Real.log_le_log (by norm_num) (by exact_mod_cast hn2)))
  have hpos2 : (0 : ℝ) < Real.sqrt (Real.log 2) :=
    Real.sqrt_pos.2 (Real.log_pos (by norm_num))
  rw [bracketingEntropyIntegral_eq]
  calc (0 : ℝ≥0∞)
      < ENNReal.ofReal (Real.sqrt (Real.log 2)) * volume (Set.Ioc (0 : ℝ) ε₀) := by
        apply ENNReal.mul_pos
        · exact (ENNReal.ofReal_pos.2 hpos2).ne'
        · rw [Real.volume_Ioc]
          simp only [sub_zero]
          exact (ENNReal.ofReal_pos.2 hε₀_pos).ne'
    _ = ∫⁻ _ε in Set.Ioc (0 : ℝ) ε₀, ENNReal.ofReal (Real.sqrt (Real.log 2)) ∂volume :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) ε₀, bracketIntegrand P ε ∂volume := by
        apply lintegral_mono_ae
        exact (ae_restrict_mem measurableSet_Ioc).mono fun ε hε => hlb ε hε
    _ ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) δ', bracketIntegrand P ε ∂volume :=
        lintegral_mono' (Measure.restrict_mono (Set.Ioc_subset_Ioc_right hε₀_le) le_rfl)
          (fun _ => le_rfl)

/-- **Maximal/chaining inequality for the empirical-CDF class** — the vdV
Lemma 19.34 sup-norm bound, the framework input `hChainBound_outer` of
`isPDonsker_of_finite_bracketing_entropy_integral`. This is **not** half-line-
specific: it is the general empirical-process maximal inequality, whose proof brick
`chain_supnorm_integral_bound_at_delta_q` is `private` in
`AsymptoticStatistics.EmpiricalProcess.Maximal` and so cannot be threaded across
modules. Inherited here verbatim as a named debt for the half-line class. -/
private theorem halfLineClass_chain_bound (P : Measure ℝ) [IsProbabilityMeasure P] :
    ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
      (X : ℕ → Ξ → ℝ),
      ∀ (Φ : ℝ → ℝ), Measurable Φ → IsEnvelope halfLineClass Φ → MemLp Φ 2 P →
        ∀ {δq : ℝ}, 0 < δq → ∀ (n : ℕ),
          ∫⁻ ξ, supNormOver halfLineClass
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
            ≤ ENNReal.ofReal 2 * bracketingEntropyIntegral δq halfLineClass P
              + ENNReal.ofReal 2 *
                (ENNReal.ofReal (Real.sqrt n)
                  * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                      * Set.indicator {x | δq * Real.sqrt n < |Φ x|} 1 ω ∂P) := by
  sorry

/-! ### Crux 1: finite bracketing-entropy integral via a CDF-quantile grid

We build, for each scale `ε ∈ (0,1]`, a finite `ε`-bracketing cover of the half-line
class of size `≤ ⌈1/ε²⌉ + 1`, by partitioning `ℝ` into `P`-mass-`≤ ε²` pieces at the
quantiles `hlQ P (j/N)` of the CDF `F = cdf P` (`N = ⌈1/ε²⌉ + 1`). The atom-robust
brackets are `[𝟙_{(−∞, q_{j}]}, 𝟙_{(−∞, q_{j+1})}]` (upper open), whose `L²(P)`-size
is `√(P((q_j, q_{j+1}))) = √(leftLim F q_{j+1} − F q_j) ≤ √(1/N) < ε`. -/

/-- The `v`-quantile of `P`: the least `x` with `cdf P x ≥ v`. -/
private noncomputable def hlQ (P : Measure ℝ) (v : ℝ) : ℝ :=
  sInf {x : ℝ | v ≤ (cdf P) x}

private lemma hlQ_nonempty (P : Measure ℝ) (v : ℝ) (hv1 : v < 1) :
    {x : ℝ | v ≤ (cdf P) x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop P).eventually_const_lt hv1).exists
  exact ⟨x, hx.le⟩

private lemma hlQ_bddBelow (P : Measure ℝ) (v : ℝ) (hv0 : 0 < v) :
    BddBelow {x : ℝ | v ≤ (cdf P) x} := by
  have h := (tendsto_cdf_atBot P).eventually_lt_const hv0
  rw [Filter.eventually_atBot] at h
  obtain ⟨b, hb⟩ := h
  refine ⟨b, fun x hx => ?_⟩
  by_contra hxb
  exact absurd (hb x (not_le.1 hxb).le) (not_lt.2 hx)

private lemma hlQ_mono (P : Measure ℝ) {v w : ℝ} (hv0 : 0 < v) (hw1 : w < 1)
    (hvw : v ≤ w) : hlQ P v ≤ hlQ P w := by
  apply csInf_le_csInf (hlQ_bddBelow P v hv0) (hlQ_nonempty P w hw1)
  exact fun x hx => le_trans hvw hx

private lemma cdf_hlQ_ge (P : Measure ℝ) {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    v ≤ (cdf P) (hlQ P v) := by
  have hgt : ∀ y, hlQ P v < y → v ≤ (cdf P) y := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := exists_lt_of_csInf_lt (hlQ_nonempty P v hv1) hy
    exact le_trans hx ((monotone_cdf P) hxy.le)
  have htend : Filter.Tendsto (cdf P)
      (nhdsWithin (hlQ P v) (Set.Ioi (hlQ P v))) (nhds ((cdf P) (hlQ P v))) :=
    ((cdf P).right_continuous (hlQ P v)).tendsto.mono_left
      (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with y hy using hgt y hy

private lemma leftLim_cdf_hlQ_le (P : Measure ℝ) {v : ℝ} (hv0 : 0 < v) :
    Function.leftLim (cdf P) (hlQ P v) ≤ v := by
  have hlt : ∀ y, y < hlQ P v → (cdf P) y < v := by
    intro y hy
    by_contra h
    push_neg at h
    exact absurd (csInf_le (hlQ_bddBelow P v hv0) h) (not_le.2 hy)
  refine le_of_tendsto ((monotone_cdf P).tendsto_leftLim (hlQ P v)) ?_
  filter_upwards [self_mem_nhdsWithin] with y hy using (hlt y hy).le

/-- Quantile/CDF duality: `hlQ P v ≤ τ ↔ v ≤ cdf P τ` (for `0 < v < 1`). -/
private lemma hlQ_le_iff (P : Measure ℝ) {v τ : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    hlQ P v ≤ τ ↔ v ≤ (cdf P) τ := by
  constructor
  · intro h; exact le_trans (cdf_hlQ_ge P hv0 hv1) ((monotone_cdf P) h)
  · intro h; exact csInf_le (hlQ_bddBelow P v hv0) h

/-- `L²(P)`-norm of a `{0,1}`-indicator is the square root of the set's `P`-mass. -/
private lemma eLpNorm_indicator_one (P : Measure ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    eLpNorm (Set.indicator A (fun _ => (1 : ℝ))) 2 P = (P A) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_indicator_const hA (by norm_num) (by norm_num)]; simp

private lemma measure_Iio_cdf (P : Measure ℝ) [IsProbabilityMeasure P] (b : ℝ) :
    P (Set.Iio b) = ENNReal.ofReal (Function.leftLim (cdf P) b) := by
  have h := StieltjesFunction.measure_Iio (cdf P) (tendsto_cdf_atBot P) b
  rw [measure_cdf] at h
  rw [h, sub_zero]

private lemma measure_Ioo_cdf (P : Measure ℝ) [IsProbabilityMeasure P] (a b : ℝ) :
    P (Set.Ioo a b) = ENNReal.ofReal (Function.leftLim (cdf P) b - (cdf P) a) := by
  have h := StieltjesFunction.measure_Ioo (cdf P) (a := a) (b := b)
  rw [measure_cdf] at h
  rw [h]

private lemma measure_Ioi_cdf (P : Measure ℝ) [IsProbabilityMeasure P] (a : ℝ) :
    P (Set.Ioi a) = ENNReal.ofReal (1 - (cdf P) a) := by
  have h := StieltjesFunction.measure_Ioi (cdf P) (tendsto_cdf_atTop P) a
  rw [measure_cdf] at h
  rw [h]

/-- If `P A ≤ 1/N` and `1/N < ε²`, the indicator of `A` is a strict `ε`-small bracket size. -/
private lemma eLpNorm_indicator_lt (P : Measure ℝ) {A : Set ℝ} (hA : MeasurableSet A)
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : (1 : ℝ) / N < ε ^ 2)
    (hmass : P A ≤ ENNReal.ofReal (1 / N)) :
    eLpNorm (Set.indicator A (fun _ => (1 : ℝ))) 2 P < ENNReal.ofReal ε := by
  rw [eLpNorm_indicator_one P hA]
  have hNnn : (0 : ℝ) ≤ 1 / N := by positivity
  calc (P A) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (1 / N)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hmass (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (1 / N)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hNnn (by norm_num), ← Real.sqrt_eq_rpow]
    _ < ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_lt_ofReal_iff hε]
        exact (Real.sqrt_lt' hε).2 hN

/-- The difference `1 − 𝟙_{(−∞,a]} = 𝟙_{(a,∞)}` (upper end-block size). -/
private lemma one_sub_indicator_Iic (a : ℝ) :
    (fun x => (1 : ℝ) - Set.indicator (Set.Iic a) (fun _ => (1 : ℝ)) x)
      = Set.indicator (Set.Ioi a) (fun _ => (1 : ℝ)) := by
  funext x
  simp only [Set.indicator_apply, Set.mem_Iic, Set.mem_Ioi]
  by_cases hx : x ≤ a
  · simp [hx, not_lt.2 hx]
  · simp [hx, not_le.1 hx]

/-- The difference `𝟙_{(−∞,a]∪(−∞,b)} − 𝟙_{(−∞,a]} = 𝟙_{(a,b)}` (middle-block size, `a ≤ b`). -/
private lemma indicator_union_sub_Iic (a b : ℝ) :
    (fun x => Set.indicator (Set.Iic a ∪ Set.Iio b) (fun _ => (1 : ℝ)) x
            - Set.indicator (Set.Iic a) (fun _ => (1 : ℝ)) x)
      = Set.indicator (Set.Ioo a b) (fun _ => (1 : ℝ)) := by
  funext x
  simp only [Set.indicator_apply, Set.mem_union, Set.mem_Iic, Set.mem_Iio, Set.mem_Ioo]
  by_cases hxa : x ≤ a
  · simp [hxa]
  · by_cases hxb : x < b
    · simp [hxa, hxb, not_le.1 hxa]
    · simp [hxa, hxb]

/-- **Half-line bracketing-number bound** (vdV §19.2 Example 19.6):
`N_[](ε, F_cdf, L²(P)) ≤ ⌈1/ε²⌉ + 1` for `0 < ε ≤ 1`. The cover uses the CDF
quantiles `q_j = hlQ P (j/N)` (`N = ⌈1/ε²⌉ + 1`), with atom-robust brackets
`[𝟙_{(−∞,q_j]}, 𝟙_{(−∞,q_j]∪(−∞,q_{j+1})}]` of `L²(P)`-size `√(P((q_j,q_{j+1}))) < ε`. -/
private lemma halfLineClass_bracketingNumber_le (P : Measure ℝ) [IsProbabilityMeasure P]
    {ε : ℝ} (hε0 : 0 < ε) :
    bracketingNumber ε halfLineClass 2 P ≤ ((Nat.ceil (1 / ε ^ 2) + 1 : ℕ) : ℕ∞) := by
  set N : ℕ := Nat.ceil (1 / ε ^ 2) + 1 with hN
  have hεsq : (0 : ℝ) < ε ^ 2 := by positivity
  have hceil : 1 ≤ Nat.ceil (1 / ε ^ 2) := Nat.one_le_ceil_iff.2 (by positivity)
  have hN2 : 2 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNε : (1 : ℝ) / N < ε ^ 2 := by
    have h1 : (1 : ℝ) / ε ^ 2 ≤ Nat.ceil (1 / ε ^ 2) := Nat.le_ceil _
    have h2 : (1 : ℝ) / ε ^ 2 < N := by rw [hN]; push_cast; linarith
    rw [div_lt_iff₀ hNR]
    rw [div_lt_iff₀ hεsq] at h2
    nlinarith [h2]
  set q : ℕ → ℝ := fun j => hlQ P ((j : ℝ) / (N : ℝ)) with hq
  set loN : ℕ → ℝ → ℝ := fun m =>
    if m = 0 then (fun _ => 0) else Set.indicator (Set.Iic (q m)) (fun _ => 1) with hloN
  set upN : ℕ → ℝ → ℝ := fun m =>
    if m + 1 = N then (fun _ => 1)
    else if m = 0 then Set.indicator (Set.Iio (q 1)) (fun _ => 1)
    else Set.indicator (Set.Iic (q m) ∪ Set.Iio (q (m + 1))) (fun _ => 1) with hupN
  rw [bracketingNumber]
  refine iInf_le_of_le N (iInf_le_of_le
    ⟨fun i => loN i.val, fun i => upN i.val, ?_, ?_⟩ le_rfl)
  · -- every block is an ε-bracket
    intro i
    obtain ⟨m, hmN⟩ := i
    simp only [hloN, hupN]
    by_cases hm0 : m = 0
    · -- left end-block: [0, 𝟙_{(−∞, q₁)}]
      subst hm0
      rw [if_pos rfl, if_neg (by omega : ¬ (0 + 1 = N)), if_pos rfl]
      refine ⟨fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x, measurable_const,
        measurable_const.indicator measurableSet_Iio, memLp_const 0,
        MemLp.indicator measurableSet_Iio (memLp_const 1), ?_⟩
      have hsize : (fun x => Set.indicator (Set.Iio (q 1)) (fun _ => (1 : ℝ)) x
                          - (fun _ => (0 : ℝ)) x)
                 = Set.indicator (Set.Iio (q 1)) (fun _ => (1 : ℝ)) := by funext x; simp
      rw [hsize]
      refine eLpNorm_indicator_lt P measurableSet_Iio hε0 hNε ?_
      rw [measure_Iio_cdf]
      refine ENNReal.ofReal_le_ofReal ?_
      have hqeq : q 1 = hlQ P ((1 : ℝ) / N) := by simp [hq]
      rw [hqeq]
      exact leftLim_cdf_hlQ_le P (by positivity)
    · by_cases hmL : m + 1 = N
      · -- right end-block: [𝟙_{(−∞, q_{N-1}]}, 1]
        rw [if_neg hm0, if_pos hmL]
        refine ⟨fun x => by by_cases hx : x ∈ Set.Iic (q m) <;> simp [Set.indicator_apply, hx],
          measurable_const.indicator measurableSet_Iic, measurable_const,
          MemLp.indicator measurableSet_Iic (memLp_const 1), memLp_const 1, ?_⟩
        have hsize : (fun x => (fun _ => (1 : ℝ)) x
                            - Set.indicator (Set.Iic (q m)) (fun _ => (1 : ℝ)) x)
                   = Set.indicator (Set.Ioi (q m)) (fun _ => (1 : ℝ)) := by
          rw [← one_sub_indicator_Iic (q m)]
        rw [hsize]
        refine eLpNorm_indicator_lt P measurableSet_Ioi hε0 hNε ?_
        rw [measure_Ioi_cdf]
        refine ENNReal.ofReal_le_ofReal ?_
        have hqeq : q m = hlQ P ((m : ℝ) / N) := by simp [hq]
        rw [hqeq]
        have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
        have hv0 : (0 : ℝ) < (m : ℝ) / N := div_pos (by exact_mod_cast hm1) hNR
        have hv1 : (m : ℝ) / N < 1 := by rw [div_lt_one hNR]; exact_mod_cast hmN
        have hcdf := cdf_hlQ_ge P hv0 hv1
        have hmeq : (m : ℝ) + 1 = N := by exact_mod_cast hmL
        have hkey : (1 : ℝ) - (m : ℝ) / N = 1 / N := by field_simp; linarith
        rw [← hkey]; linarith [hcdf]
      · -- middle block: [𝟙_{(−∞, q_m]}, 𝟙_{(−∞, q_m]∪(−∞, q_{m+1})}]
        rw [if_neg hm0, if_neg hmL, if_neg hm0]
        refine ⟨fun x => Set.indicator_le_indicator_of_subset Set.subset_union_left
            (fun _ => zero_le_one) x,
          measurable_const.indicator measurableSet_Iic,
          measurable_const.indicator (measurableSet_Iic.union measurableSet_Iio),
          MemLp.indicator measurableSet_Iic (memLp_const 1),
          MemLp.indicator (measurableSet_Iic.union measurableSet_Iio) (memLp_const 1), ?_⟩
        rw [indicator_union_sub_Iic]
        refine eLpNorm_indicator_lt P measurableSet_Ioo hε0 hNε ?_
        rw [measure_Ioo_cdf]
        refine ENNReal.ofReal_le_ofReal ?_
        have hqm : q m = hlQ P ((m : ℝ) / N) := by simp [hq]
        have hqm1 : q (m + 1) = hlQ P (((m : ℝ) + 1) / N) := by simp only [hq]; push_cast; ring_nf
        rw [hqm, hqm1]
        have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
        have hv0m : (0 : ℝ) < (m : ℝ) / N := div_pos (by exact_mod_cast hm1) hNR
        have hv1m : (m : ℝ) / N < 1 := by rw [div_lt_one hNR]; exact_mod_cast hmN
        have hcdfm := cdf_hlQ_ge P hv0m hv1m
        have hleft := leftLim_cdf_hlQ_le P (show (0 : ℝ) < ((m : ℝ) + 1) / N by positivity)
        have hdiff : ((m : ℝ) + 1) / N - (m : ℝ) / N = 1 / N := by field_simp; ring
        calc Function.leftLim (cdf P) (hlQ P (((m : ℝ) + 1) / N)) - cdf P (hlQ P ((m : ℝ) / N))
            ≤ ((m : ℝ) + 1) / N - (m : ℝ) / N := by linarith [hcdfm, hleft]
          _ = 1 / N := hdiff
  · -- the blocks cover the half-line class
    intro f hf
    obtain ⟨τ, rfl⟩ := hf
    set Fτ : ℝ := (cdf P) τ with hFτdef
    have hFτ0 : (0 : ℝ) ≤ Fτ := cdf_nonneg P τ
    set j : ℕ := min (Nat.floor (N * Fτ)) (N - 1) with hjdef
    have hjlt : j < N := by omega
    refine ⟨⟨j, hjlt⟩, fun x => ?_⟩
    simp only [hloN, hupN]
    -- `j ≤ ⌊N·Fτ⌋ ≤ N·Fτ`, giving `q j = hlQ(j/N) ≤ τ` via duality
    have hmle : (j : ℝ) ≤ N * Fτ := by
      have h1 : j ≤ Nat.floor (N * Fτ) := by omega
      calc (j : ℝ) ≤ (Nat.floor (N * Fτ) : ℝ) := by exact_mod_cast h1
        _ ≤ N * Fτ := Nat.floor_le (by positivity)
    by_cases hj0 : j = 0
    · -- left end-block covers `τ < q₁`
      rw [if_pos hj0, if_neg (show ¬ (j + 1 = N) by omega), if_pos hj0]
      have hFτlt : Fτ < 1 / N := by
        have hf0 : Nat.floor (N * Fτ) = 0 := by omega
        have : N * Fτ < 1 := Nat.floor_eq_zero.1 hf0
        rw [lt_div_iff₀ hNR]; nlinarith
      have hq1 : q 1 = hlQ P ((1 : ℝ) / N) := by simp [hq]
      have hτq1 : τ < q 1 := by
        rw [hq1]
        have hduality := hlQ_le_iff P (v := (1 : ℝ) / N) (τ := τ) (by positivity)
          (by rw [div_lt_one hNR]; exact_mod_cast hN2)
        rw [← hFτdef] at hduality
        exact not_le.1 (fun h => absurd (hduality.1 h) (not_le.2 hFτlt))
      refine ⟨Set.indicator_nonneg (fun _ _ => zero_le_one) x,
        Set.indicator_le_indicator_of_subset
          (fun y hy => lt_of_le_of_lt hy hτq1) (fun _ => zero_le_one) x⟩
    · have hv0 : (0 : ℝ) < (j : ℝ) / N := div_pos (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj0) hNR
      have hv1 : (j : ℝ) / N < 1 := by rw [div_lt_one hNR]; exact_mod_cast hjlt
      have hqj : q j = hlQ P ((j : ℝ) / N) := by simp [hq]
      have hτqj : q j ≤ τ := by
        rw [hqj]
        refine (hlQ_le_iff P hv0 hv1).2 ?_
        rw [← hFτdef, div_le_iff₀ hNR]; nlinarith [hmle]
      by_cases hjL : j + 1 = N
      · -- right end-block covers `q_{N-1} ≤ τ`
        rw [if_neg hj0, if_pos hjL]
        refine ⟨Set.indicator_le_indicator_of_subset
            (Set.Iic_subset_Iic.2 hτqj) (fun _ => zero_le_one) x,
          by by_cases hx : x ∈ Set.Iic τ <;> simp [Set.indicator_apply, hx]⟩
      · -- middle block covers `q_j ≤ τ < q_{j+1}`
        rw [if_neg hj0, if_neg hjL, if_neg hj0]
        have hfloorj : Nat.floor (N * Fτ) = j := by omega
        have hFτlt : Fτ < ((j : ℝ) + 1) / N := by
          have : N * Fτ < (j : ℝ) + 1 := by
            have h := Nat.lt_floor_add_one (N * Fτ)
            rw [hfloorj] at h; push_cast at h; linarith
          rw [lt_div_iff₀ hNR]; nlinarith
        have hqj1 : q (j + 1) = hlQ P (((j : ℝ) + 1) / N) := by
          simp only [hq]; push_cast; ring_nf
        have hτqj1 : τ < q (j + 1) := by
          rw [hqj1]
          have hduality := hlQ_le_iff P (v := ((j : ℝ) + 1) / N) (τ := τ) (by positivity)
            (by rw [div_lt_one hNR]; exact_mod_cast (show j + 1 < N by omega))
          rw [← hFτdef] at hduality
          exact not_le.1 (fun h => absurd (hduality.1 h) (not_le.2 hFτlt))
        refine ⟨Set.indicator_le_indicator_of_subset
            (Set.Iic_subset_Iic.2 hτqj) (fun _ => zero_le_one) x,
          Set.indicator_le_indicator_of_subset
            (fun y hy => Set.mem_union_right _ (lt_of_le_of_lt hy hτqj1))
            (fun _ => zero_le_one) x⟩

theorem halfLineClass_bracketingEntropyIntegral_lt_top
    (P : Measure ℝ) [IsProbabilityMeasure P] :
    bracketingEntropyIntegral 1 halfLineClass P < ⊤ := by
  sorry

/-- **The empirical-CDF class is `P`-Donsker** (the H₀ half of the Donoho–Jin
detection program; vdV §19.2 Thm 19.5, Candès Lecture 3 §3.3.3). The class of
half-line indicators `F_cdf = { 𝟙_{(−∞,t]} : t ∈ ℝ }` is `P`-Donsker for *every*
law `P` on `ℝ`: the empirical-CDF process `√n(F̂ₙ − F)` converges weakly to a tight
Gaussian limit in `ℓ^∞(F_cdf)`.

Obtained from the project's bracketing-entropy Donsker theorem
`isPDonsker_of_finite_bracketing_entropy_integral`, fed the half-line measurability
(`halfLineClass_measurable`, 0-sorry) and entropy finiteness
(`halfLineClass_bracketingEntropyIntegral_lt_top`), together with the framework's
own maximal-inequality / positivity inputs (`halfLineClass_chain_bound`,
`halfLineClass_J_pos`). See the section docstring for the debt accounting. -/
theorem halfLine_isPDonsker (P : Measure ℝ) [IsProbabilityMeasure P] :
    IsPDonsker halfLineClass P :=
  isPDonsker_of_finite_bracketing_entropy_integral halfLineClass P
    (fun _ hf => (halfLineClass_measurable hf).aemeasurable)
    (halfLineClass_bracketingEntropyIntegral_lt_top P)
    (halfLineClass_J_pos P)
    (halfLineClass_chain_bound P)

end StatLean.MultipleTesting
