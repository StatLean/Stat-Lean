import StatLean.Minimaxity.LeCam.Functional
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Pointwise estimation of a Lipschitz density and a lower bound for the quadratic functional ∫(f′)²

Two nonparametric minimax lower bounds obtained from Le Cam's two-point/functional method,
each realized by an explicit two-point sub-experiment built from a hat (wavelet) perturbation of
the uniform density.

* **Example 15.7 — pointwise estimation of a Lipschitz density.** Over the class of densities on
  the interval `[-1/2, 1/2]` that are `1`-Lipschitz and bounded below by `1/2`, any estimator of the
  functional value `θ(f) = f(0)` has minimax squared-error risk at least `c · n^{-2/3}` for some
  constant `c > 0` and all `n ≥ 1`. Equivalently, the Hellinger modulus of continuity scales as
  `ω(ε) ≍ ε^{2/3}`, which is the optimal pointwise rate `n^{-β/(2β+1)}` at smoothness `β = 1`.
* **Example 15.8 — quadratic functional `θ(f) = ∫₀¹ (f′)²`.** Over densities on `[0, 1]` bounded
  below by `1/2`, any estimator of the genuine quadratic functional `θ(f) = ∫₀¹ (f′(x))² dx` has
  minimax absolute-error risk at least `c · n^{-1/2}` for some `c > 0` and all `n ≥ 1`. This is the
  *suboptimal two-point* rate: the optimal `n^{-4/9}` rate of Wainwright Example 15.11, which needs a
  full sign-vector/χ² mixture, is out of scope here.

Both public theorems are phrased *existentially*: each exhibits a finite (two-point) family of
densities realizing the stated rate, together with the `n`-fold i.i.d. product model, and concludes a
lower bound on the minimax risk. The witness is the hat (wavelet) perturbation of the uniform density
(Wainwright Eq. (15.19)), `f = 1 + φ` with `φ(x) = tent(x) − tent(x − 2δ)` a mean-zero bump and
`tent(x) = max(δ − |x|, 0)` a triangular spike. For Example 15.7 the width scales as `δ ≍ n^{-1/3}`;
for Example 15.8 a single calibrated, amplified bump of width `δ ≍ n^{-1/4}` and amplitude
`a ≍ n^{-1/8}` is used.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Examples 15.7–15.8,
Eq. (15.19). Both reduce to Le Cam's two-point bound via the functional modulus (Corollary 15.6).

**Proof formalization notes.**

* *Common machinery.* The hat perturbation `φ = tent(·) − tent(· − 2δ)` is shown continuous,
  `1`-Lipschitz, mean-zero on the reference interval, and bounded by `δ` in sup-norm; the two-point
  family `{1, 1 + φ}` (resp. `{1, 1 + a·φ}`) gives genuine probability densities (each integrates to
  one, bounded below by `1/2`). The squared-Hellinger distance between two strictly-positive
  `withDensity` measures is reduced to `H²(ρ·f ‖ ρ·g) = ∫ (√f − √g)² dρ` (lemma
  `sqHellinger_withDensity_eq`, via the Radon–Nikodym derivative of one `withDensity` against
  another), and the integrand is controlled by the contractive bound `(1 − √(1+u))² ≤ u²`.
* *Example 15.7.* Calibrating `δ = (1/6)·n^{-1/3}` gives `H² ≤ 4δ³ = 1/(54n) ≤ (1/(2√n))²`, so the
  pair is admissible at the critical Hellinger radius; the value-gap is `f_true(0) − f_false(0) = δ`,
  and `minimax_functional_modulus` with distortion `Φ(x) = x²` yields the `n^{-2/3}` lower bound with
  provable constant `c = 1/576`.
* *Example 15.8.* A single calibrated bump on `[0,1]` makes `g = 1 + a·φ` piecewise linear with slope
  `a` on the rising edge `(0, δ)`, so `θ(g) = ∫₀¹ (g′)² ≥ a²·δ` (lower-bounded by the mass `a²` over
  `(0, δ)`), while `θ(1) = 0`. With `4a²δ³ = 1/(16n)` the pair is admissible, and
  `minimax_functional_modulus` with the identity distortion `Φ = id` yields the `n^{-1/2}` lower bound
  with provable constant `c = 1/32`.
* *Book-vs-Lean constants.* We state the constants that are actually provable from the two-point
  construction (`c = 1/576` for Ex 15.7, `c = 1/32` for Ex 15.8) rather than asymptotic `≍` constants;
  these are smaller than any sharp constant and only affect the multiplicative factor in the rate.

**Bibliographic comments.**

* The two-point reduction underlying both results is L. Le Cam's method; see L. Le Cam,
  "Convergence of estimates under dimensionality restrictions," *Annals of Statistics* **1** (1973),
  38–53.
* The pointwise rate `n^{-β/(2β+1)}` for density estimation over Hölder/Lipschitz classes (here
  `β = 1`, giving `n^{-1/3}` for the estimate and `n^{-2/3}` for squared error, as in Example 15.7) is
  due to C. J. Stone, "Optimal rates of convergence for nonparametric estimators," *Annals of
  Statistics* **8**(6) (1980), 1348–1360, which establishes these as the optimal nonparametric rates.
* The quadratic functional `∫ (f′)²` of Example 15.8 originates with P. J. Bickel and Y. Ritov,
  "Estimating integrated squared density derivatives: sharp best order of convergence estimates,"
  *Sankhyā: The Indian Journal of Statistics, Series A* **50**(3) (1988), 381–393. That paper
  established the optimal `n^{-4/9}` rate (and the "elbow" phenomenon) for this functional; the
  `n^{-1/2}` bound formalized here is the simpler two-point bound of Wainwright Example 15.8, not the
  sharp Bickel–Ritov rate (Wainwright Example 15.11).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

/-! ## The hat perturbation (Wainwright Eq. (15.19))

`tent δ` is the symmetric triangular bump of height `δ` on `[-δ, δ]`; `hatφ δ = tent δ(·) − tent δ(· − 2δ)`
is the mean-zero wavelet supported on `[-δ, 3δ]`. -/

/-- A symmetric triangular tent of height `δ` supported on `[-δ, δ]`. -/
private noncomputable def tent (δ x : ℝ) : ℝ := max (δ - |x|) 0

/-- The mean-zero hat perturbation `φ = tent(·) − tent(· − 2δ)` (Wainwright Eq. (15.19)),
supported on `[-δ, 3δ]`. -/
private noncomputable def hatφ (δ x : ℝ) : ℝ := tent δ x - tent δ (x - 2 * δ)

private lemma tent_nonneg (δ x : ℝ) : 0 ≤ tent δ x := le_max_right _ _

private lemma tent_le (δ : ℝ) (hδ : 0 ≤ δ) (x : ℝ) : tent δ x ≤ δ :=
  max_le (by have := abs_nonneg x; linarith) hδ

private lemma tent_eq_zero (δ : ℝ) {x : ℝ} (hx : δ ≤ |x|) : tent δ x = 0 :=
  max_eq_right (by linarith)

private lemma tent_continuous (δ : ℝ) : Continuous (tent δ) :=
  (continuous_const.sub continuous_abs).max continuous_const

private lemma tent_lipschitz (δ : ℝ) : LipschitzWith 1 (tent δ) := by
  have h1 : LipschitzWith 1 (fun x : ℝ => δ - |x|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq]
    simp only [NNReal.coe_one, one_mul]
    calc |(δ - |x|) - (δ - |y|)| = abs (|y| - |x|) := by congr 1; ring
      _ ≤ |y - x| := abs_abs_sub_abs_le_abs_sub y x
      _ = |x - y| := abs_sub_comm y x
  exact h1.max_const 0

private lemma tent_dist_le (δ a b : ℝ) : |tent δ a - tent δ b| ≤ |a - b| := by
  have := (tent_lipschitz δ).dist_le_mul a b
  rwa [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at this

private lemma hatφ_continuous (δ : ℝ) : Continuous (hatφ δ) :=
  (tent_continuous δ).sub ((tent_continuous δ).comp (continuous_id.sub continuous_const))

private lemma hatφ_zero (δ : ℝ) (hδ : 0 ≤ δ) : hatφ δ 0 = δ := by
  unfold hatφ tent
  simp only [abs_zero, sub_zero, zero_sub, abs_neg]
  rw [max_eq_left hδ, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * δ)]
  rw [max_eq_right (by linarith : δ - 2 * δ ≤ 0)]
  ring

private lemma hatφ_eq_ite (δ : ℝ) (hδ : 0 ≤ δ) (z : ℝ) :
    hatφ δ z = if z ≤ δ then tent δ z else -tent δ (z - 2 * δ) := by
  unfold hatφ
  rcases le_or_gt z δ with hz | hz
  · rw [if_pos hz,
      show tent δ (z - 2 * δ) = 0 from tent_eq_zero δ
        (by rw [abs_of_nonpos (by linarith : z - 2 * δ ≤ 0)]; linarith), sub_zero]
  · rw [if_neg (not_le.mpr hz),
      show tent δ z = 0 from tent_eq_zero δ
        (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ z)]; linarith), zero_sub]

private lemma hatφ_abs_le (δ : ℝ) (hδ : 0 ≤ δ) (x : ℝ) : |hatφ δ x| ≤ δ := by
  rw [hatφ_eq_ite δ hδ x]
  rcases le_or_gt x δ with hx | hx
  · rw [if_pos hx, abs_of_nonneg (tent_nonneg δ x)]; exact tent_le δ hδ x
  · rw [if_neg (not_le.mpr hx), abs_neg, abs_of_nonneg (tent_nonneg δ _)]; exact tent_le δ hδ _

private lemma hatφ_eq_zero_of_lt (δ : ℝ) (hδ : 0 ≤ δ) {x : ℝ} (hx : x < -δ ∨ 3 * δ < x) :
    hatφ δ x = 0 := by
  rw [hatφ_eq_ite δ hδ x]
  rcases hx with hx | hx
  · rw [if_pos (by linarith), tent_eq_zero δ (by rw [abs_of_neg (by linarith : x < 0)]; linarith)]
  · rw [if_neg (by linarith),
      tent_eq_zero δ (by rw [abs_of_pos (by linarith : (0:ℝ) < x - 2 * δ)]; linarith), neg_zero]

private lemma hatφ_lipschitz (δ : ℝ) (hδ : 0 ≤ δ) : LipschitzWith 1 (hatφ δ) := by
  have hδδ : tent δ δ = 0 := tent_eq_zero δ (by rw [abs_of_nonneg hδ])
  have hnδ : tent δ (-δ) = 0 := tent_eq_zero δ (by rw [abs_of_nonpos (by linarith : -δ ≤ 0)]; linarith)
  have key : ∀ a b : ℝ, hatφ δ a - hatφ δ b ≤ |a - b| := by
    intro a b
    rw [hatφ_eq_ite δ hδ a, hatφ_eq_ite δ hδ b]
    rcases le_or_gt a δ with ha | ha <;> rcases le_or_gt b δ with hb | hb
    · rw [if_pos ha, if_pos hb]
      exact le_trans (le_abs_self _) (tent_dist_le δ a b)
    · rw [if_pos ha, if_neg (not_le.mpr hb)]
      have t1 : tent δ a ≤ δ - a := by
        calc tent δ a = tent δ a - tent δ δ := by rw [hδδ, sub_zero]
          _ ≤ |tent δ a - tent δ δ| := le_abs_self _
          _ ≤ |a - δ| := tent_dist_le δ a δ
          _ = δ - a := by rw [abs_of_nonpos (by linarith)]; ring
      have t2 : tent δ (b - 2 * δ) ≤ b - δ := by
        calc tent δ (b - 2 * δ) = tent δ (b - 2 * δ) - tent δ (-δ) := by rw [hnδ, sub_zero]
          _ ≤ |tent δ (b - 2 * δ) - tent δ (-δ)| := le_abs_self _
          _ ≤ |(b - 2 * δ) - (-δ)| := tent_dist_le δ (b - 2 * δ) (-δ)
          _ = b - δ := by rw [abs_of_nonneg (by linarith)]; ring
      rw [abs_of_nonpos (by linarith : a - b ≤ 0)]; linarith
    · rw [if_neg (not_le.mpr ha), if_pos hb]
      have := tent_nonneg δ (a - 2 * δ); have := tent_nonneg δ b; have := abs_nonneg (a - b)
      linarith
    · rw [if_neg (not_le.mpr ha), if_neg (not_le.mpr hb)]
      calc -tent δ (a - 2 * δ) - -tent δ (b - 2 * δ)
          ≤ |tent δ (b - 2 * δ) - tent δ (a - 2 * δ)| := by
            rw [show -tent δ (a - 2 * δ) - -tent δ (b - 2 * δ)
              = tent δ (b - 2 * δ) - tent δ (a - 2 * δ) by ring]
            exact le_abs_self _
        _ ≤ |(b - 2 * δ) - (a - 2 * δ)| := tent_dist_le δ (b - 2 * δ) (a - 2 * δ)
        _ = |a - b| := by rw [show (b - 2 * δ) - (a - 2 * δ) = -(a - b) by ring, abs_neg]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  refine ⟨?_, key x y⟩
  have := key y x; rw [abs_sub_comm] at this; linarith

/-! ## The two-point density family -/

/-- The two-point density family on `[-1/2,1/2]`: `false ↦ 1` (uniform), `true ↦ 1 + φ`. -/
private noncomputable def lipDensity (δ : ℝ) : Bool → ℝ → ℝ :=
  fun i x => cond i (1 + hatφ δ x) 1

@[simp] private lemma lipDensity_false (δ x : ℝ) : lipDensity δ false x = 1 := rfl

@[simp] private lemma lipDensity_true (δ x : ℝ) : lipDensity δ true x = 1 + hatφ δ x := rfl

private lemma lipDensity_continuous (δ : ℝ) (i : Bool) : Continuous (lipDensity δ i) := by
  cases i
  · exact continuous_const
  · exact continuous_const.add (hatφ_continuous δ)

private lemma lipDensity_measurable (δ : ℝ) (i : Bool) : Measurable (lipDensity δ i) :=
  (lipDensity_continuous δ i).measurable

private lemma lipDensity_ge (δ : ℝ) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) (i : Bool) (x : ℝ) :
    (1 / 2 : ℝ) ≤ lipDensity δ i x := by
  cases i
  · simp only [lipDensity_false]; norm_num
  · simp only [lipDensity_true]
    have h2 : -δ ≤ hatφ δ x := (abs_le.mp (hatφ_abs_le δ hδ x)).1
    linarith

private lemma lipDensity_pos (δ : ℝ) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) (i : Bool) (x : ℝ) :
    0 < lipDensity δ i x :=
  lt_of_lt_of_le (by norm_num) (lipDensity_ge δ hδ hδ2 i x)

private lemma lipDensity_lipschitz (δ : ℝ) (hδ : 0 ≤ δ) (i : Bool) :
    LipschitzWith 1 (lipDensity δ i) := by
  cases i
  · exact LipschitzWith.of_dist_le_mul
      (fun x y => by simp only [lipDensity_false]; rw [dist_self]; positivity)
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [lipDensity_true]
    rw [dist_add_left]
    exact (hatφ_lipschitz δ hδ).dist_le_mul x y

/-! ## The reference interval and mass computations -/

/-- `∫_{Icc} ψ = ∫_ℝ ψ` when `ψ` vanishes outside the interval. -/
private lemma setIntegral_Icc_eq_integral (ψ : ℝ → ℝ)
    (hψ : ∀ x ∉ Set.Icc (-(1:ℝ) / 2) (1 / 2), ψ x = 0) :
    ∫ x in Set.Icc (-(1:ℝ) / 2) (1 / 2), ψ x ∂volume = ∫ x, ψ x ∂volume := by
  rw [← integral_indicator measurableSet_Icc]
  congr 1; funext x
  by_cases hx : x ∈ Set.Icc (-(1:ℝ) / 2) (1 / 2)
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hψ x hx]

private lemma integral_one_Icc : ∫ _ in Set.Icc (-(1:ℝ) / 2) (1 / 2), (1:ℝ) ∂volume = 1 := by
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Icc,
    show (1:ℝ) / 2 - -(1:ℝ) / 2 = 1 by norm_num, ENNReal.ofReal_one, ENNReal.toReal_one]

private lemma hatφ_integral_zero (δ : ℝ) (hδ : 0 ≤ δ) (hδ6 : δ ≤ 1 / 6) :
    ∫ x in Set.Icc (-(1:ℝ) / 2) (1 / 2), hatφ δ x ∂volume = 0 := by
  have hsupp1 : ∀ x ∉ Set.Icc (-(1:ℝ) / 2) (1 / 2), tent δ x = 0 := by
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    apply tent_eq_zero
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hsupp2 : ∀ x ∉ Set.Icc (-(1:ℝ) / 2) (1 / 2), tent δ (x - 2 * δ) = 0 := by
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    apply tent_eq_zero
    rcases hx with h | h
    · rw [abs_of_neg (by linarith : x - 2 * δ < 0)]; linarith
    · rw [abs_of_pos (by linarith : (0:ℝ) < x - 2 * δ)]; linarith
  have hint1 : IntegrableOn (fun x => tent δ x) (Set.Icc (-(1:ℝ) / 2) (1 / 2)) volume :=
    (tent_continuous δ).integrableOn_Icc
  have hint2 : IntegrableOn (fun x => tent δ (x - 2 * δ)) (Set.Icc (-(1:ℝ) / 2) (1 / 2)) volume :=
    ((tent_continuous δ).comp (continuous_id.sub continuous_const)).integrableOn_Icc
  calc ∫ x in Set.Icc (-(1:ℝ) / 2) (1 / 2), hatφ δ x ∂volume
      = ∫ x in Set.Icc (-(1:ℝ) / 2) (1 / 2), (tent δ x - tent δ (x - 2 * δ)) ∂volume := by
        simp only [hatφ]
    _ = (∫ x in Set.Icc (-(1:ℝ) / 2) (1 / 2), tent δ x ∂volume)
          - ∫ x in Set.Icc (-(1:ℝ) / 2) (1 / 2), tent δ (x - 2 * δ) ∂volume :=
        integral_sub hint1 hint2
    _ = (∫ x, tent δ x ∂volume) - ∫ x, tent δ (x - 2 * δ) ∂volume := by
        rw [setIntegral_Icc_eq_integral _ hsupp1, setIntegral_Icc_eq_integral _ hsupp2]
    _ = 0 := by rw [integral_sub_right_eq_self (tent δ) (2 * δ)]; ring

/-- Each density `1 + φ` (and the uniform `1`) integrates to one over `[-1/2,1/2]`, hence its
`withDensity` against the restricted Lebesgue measure is a probability measure. -/
private lemma lipDensity_isProbabilityMeasure (δ : ℝ) (hδ : 0 < δ) (hδ6 : δ ≤ 1 / 6) (i : Bool) :
    IsProbabilityMeasure ((volume.restrict (Set.Icc (-(1:ℝ) / 2) (1 / 2))).withDensity
      fun x => ENNReal.ofReal (lipDensity δ i x)) := by
  have hnn : ∀ x, 0 ≤ lipDensity δ i x :=
    fun x => (lipDensity_pos δ hδ.le (by linarith) i x).le
  have hint : IntegrableOn (lipDensity δ i) (Set.Icc (-(1:ℝ) / 2) (1 / 2)) volume :=
    (lipDensity_continuous δ i).integrableOn_Icc
  have hmass : ∫ x in Set.Icc (-(1:ℝ) / 2) (1 / 2), lipDensity δ i x ∂volume = 1 := by
    cases i
    · simp only [lipDensity_false]; exact integral_one_Icc
    · simp only [lipDensity_true]
      rw [integral_add (continuous_const.integrableOn_Icc) ((hatφ_continuous δ).integrableOn_Icc),
        hatφ_integral_zero δ hδ.le hδ6, add_zero, integral_one_Icc]
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_restrict MeasurableSet.univ,
    Set.univ_inter,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn), hmass,
    ENNReal.ofReal_one]

/-! ## The squared-Hellinger bridge for `withDensity` measures -/

/-- Pointwise simplification underlying the Hellinger bridge: with `a = f x`, `b = g x` both positive,
the common-dominating-measure integrand collapses to `(√a − √b)²`. -/
private lemma bridge_pointwise (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (ENNReal.ofReal a + ENNReal.ofReal b) *
      ENNReal.ofReal ((Real.sqrt (((ENNReal.ofReal a + ENNReal.ofReal b)⁻¹ * ENNReal.ofReal a).toReal)
        - Real.sqrt (((ENNReal.ofReal a + ENNReal.ofReal b)⁻¹ * ENNReal.ofReal b).toReal)) ^ 2)
      = ENNReal.ofReal ((Real.sqrt a - Real.sqrt b) ^ 2) := by
  have hs : (0:ℝ) < a + b := by linarith
  rw [(ENNReal.ofReal_add ha.le hb.le).symm]
  rw [show ((ENNReal.ofReal (a + b))⁻¹ * ENNReal.ofReal a).toReal = a / (a + b) from by
        rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hs.le,
          ENNReal.toReal_ofReal ha.le, div_eq_inv_mul],
      show ((ENNReal.ofReal (a + b))⁻¹ * ENNReal.ofReal b).toReal = b / (a + b) from by
        rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hs.le,
          ENNReal.toReal_ofReal hb.le, div_eq_inv_mul],
      Real.sqrt_div ha.le, Real.sqrt_div hb.le, div_sub_div_same, div_pow,
      Real.sq_sqrt hs.le, ← ENNReal.ofReal_mul hs.le]
  congr 1
  field_simp

/-- **Squared-Hellinger bridge.** For two strictly-positive densities `f, g` against a common
σ-finite reference `ρ`, the squared Hellinger distance equals the `L²`-residual of the square roots,
`H²(ρ·f ‖ ρ·g) = ∫ (√f − √g)² dρ`. Proved from the Radon–Nikodym derivative of a `withDensity`
measure against another (`rnDeriv_withDensity_right_of_absolutelyContinuous`). -/
private lemma sqHellinger_withDensity_eq (ρ : Measure ℝ) [SigmaFinite ρ]
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfpos : ∀ x, 0 < f x) (hgpos : ∀ x, 0 < g x)
    [IsFiniteMeasure (ρ.withDensity fun x => ENNReal.ofReal (f x))]
    [IsFiniteMeasure (ρ.withDensity fun x => ENNReal.ofReal (g x))] :
    sqHellinger (ρ.withDensity fun x => ENNReal.ofReal (f x))
        (ρ.withDensity fun x => ENNReal.ofReal (g x))
      = ∫⁻ x, ENNReal.ofReal ((Real.sqrt (f x) - Real.sqrt (g x)) ^ 2) ∂ρ := by
  set F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f x) with hFdef
  set G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (g x) with hGdef
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp hf
  have hGm : Measurable G := ENNReal.measurable_ofReal.comp hg
  have hFGm : Measurable (F + G) := hFm.add hGm
  have hsum : (ρ.withDensity F) + (ρ.withDensity G) = ρ.withDensity (F + G) :=
    (withDensity_add_left hFm G).symm
  have hne0 : ∀ᵐ x ∂ρ, (F + G) x ≠ 0 := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [Pi.add_apply, hFdef, hGdef]
    exact (add_pos_of_pos_of_nonneg (ENNReal.ofReal_pos.mpr (hfpos x)) (zero_le _)).ne'
  have hnetop : ∀ᵐ x ∂ρ, (F + G) x ≠ ⊤ := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [Pi.add_apply, hFdef, hGdef]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hμrn : (ρ.withDensity F).rnDeriv (ρ.withDensity (F + G)) =ᵐ[ρ]
      fun x => ((F + G) x)⁻¹ * F x := by
    have h1 := Measure.rnDeriv_withDensity_right_of_absolutelyContinuous
      (μ := ρ.withDensity F) (ν := ρ) (f := F + G)
      (withDensity_absolutelyContinuous ρ F) hFGm.aemeasurable hne0 hnetop
    have h2 := Measure.rnDeriv_withDensity ρ (f := F) hFm
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
  have hνrn : (ρ.withDensity G).rnDeriv (ρ.withDensity (F + G)) =ᵐ[ρ]
      fun x => ((F + G) x)⁻¹ * G x := by
    have h1 := Measure.rnDeriv_withDensity_right_of_absolutelyContinuous
      (μ := ρ.withDensity G) (ν := ρ) (f := F + G)
      (withDensity_absolutelyContinuous ρ G) hFGm.aemeasurable hne0 hnetop
    have h2 := Measure.rnDeriv_withDensity ρ (f := G) hGm
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
  have hΨm : Measurable (fun x => ENNReal.ofReal
      ((Real.sqrt ((ρ.withDensity F).rnDeriv (ρ.withDensity (F + G)) x).toReal
        - Real.sqrt ((ρ.withDensity G).rnDeriv (ρ.withDensity (F + G)) x).toReal) ^ 2)) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.pow_const
    exact ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt).sub
          ((Measure.measurable_rnDeriv _ _).ennreal_toReal.sqrt)
  unfold sqHellinger
  rw [hsum, lintegral_withDensity_eq_lintegral_mul ρ hFGm hΨm]
  refine lintegral_congr_ae ?_
  filter_upwards [hμrn, hνrn] with x hx1 hx2
  simp only [Pi.mul_apply]
  rw [hx1, hx2]
  simp only [Pi.add_apply, hFdef, hGdef]
  exact bridge_pointwise (f x) (g x) (hfpos x) (hgpos x)

/-! ## The Hellinger bound for the two-point family -/

/-- Pointwise: `(1 − √(1+u))² ≤ u²` for `u ≥ -1` (the square-root residual is contractive). -/
private lemma sqrt_perturb_sq_le (u : ℝ) (hu : -1 ≤ u) : (1 - Real.sqrt (1 + u)) ^ 2 ≤ u ^ 2 := by
  have h1u : (0:ℝ) ≤ 1 + u := by linarith
  set s := Real.sqrt (1 + u) with hs
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 + u := Real.sq_sqrt h1u
  nlinarith [mul_nonneg (mul_nonneg hsnn (by linarith : (0:ℝ) ≤ s + 2)) (sq_nonneg (s - 1)), hs2,
    sq_nonneg (s - 1)]

/-- The squared Hellinger distance between the uniform density and the bump density is `≤ 4δ³`. -/
private lemma lipDensity_sqHellinger_bound (δ : ℝ) (hδ : 0 < δ) (hδ6 : δ ≤ 1 / 6) :
    sqHellinger
        ((volume.restrict (Set.Icc (-(1:ℝ) / 2) (1 / 2))).withDensity
          fun x => ENNReal.ofReal (lipDensity δ false x))
        ((volume.restrict (Set.Icc (-(1:ℝ) / 2) (1 / 2))).withDensity
          fun x => ENNReal.ofReal (lipDensity δ true x))
      ≤ ENNReal.ofReal (4 * δ ^ 3) := by
  haveI := lipDensity_isProbabilityMeasure δ hδ hδ6 false
  haveI := lipDensity_isProbabilityMeasure δ hδ hδ6 true
  rw [sqHellinger_withDensity_eq _ (lipDensity δ false) (lipDensity δ true)
      (lipDensity_measurable δ false) (lipDensity_measurable δ true)
      (lipDensity_pos δ hδ.le (by linarith) false) (lipDensity_pos δ hδ.le (by linarith) true)]
  -- bound the integrand by `φ²`, then by `δ²·𝟙[-δ,3δ]`
  have hstep1 : ∫⁻ x, ENNReal.ofReal ((Real.sqrt (lipDensity δ false x)
        - Real.sqrt (lipDensity δ true x)) ^ 2) ∂(volume.restrict (Set.Icc (-(1:ℝ) / 2) (1 / 2)))
      ≤ ∫⁻ x, (Set.Icc (-δ) (3 * δ)).indicator (fun _ => ENNReal.ofReal (δ ^ 2)) x
          ∂(volume.restrict (Set.Icc (-(1:ℝ) / 2) (1 / 2))) := by
    apply lintegral_mono
    intro x
    simp only [lipDensity_false, lipDensity_true, Real.sqrt_one]
    by_cases hx : x ∈ Set.Icc (-δ) (3 * δ)
    · rw [Set.indicator_of_mem hx]
      refine ENNReal.ofReal_le_ofReal (le_trans (sqrt_perturb_sq_le (hatφ δ x) ?_) ?_)
      · have := (abs_le.mp (hatφ_abs_le δ hδ.le x)).1; linarith
      · rw [← sq_abs (hatφ δ x)]; exact pow_le_pow_left₀ (abs_nonneg _) (hatφ_abs_le δ hδ.le x) 2
    · rw [Set.indicator_of_notMem hx]
      have hz : hatφ δ x = 0 := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
        exact hatφ_eq_zero_of_lt δ hδ.le hx
      rw [hz]; simp
  calc ∫⁻ x, ENNReal.ofReal ((Real.sqrt (lipDensity δ false x)
          - Real.sqrt (lipDensity δ true x)) ^ 2) ∂(volume.restrict (Set.Icc (-(1:ℝ) / 2) (1 / 2)))
      ≤ ∫⁻ x, (Set.Icc (-δ) (3 * δ)).indicator (fun _ => ENNReal.ofReal (δ ^ 2)) x
          ∂(volume.restrict (Set.Icc (-(1:ℝ) / 2) (1 / 2))) := hstep1
    _ ≤ ∫⁻ x, (Set.Icc (-δ) (3 * δ)).indicator (fun _ => ENNReal.ofReal (δ ^ 2)) x ∂volume :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (δ ^ 2) * volume (Set.Icc (-δ) (3 * δ)) := by
        rw [lintegral_indicator measurableSet_Icc, setLIntegral_const]
    _ = ENNReal.ofReal (4 * δ ^ 3) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-! ## Assembly -/

/-- `4⁻¹·(2⁻¹·ofReal d)² = ofReal(d²/16)`. -/
private lemma enn_quarter_half_sq (d : ℝ) (hd : 0 ≤ d) :
    (4:ℝ≥0∞)⁻¹ * (2⁻¹ * ENNReal.ofReal d) ^ 2 = ENNReal.ofReal (d ^ 2 / 16) := by
  have h2 : (2:ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  have h4 : (4:ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 4) := by
    rw [show (1 / 4 : ℝ) = 4⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [h2, h4, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

/-- The critical-radius admissibility of the two-point pair: with `δ = (1/6)·n^{-1/3}`, the squared
Hellinger distance is `≤ (1/(2√n))²`. -/
private lemma lipDensity_admissible (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) (hδ6 : δ ≤ 1 / 6)
    (hδ3 : δ ^ 3 = 1 / (216 * n)) :
    sqHellinger
        ((volume.restrict (Set.Icc (-(1:ℝ) / 2) (1 / 2))).withDensity
          fun x => ENNReal.ofReal (lipDensity δ false x))
        ((volume.restrict (Set.Icc (-(1:ℝ) / 2) (1 / 2))).withDensity
          fun x => ENNReal.ofReal (lipDensity δ true x))
      ≤ (ENNReal.ofReal (1 / (2 * Real.sqrt n))) ^ 2 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  refine le_trans (lipDensity_sqHellinger_bound δ hδ hδ6) ?_
  rw [← ENNReal.ofReal_pow (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hn0 : (n:ℝ) ≠ 0 := hnpos.ne'
  have hsq : (1 / (2 * Real.sqrt n)) ^ 2 = 1 / (4 * n) := by
    rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hnpos.le]; ring
  have e : 4 * δ ^ 3 = 1 / (54 * n) := by rw [hδ3]; field_simp; ring
  rw [hsq, e]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hnpos])

/-- **Pointwise estimation of a Lipschitz density** (Wainwright Example 15.7): there is a two-point
family of `1`-Lipschitz densities on `[-1/2, 1/2]`, bounded below by `1/2`, whose `n`-fold i.i.d.
product model has minimax squared-error risk for estimating `f(0)` at least `c · n^{-2/3}`.

-- USER-INPUT: witnessing density sub-experiment on [-1/2,1/2] realizing the rate (Wainwright Ex 15.7/15.8); a lower bound on the full-class minimax.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.7. -/
theorem lipschitz_density_pointwise_rate (n : ℕ) (hn : 1 ≤ n) :
    ∃ (ι : Type) (_ : MeasurableSpace ι) (_ : Nonempty ι) (f : ι → ℝ → ℝ)
      (_ : ∀ i, IsProbabilityMeasure
            ((volume.restrict (Set.Icc (-(1:ℝ) / 2) (1 / 2))).withDensity
              fun x => ENNReal.ofReal (f i x)))
      (θfunc : ι → ℝ) (Pn : Kernel ι (Fin n → ℝ)) (_ : IsMarkovKernel Pn),
      (∀ i, θfunc i = f i 0) ∧
      (∀ i, LipschitzWith 1 (f i) ∧ ∀ x, (1 / 2 : ℝ) ≤ f i x) ∧
      (∀ i, Pn i = Measure.pi fun _ : Fin n =>
            (volume.restrict (Set.Icc (-(1:ℝ) / 2) (1 / 2))).withDensity
              fun x => ENNReal.ofReal (f i x)) ∧
      ∃ c : ℝ, 0 < c ∧
        ENNReal.ofReal (c * (n : ℝ) ^ (-(2 : ℝ) / 3)) ≤ minimaxRiskDist (· ^ 2) θfunc Pn := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  set t : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 3) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hnpos _
  have htle1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num)
  set δ : ℝ := t / 6 with hδdef
  have hδpos : 0 < δ := by positivity
  have hδ6 : δ ≤ 1 / 6 := by rw [hδdef]; linarith
  have ht3 : t ^ 3 = 1 / (n : ℝ) := by
    rw [ht, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 : ℝ) / 3)) 3, ← Real.rpow_mul hnpos.le]
    norm_num
    rw [Real.rpow_neg_one]
  have ht2 : t ^ 2 = (n : ℝ) ^ (-(2 : ℝ) / 3) := by
    rw [ht, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 : ℝ) / 3)) 2, ← Real.rpow_mul hnpos.le]
    norm_num
  have hδ3 : δ ^ 3 = 1 / (216 * n) := by
    rw [hδdef, div_pow, ht3]; ring
  -- the family and its model
  set P : Bool → Measure ℝ := fun i =>
    (volume.restrict (Set.Icc (-(1:ℝ) / 2) (1 / 2))).withDensity
      fun x => ENNReal.ofReal (lipDensity δ i x) with hP
  haveI hprob : ∀ i, IsProbabilityMeasure (P i) :=
    fun i => lipDensity_isProbabilityMeasure δ hδpos hδ6 i
  set Pn : Kernel Bool (Fin n → ℝ) :=
    ⟨fun i => Measure.pi fun _ : Fin n => P i, measurable_of_countable _⟩ with hPn
  haveI hmark : IsMarkovKernel Pn := by
    refine ⟨fun a => ?_⟩
    show IsProbabilityMeasure (Measure.pi fun _ : Fin n => P a)
    infer_instance
  refine ⟨Bool, inferInstance, inferInstance, lipDensity δ, hprob,
    fun i => lipDensity δ i 0, Pn, hmark, fun i => rfl, ?_, fun i => rfl, ?_⟩
  · exact fun i => ⟨lipDensity_lipschitz δ hδpos.le i, lipDensity_ge δ hδpos.le (by linarith) i⟩
  · refine ⟨1 / 576, by norm_num, ?_⟩
    -- Le Cam functional bound
    have key := minimax_functional_modulus (fun i => lipDensity δ i 0) P n Pn
      (fun x : ℝ≥0∞ => x ^ 2) (fun a b hab => pow_le_pow_left' hab 2)
      ((ENNReal.continuous_pow 2).lowerSemicontinuous) (fun i => rfl)
    refine le_trans ?_ key
    -- modulus lower bound via the admissible pair (true, false)
    have hadm : sqHellinger (P true) (P false)
        ≤ (ENNReal.ofReal (1 / (2 * Real.sqrt n))) ^ 2 := by
      rw [sqHellinger_comm]
      exact lipDensity_admissible n hn δ hδpos hδ6 hδ3
    have hgap : ENNReal.ofReal |lipDensity δ true 0 - lipDensity δ false 0| = ENNReal.ofReal δ := by
      have : lipDensity δ true 0 - lipDensity δ false 0 = δ := by
        simp only [lipDensity_true, lipDensity_false]
        rw [hatφ_zero δ hδpos.le]; ring
      rw [this, abs_of_pos hδpos]
    have hmod : ENNReal.ofReal δ
        ≤ hellingerModulus (fun i => lipDensity δ i 0) P (ENNReal.ofReal (1 / (2 * Real.sqrt n))) := by
      rw [← hgap]
      exact le_iSup_of_le true (le_iSup_of_le false (le_iSup_of_le hadm le_rfl))
    calc ENNReal.ofReal (1 / 576 * (n : ℝ) ^ (-(2 : ℝ) / 3))
        = ENNReal.ofReal (δ ^ 2 / 16) := by
          congr 1; rw [hδdef, ← ht2]; ring
      _ = 4⁻¹ * (2⁻¹ * ENNReal.ofReal δ) ^ 2 := (enn_quarter_half_sq δ hδpos.le).symm
      _ ≤ 4⁻¹ * (2⁻¹ * hellingerModulus (fun i => lipDensity δ i 0) P
            (ENNReal.ofReal (1 / (2 * Real.sqrt n)))) ^ 2 := by gcongr

/-! ## The quadratic-functional two-point family (Wainwright Example 15.8)

For the quadratic functional `θ(f) = ∫₀¹ (f')²`, a *single* calibrated bump suffices for the two-point
lower bound. On `[0,1]` we use `qbump δ a = a · φ(· − δ)` where `φ = hatφ δ` is the mean-zero hat of
Eq. (15.19) shifted to have support `[0, 4δ]`, with width parameter `δ ≍ n^{-1/4}` and amplitude
`a ≍ n^{-1/8}`. The alternative density is `g = 1 + qbump`, the null is the uniform `1`.

* **Genuine functional gap.** `g` is piecewise linear; on the rising edge `(0, δ)` it equals `1 + a·x`,
  so `(g')² = a²` there, giving `θ(g) = ∫₀¹ (g')² ≥ a²·δ` (while `θ(1) = 0`). With `a²δ = r²/4` and
  `r = n^{-1/4}`, the gap is `≍ n^{-1/2}`.
* **Hellinger admissibility.** `H²(1 ‖ g) ≤ ∫ qbump² ≤ 4a²δ³ = 1/(16n) ≤ (1/(2√n))²`, so the pair is
  admissible at the critical radius and `minimax_functional_modulus` with the identity distortion
  `Φ = id` yields `minimaxRiskDist id θ Pn ≥ ⅛·(gap) ≍ n^{-1/2}`. -/

/-- The (shifted, amplified) single bump `qbump δ a x = a · hatφ δ (x − δ)`, supported on `[0, 4δ]`. -/
private noncomputable def qbump (δ a x : ℝ) : ℝ := a * hatφ δ (x - δ)

/-- The two-point density family on `[0,1]`: `false ↦ 1` (uniform), `true ↦ 1 + qbump`. -/
private noncomputable def qDensity (δ a : ℝ) : Bool → ℝ → ℝ :=
  fun i x => cond i (1 + qbump δ a x) 1

@[simp] private lemma qDensity_false (δ a x : ℝ) : qDensity δ a false x = 1 := rfl

@[simp] private lemma qDensity_true (δ a x : ℝ) : qDensity δ a true x = 1 + qbump δ a x := rfl

private lemma qbump_continuous (δ a : ℝ) : Continuous (qbump δ a) :=
  continuous_const.mul ((hatφ_continuous δ).comp (continuous_id.sub continuous_const))

private lemma qDensity_continuous (δ a : ℝ) (i : Bool) : Continuous (qDensity δ a i) := by
  cases i
  · exact continuous_const
  · exact continuous_const.add (qbump_continuous δ a)

private lemma qDensity_measurable (δ a : ℝ) (i : Bool) : Measurable (qDensity δ a i) :=
  (qDensity_continuous δ a i).measurable

private lemma qbump_abs_le (δ a : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (x : ℝ) : |qbump δ a x| ≤ a * δ := by
  unfold qbump
  rw [abs_mul, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (hatφ_abs_le δ hδ (x - δ)) ha

private lemma qbump_eq_zero_of_notMem (δ a : ℝ) (hδ : 0 ≤ δ) {x : ℝ}
    (hx : x < 0 ∨ 4 * δ < x) : qbump δ a x = 0 := by
  unfold qbump
  have h : hatφ δ (x - δ) = 0 := by
    apply hatφ_eq_zero_of_lt δ hδ
    rcases hx with h | h
    · left; linarith
    · right; linarith
  rw [h, mul_zero]

private lemma qDensity_ge (δ a : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (haδ : a * δ ≤ 1 / 2)
    (i : Bool) (x : ℝ) : (1 / 2 : ℝ) ≤ qDensity δ a i x := by
  cases i
  · simp only [qDensity_false]; norm_num
  · simp only [qDensity_true]
    have h2 : -(a * δ) ≤ qbump δ a x := (abs_le.mp (qbump_abs_le δ a ha hδ x)).1
    linarith

private lemma qDensity_pos (δ a : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (haδ : a * δ ≤ 1 / 2)
    (i : Bool) (x : ℝ) : 0 < qDensity δ a i x :=
  lt_of_lt_of_le (by norm_num) (qDensity_ge δ a ha hδ haδ i x)

/-! ## Mass and probability-measure facts on `[0,1]` -/

/-- `∫_{Icc 0 1} ψ = ∫_ℝ ψ` when `ψ` vanishes outside `[0,1]`. -/
private lemma setIntegral_Icc01_eq_integral (ψ : ℝ → ℝ)
    (hψ : ∀ x ∉ Set.Icc (0:ℝ) 1, ψ x = 0) :
    ∫ x in Set.Icc (0:ℝ) 1, ψ x ∂volume = ∫ x, ψ x ∂volume := by
  rw [← integral_indicator measurableSet_Icc]
  congr 1; funext x
  by_cases hx : x ∈ Set.Icc (0:ℝ) 1
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hψ x hx]

private lemma integral_one_Icc01 : ∫ _ in Set.Icc (0:ℝ) 1, (1:ℝ) ∂volume = 1 := by
  rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, ENNReal.toReal_one]

private lemma qbump_integral_zero (δ a : ℝ) (hδ : 0 < δ) (h4δ : 4 * δ ≤ 1) :
    ∫ x in Set.Icc (0:ℝ) 1, qbump δ a x ∂volume = 0 := by
  have hs1 : ∀ x ∉ Set.Icc (0:ℝ) 1, tent δ (x - δ) = 0 := by
    intro x hx; rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    apply tent_eq_zero
    rcases hx with h | h
    · rw [abs_of_neg (by linarith : x - δ < 0)]; linarith
    · rw [abs_of_pos (by linarith : (0:ℝ) < x - δ)]; linarith
  have hs2 : ∀ x ∉ Set.Icc (0:ℝ) 1, tent δ (x - δ - 2 * δ) = 0 := by
    intro x hx; rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    apply tent_eq_zero
    rcases hx with h | h
    · rw [abs_of_neg (by linarith : x - δ - 2 * δ < 0)]; linarith
    · rw [abs_of_pos (by linarith : (0:ℝ) < x - δ - 2 * δ)]; linarith
  have hint1 : IntegrableOn (fun x => tent δ (x - δ)) (Set.Icc (0:ℝ) 1) volume :=
    ((tent_continuous δ).comp (continuous_id.sub continuous_const)).integrableOn_Icc
  have hint2 : IntegrableOn (fun x => tent δ (x - δ - 2 * δ)) (Set.Icc (0:ℝ) 1) volume :=
    ((tent_continuous δ).comp
      ((continuous_id.sub continuous_const).sub continuous_const)).integrableOn_Icc
  unfold qbump
  rw [integral_const_mul]
  have hzero : ∫ x in Set.Icc (0:ℝ) 1, hatφ δ (x - δ) ∂volume = 0 := by
    calc ∫ x in Set.Icc (0:ℝ) 1, hatφ δ (x - δ) ∂volume
        = ∫ x in Set.Icc (0:ℝ) 1, (tent δ (x - δ) - tent δ (x - δ - 2 * δ)) ∂volume := by
          simp only [hatφ]
      _ = (∫ x in Set.Icc (0:ℝ) 1, tent δ (x - δ) ∂volume)
            - ∫ x in Set.Icc (0:ℝ) 1, tent δ (x - δ - 2 * δ) ∂volume := integral_sub hint1 hint2
      _ = (∫ x, tent δ (x - δ) ∂volume) - ∫ x, tent δ (x - δ - 2 * δ) ∂volume := by
          rw [setIntegral_Icc01_eq_integral _ hs1, setIntegral_Icc01_eq_integral _ hs2]
      _ = 0 := by
          rw [show (fun x => tent δ (x - δ - 2 * δ)) = (fun x => tent δ (x - 3 * δ)) from by
                funext x; congr 1; ring,
            integral_sub_right_eq_self (tent δ) δ, integral_sub_right_eq_self (tent δ) (3 * δ)]
          ring
  rw [hzero, mul_zero]

/-- Each density `1 + qbump` (and the uniform `1`) integrates to one over `[0,1]`, hence its
`withDensity` against the restricted Lebesgue measure is a probability measure. -/
private lemma qDensity_isProbabilityMeasure (δ a : ℝ) (hδ : 0 < δ) (h4δ : 4 * δ ≤ 1) (ha : 0 ≤ a)
    (haδ : a * δ ≤ 1 / 2) (i : Bool) :
    IsProbabilityMeasure ((volume.restrict (Set.Icc (0:ℝ) 1)).withDensity
      fun x => ENNReal.ofReal (qDensity δ a i x)) := by
  have hnn : ∀ x, 0 ≤ qDensity δ a i x :=
    fun x => (qDensity_pos δ a ha hδ.le haδ i x).le
  have hint : IntegrableOn (qDensity δ a i) (Set.Icc (0:ℝ) 1) volume :=
    (qDensity_continuous δ a i).integrableOn_Icc
  have hmass : ∫ x in Set.Icc (0:ℝ) 1, qDensity δ a i x ∂volume = 1 := by
    cases i
    · simp only [qDensity_false]; exact integral_one_Icc01
    · simp only [qDensity_true]
      rw [integral_add (continuous_const.integrableOn_Icc) ((qbump_continuous δ a).integrableOn_Icc),
        qbump_integral_zero δ a hδ h4δ, add_zero, integral_one_Icc01]
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_restrict MeasurableSet.univ,
    Set.univ_inter,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn), hmass,
    ENNReal.ofReal_one]

/-! ## The Hellinger bound for the two-point family -/

/-- The squared Hellinger distance between the uniform density and the bump density is `≤ 4a²δ³`. -/
private lemma qDensity_sqHellinger_bound (δ a : ℝ) (hδ : 0 < δ) (h4δ : 4 * δ ≤ 1)
    (ha : 0 ≤ a) (haδ : a * δ ≤ 1 / 2) :
    sqHellinger
        ((volume.restrict (Set.Icc (0:ℝ) 1)).withDensity
          fun x => ENNReal.ofReal (qDensity δ a false x))
        ((volume.restrict (Set.Icc (0:ℝ) 1)).withDensity
          fun x => ENNReal.ofReal (qDensity δ a true x))
      ≤ ENNReal.ofReal (4 * a ^ 2 * δ ^ 3) := by
  haveI := qDensity_isProbabilityMeasure δ a hδ h4δ ha haδ false
  haveI := qDensity_isProbabilityMeasure δ a hδ h4δ ha haδ true
  rw [sqHellinger_withDensity_eq _ (qDensity δ a false) (qDensity δ a true)
      (qDensity_measurable δ a false) (qDensity_measurable δ a true)
      (qDensity_pos δ a ha hδ.le haδ false) (qDensity_pos δ a ha hδ.le haδ true)]
  have hstep1 : ∫⁻ x, ENNReal.ofReal ((Real.sqrt (qDensity δ a false x)
        - Real.sqrt (qDensity δ a true x)) ^ 2) ∂(volume.restrict (Set.Icc (0:ℝ) 1))
      ≤ ∫⁻ x, (Set.Icc (0:ℝ) (4 * δ)).indicator (fun _ => ENNReal.ofReal (a ^ 2 * δ ^ 2)) x
          ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
    apply lintegral_mono
    intro x
    simp only [qDensity_false, qDensity_true, Real.sqrt_one]
    by_cases hx : x ∈ Set.Icc (0:ℝ) (4 * δ)
    · rw [Set.indicator_of_mem hx]
      refine ENNReal.ofReal_le_ofReal (le_trans (sqrt_perturb_sq_le (qbump δ a x) ?_) ?_)
      · have h := (abs_le.mp (qbump_abs_le δ a ha hδ.le x)).1
        nlinarith [h, haδ]
      · rw [← sq_abs (qbump δ a x)]
        have h := qbump_abs_le δ a ha hδ.le x
        nlinarith [h, abs_nonneg (qbump δ a x), mul_nonneg ha hδ.le]
    · rw [Set.indicator_of_notMem hx]
      have hz : qbump δ a x = 0 := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
        exact qbump_eq_zero_of_notMem δ a hδ.le hx
      rw [hz]; simp
  calc ∫⁻ x, ENNReal.ofReal ((Real.sqrt (qDensity δ a false x)
          - Real.sqrt (qDensity δ a true x)) ^ 2) ∂(volume.restrict (Set.Icc (0:ℝ) 1))
      ≤ ∫⁻ x, (Set.Icc (0:ℝ) (4 * δ)).indicator (fun _ => ENNReal.ofReal (a ^ 2 * δ ^ 2)) x
          ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := hstep1
    _ ≤ ∫⁻ x, (Set.Icc (0:ℝ) (4 * δ)).indicator (fun _ => ENNReal.ofReal (a ^ 2 * δ ^ 2)) x
          ∂volume := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (a ^ 2 * δ ^ 2) * volume (Set.Icc (0:ℝ) (4 * δ)) := by
        rw [lintegral_indicator measurableSet_Icc, setLIntegral_const]
    _ = ENNReal.ofReal (4 * a ^ 2 * δ ^ 3) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- The critical-radius admissibility of the two-point pair: with `4a²δ³ = 1/(16n)`, the squared
Hellinger distance is `≤ (1/(2√n))²`. -/
private lemma qDensity_admissible (n : ℕ) (hn : 1 ≤ n) (δ a : ℝ) (hδ : 0 < δ) (h4δ : 4 * δ ≤ 1)
    (ha : 0 ≤ a) (haδ : a * δ ≤ 1 / 2) (hbound : 4 * a ^ 2 * δ ^ 3 = 1 / (16 * (n : ℝ))) :
    sqHellinger
        ((volume.restrict (Set.Icc (0:ℝ) 1)).withDensity
          fun x => ENNReal.ofReal (qDensity δ a false x))
        ((volume.restrict (Set.Icc (0:ℝ) 1)).withDensity
          fun x => ENNReal.ofReal (qDensity δ a true x))
      ≤ (ENNReal.ofReal (1 / (2 * Real.sqrt n))) ^ 2 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  refine le_trans (qDensity_sqHellinger_bound δ a hδ h4δ ha haδ) ?_
  rw [← ENNReal.ofReal_pow (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hsq : (1 / (2 * Real.sqrt n)) ^ 2 = 1 / (4 * (n : ℝ)) := by
    rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hnpos.le]; ring
  rw [hsq, hbound]
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-! ## The genuine functional gap `∫₀¹ (g')² ≥ a²δ` -/

/-- The amplified, shifted bump is `a`-Lipschitz (`hatφ` is `1`-Lipschitz). -/
private lemma qDensity_true_lipschitz (δ a : ℝ) (hδ : 0 ≤ δ) (ha : 0 ≤ a) :
    LipschitzWith a.toNNReal (qDensity δ a true) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [qDensity_true, qbump]
  rw [Real.dist_eq, Real.dist_eq,
    show (1 + a * hatφ δ (x - δ)) - (1 + a * hatφ δ (y - δ))
        = a * (hatφ δ (x - δ) - hatφ δ (y - δ)) by ring,
    abs_mul, abs_of_nonneg ha, Real.coe_toNNReal a ha]
  apply mul_le_mul_of_nonneg_left _ ha
  have h := (hatφ_lipschitz δ hδ).dist_le_mul (x - δ) (y - δ)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
  calc |hatφ δ (x - δ) - hatφ δ (y - δ)| ≤ |(x - δ) - (y - δ)| := h
    _ = |x - y| := by rw [show (x - δ) - (y - δ) = x - y by ring]

/-- On the negative slope window `(-δ, 0)` the hat is the line `δ + z` (slope `+1`). -/
private lemma hatφ_on_Ioo_neg (δ : ℝ) (hδ : 0 < δ) {z : ℝ} (hz : z ∈ Set.Ioo (-δ) 0) :
    hatφ δ z = δ + z := by
  obtain ⟨h1, h2⟩ := hz
  rw [hatφ_eq_ite δ hδ.le z, if_pos (by linarith : z ≤ δ)]
  unfold tent
  rw [abs_of_neg h2, max_eq_left (by linarith : (0:ℝ) ≤ δ - -z)]
  ring

/-- On the rising edge `(0, δ)`, `g = 1 + qbump` equals the line `1 + a·x`, so `g' = a`. -/
private lemma qDensity_true_deriv_on (δ a : ℝ) (hδ : 0 < δ) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) δ) :
    deriv (qDensity δ a true) x = a := by
  have hev : (qDensity δ a true) =ᶠ[nhds x] (fun y => 1 + a * y) :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds hx.1 hx.2) (fun y hy => by
      change (1 + qbump δ a y) = 1 + a * y
      unfold qbump
      rw [hatφ_on_Ioo_neg δ hδ ⟨by linarith [hy.1], by linarith [hy.2]⟩]
      ring)
  have hd : HasDerivAt (fun y => 1 + a * y) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).const_add 1
  exact (hd.congr_of_eventuallyEq hev).deriv

/-- **The genuine functional value-gap.** `θ(g) = ∫₀¹ (g')² ≥ a²·δ`, the integral being lower-bounded
by its mass `a²` over the rising-edge interval `(0, δ)`. -/
private lemma qDensity_gap_lower (δ a : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a) (h4δ : 4 * δ ≤ 1) :
    a ^ 2 * δ ≤ ∫ x in Set.Icc (0:ℝ) 1, (deriv (qDensity δ a true) x) ^ 2 ∂volume := by
  have hmeas : Measurable (deriv (qDensity δ a true)) := measurable_deriv _
  have hbound : ∀ x, (deriv (qDensity δ a true) x) ^ 2 ≤ a ^ 2 := by
    intro x
    have hb : |deriv (qDensity δ a true) x| ≤ a := by
      have h := norm_deriv_le_of_lipschitz (qDensity_true_lipschitz δ a hδ.le ha) (x₀ := x)
      rwa [Real.norm_eq_abs, Real.coe_toNNReal a ha] at h
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hint : IntegrableOn (fun x => (deriv (qDensity δ a true) x) ^ 2) (Set.Icc (0:ℝ) 1) volume := by
    refine Integrable.mono' (g := fun _ => a ^ 2)
      (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      (hmeas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hbound x
  have hind_int : IntegrableOn
      (fun x => (Set.Ioo (0:ℝ) δ).indicator (fun _ => a ^ 2) x) (Set.Icc (0:ℝ) 1) volume := by
    refine Integrable.mono' (g := fun _ => a ^ 2)
      (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      ((measurable_const.indicator measurableSet_Ioo).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Set.Ioo (0:ℝ) δ
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    · rw [Set.indicator_of_notMem hx, norm_zero]; positivity
  have hpt : ∀ x, (Set.Ioo (0:ℝ) δ).indicator (fun _ => a ^ 2) x
      ≤ (deriv (qDensity δ a true) x) ^ 2 := by
    intro x
    by_cases hx : x ∈ Set.Ioo (0:ℝ) δ
    · simp only [Set.indicator_of_mem hx, qDensity_true_deriv_on δ a hδ hx, le_refl]
    · rw [Set.indicator_of_notMem hx]; positivity
  have hval : ∫ x in Set.Icc (0:ℝ) 1, (Set.Ioo (0:ℝ) δ).indicator (fun _ => a ^ 2) x ∂volume
      = a ^ 2 * δ := by
    rw [setIntegral_indicator measurableSet_Ioo]
    have hinter : Set.Icc (0:ℝ) 1 ∩ Set.Ioo 0 δ = Set.Ioo 0 δ :=
      Set.inter_eq_right.mpr (fun x hx => ⟨hx.1.le, le_trans hx.2.le (by linarith)⟩)
    rw [hinter, setIntegral_const, measureReal_def, Real.volume_Ioo, sub_zero,
      ENNReal.toReal_ofReal hδ.le, smul_eq_mul]
    ring
  calc a ^ 2 * δ
      = ∫ x in Set.Icc (0:ℝ) 1, (Set.Ioo (0:ℝ) δ).indicator (fun _ => a ^ 2) x ∂volume :=
        hval.symm
    _ ≤ ∫ x in Set.Icc (0:ℝ) 1, (deriv (qDensity δ a true) x) ^ 2 ∂volume :=
        setIntegral_mono hind_int hint hpt

/-! ## Assembly -/

/-- `4⁻¹·(2⁻¹·ofReal d) = ofReal(d/8)`. -/
private lemma enn_quarter_half (d : ℝ) (hd : 0 ≤ d) :
    (4:ℝ≥0∞)⁻¹ * (2⁻¹ * ENNReal.ofReal d) = ENNReal.ofReal (d / 8) := by
  have h2 : (2:ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  have h4 : (4:ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 4) := by
    rw [show (1 / 4 : ℝ) = 4⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [h2, h4, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

/-- **Lower bound for a quadratic functional** (Wainwright Example 15.8): there is a two-point family
of densities on `[0, 1]`, bounded below by `1/2`, whose `n`-fold i.i.d. product model has minimax
*absolute-error* risk for the genuine quadratic functional `θ(f) = ∫₀¹ (f')²` at least `c · n^{-1/2}`
(the suboptimal two-point rate; the optimal `n^{-4/9}` convex-hull rate of Wainwright Ex 15.11 is
out of scope — its genuine proof needs a sign-vector/χ² mixture not yet in Mathlib/StatLean).

-- USER-INPUT: absolute-error loss (Φ=id) with the genuine functional θ(f)=∫(f')² and book rate n^{-1/2} (Wainwright Ex 15.8); the suboptimal two-point bound (the optimal n^{-4/9} rate of Ex 15.11 is out of scope).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2, Example 15.8. -/
theorem quadratic_functional_two_point_rate (n : ℕ) (hn : 1 ≤ n) :
    ∃ (ι : Type) (_ : MeasurableSpace ι) (f : ι → ℝ → ℝ) (θfunc : ι → ℝ)
      (Pn : Kernel ι (Fin n → ℝ)) (_ : IsMarkovKernel Pn),
      (∀ i, ∀ x ∈ Set.Icc (0:ℝ) 1, (1 / 2 : ℝ) ≤ f i x) ∧
      (∀ i, θfunc i = ∫ x in Set.Icc (0:ℝ) 1, (deriv (f i) x) ^ 2) ∧
      (∀ i, Pn i = Measure.pi fun _ : Fin n =>
            (volume.restrict (Set.Icc (0:ℝ) 1)).withDensity fun x => ENNReal.ofReal (f i x)) ∧
      ∃ c : ℝ, 0 < c ∧
        ENNReal.ofReal (c * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤ minimaxRiskDist id θfunc Pn := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  set r : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 4) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos hnpos _
  have hrle1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num)
  have hr4 : r ^ 4 = 1 / (n : ℝ) := by
    rw [hr, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 : ℝ) / 4)) 4, ← Real.rpow_mul hnpos.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hr2 : r ^ 2 = (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [hr, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 : ℝ) / 4)) 2, ← Real.rpow_mul hnpos.le]
    norm_num
  set δ : ℝ := r / 4 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have h4δ : 4 * δ ≤ 1 := by rw [hδdef, show 4 * (r / 4) = r by ring]; exact hrle1
  have hδ4 : δ ≤ 1 / 4 := by rw [hδdef]; linarith
  set a : ℝ := Real.sqrt r with hadef
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = r := Real.sq_sqrt hrpos.le
  have ha1 : a ≤ 1 := by
    rw [hadef, show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hrle1
  have haδ : a * δ ≤ 1 / 2 := by
    have := mul_le_mul ha1 hδ4 hδpos.le (zero_le_one)
    linarith
  have hbound : 4 * a ^ 2 * δ ^ 3 = 1 / (16 * (n : ℝ)) := by
    have h : 4 * a ^ 2 * δ ^ 3 = r ^ 4 / 16 := by rw [ha2, hδdef]; ring
    rw [h, hr4]; ring
  -- the family and its model
  set P : Bool → Measure ℝ := fun i =>
    (volume.restrict (Set.Icc (0:ℝ) 1)).withDensity
      fun x => ENNReal.ofReal (qDensity δ a i x) with hP
  haveI hprob : ∀ i, IsProbabilityMeasure (P i) :=
    fun i => qDensity_isProbabilityMeasure δ a hδpos h4δ ha haδ i
  set Pn : Kernel Bool (Fin n → ℝ) :=
    ⟨fun i => Measure.pi fun _ : Fin n => P i, measurable_of_countable _⟩ with hPn
  haveI hmark : IsMarkovKernel Pn := by
    refine ⟨fun a => ?_⟩
    show IsProbabilityMeasure (Measure.pi fun _ : Fin n => P a)
    infer_instance
  set θfunc : Bool → ℝ :=
    fun i => ∫ x in Set.Icc (0:ℝ) 1, (deriv (qDensity δ a i) x) ^ 2 ∂volume with hθdef
  refine ⟨Bool, inferInstance, qDensity δ a, θfunc, Pn, hmark, ?_, fun i => rfl, fun i => rfl, ?_⟩
  · intro i x _; exact qDensity_ge δ a ha hδpos.le haδ i x
  · refine ⟨1 / 32, by norm_num, ?_⟩
    have key := minimax_functional_modulus θfunc P n Pn id monotone_id
      (continuous_id.lowerSemicontinuous) (fun i => rfl)
    simp only [id_eq] at key
    refine le_trans ?_ key
    have hadm : sqHellinger (P true) (P false)
        ≤ (ENNReal.ofReal (1 / (2 * Real.sqrt n))) ^ 2 := by
      rw [sqHellinger_comm]
      exact qDensity_admissible n hn δ a hδpos h4δ ha haδ hbound
    have hgapval : a ^ 2 * δ ≤ θfunc true := qDensity_gap_lower δ a hδpos ha h4δ
    have hθfalse : θfunc false = 0 := by
      have hd0 : ∀ x, deriv (qDensity δ a false) x = 0 := fun x => by
        rw [show qDensity δ a false = (fun _ => (1:ℝ)) from rfl]; exact deriv_const x 1
      change (∫ x in Set.Icc (0:ℝ) 1, (deriv (qDensity δ a false) x) ^ 2 ∂volume) = 0
      simp only [hd0]; simp
    have hθtrue_nonneg : 0 ≤ θfunc true :=
      le_trans (mul_nonneg (sq_nonneg a) hδpos.le) hgapval
    have hmod : ENNReal.ofReal (a ^ 2 * δ)
        ≤ hellingerModulus θfunc P (ENNReal.ofReal (1 / (2 * Real.sqrt n))) := by
      have hle : a ^ 2 * δ ≤ |θfunc true - θfunc false| := by
        rw [hθfalse, sub_zero, abs_of_nonneg hθtrue_nonneg]; exact hgapval
      calc ENNReal.ofReal (a ^ 2 * δ) ≤ ENNReal.ofReal |θfunc true - θfunc false| :=
            ENNReal.ofReal_le_ofReal hle
        _ ≤ hellingerModulus θfunc P (ENNReal.ofReal (1 / (2 * Real.sqrt n))) :=
            le_iSup_of_le true (le_iSup_of_le false (le_iSup_of_le hadm le_rfl))
    have hval : (1 / 32 : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 2) = a ^ 2 * δ / 8 := by
      rw [← hr2, ha2, hδdef]; ring
    calc ENNReal.ofReal (1 / 32 * (n : ℝ) ^ (-(1 : ℝ) / 2))
        = ENNReal.ofReal (a ^ 2 * δ / 8) := by rw [hval]
      _ = 4⁻¹ * (2⁻¹ * ENNReal.ofReal (a ^ 2 * δ)) :=
          (enn_quarter_half (a ^ 2 * δ) (mul_nonneg (sq_nonneg a) hδpos.le)).symm
      _ ≤ 4⁻¹ * (2⁻¹ * hellingerModulus θfunc P (ENNReal.ofReal (1 / (2 * Real.sqrt n)))) := by
          gcongr

end StatLean.Minimaxity
