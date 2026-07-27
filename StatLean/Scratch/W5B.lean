import StatLean.HypothesisTesting.GoodnessOfFit.SmoothTest
import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity

/-! Scratch development file for wave-5 lane B.  Not part of the library. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators NNReal InnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (chiSquared)

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]

/-- local copy of the private `psiVec` of `SmoothTest.lean`. -/
private noncomputable def psiVec' {k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (x : 𝓧) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => ψ j x)

private lemma inner_eucl_sum' {k : ℕ} (u w : EuclideanSpace ℝ (Fin k)) :
    ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

private lemma inner_psiVec' {k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (u : EuclideanSpace ℝ (Fin k))
    (x : 𝓧) : ⟪u, psiVec' ψ x⟫_ℝ = ∑ j, u j * ψ j x := by
  rw [inner_eucl_sum']
  exact Finset.sum_congr rfl fun j _ => rfl

/-! ### Elementary real inequalities -/

/-- `|e^z − (1 + z + z²/2)| ≤ 4 |z|³ e^{|z|}` for every real `z`. -/
private lemma abs_exp_sub_quadratic_le (z : ℝ) :
    |Real.exp z - (1 + z + z ^ 2 / 2)| ≤ 4 * |z| ^ 3 * Real.exp |z| := by
  have hexp1 : (1 : ℝ) ≤ Real.exp |z| := Real.one_le_exp (abs_nonneg z)
  have hcube0 : (0 : ℝ) ≤ |z| ^ 3 := pow_nonneg (abs_nonneg z) 3
  rcases le_or_gt |z| 1 with hle | hgt
  · have h := Real.exp_bound hle (n := 3) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 3, z ^ m / (Nat.factorial m) = 1 + z + z ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    rw [hsum] at h
    have hcoef : ((Nat.succ 3 : ℝ) / ((Nat.factorial 3 : ℝ) * 3)) ≤ 4 := by
      norm_num [Nat.factorial]
    calc |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |z| ^ 3 * ((Nat.succ 3 : ℝ) / ((Nat.factorial 3) * 3)) := h
      _ ≤ |z| ^ 3 * 4 := by nlinarith
      _ ≤ 4 * |z| ^ 3 * Real.exp |z| := by nlinarith
  · -- `|z| > 1`: crude triangle-inequality bound
    have habs0 : (0 : ℝ) ≤ |z| := abs_nonneg z
    have h1 : (1 : ℝ) ≤ |z| ^ 3 := one_le_pow₀ hgt.le
    have hd : 0 ≤ |z| * ((|z| - 1) * (|z| + 1)) :=
      mul_nonneg habs0 (mul_nonneg (by linarith) (by linarith))
    have hz : |z| ≤ |z| ^ 3 := by nlinarith
    have hd2 : 0 ≤ (|z| * |z|) * (|z| - 1) :=
      mul_nonneg (mul_nonneg habs0 habs0) (by linarith)
    have hz2 : z ^ 2 ≤ |z| ^ 3 := by
      have hsq : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
      nlinarith
    have hexpz : Real.exp z ≤ Real.exp |z| := Real.exp_le_exp.mpr (le_abs_self z)
    have htri : |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |Real.exp z| + |1 + z + z ^ 2 / 2| := by
      rw [sub_eq_add_neg]
      refine (abs_add_le _ _).trans_eq ?_
      rw [abs_neg]
    have hterm : |1 + z + z ^ 2 / 2| ≤ 3 * |z| ^ 3 := by
      have hb : |1 + z + z ^ 2 / 2| ≤ 1 + |z| + z ^ 2 / 2 := by
        have h₁ : |1 + z + z ^ 2 / 2| ≤ |1 + z| + |z ^ 2 / 2| := abs_add_le _ _
        have h₂ : |1 + z| ≤ 1 + |z| := by
          calc |1 + z| ≤ |(1 : ℝ)| + |z| := abs_add_le _ _
            _ = 1 + |z| := by norm_num
        have h₃ : |z ^ 2 / 2| = z ^ 2 / 2 := abs_of_nonneg (by positivity)
        linarith
      linarith
    have hexpabs : |Real.exp z| = Real.exp z := abs_of_nonneg (Real.exp_pos z).le
    have hstep : Real.exp |z| ≤ |z| ^ 3 * Real.exp |z| := by nlinarith [Real.exp_pos |z|]
    calc |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |Real.exp z| + |1 + z + z ^ 2 / 2| := htri
      _ ≤ Real.exp |z| + 3 * |z| ^ 3 := by rw [hexpabs]; linarith
      _ ≤ 4 * |z| ^ 3 * Real.exp |z| := by nlinarith

/-- `|log (1 + w) − w| ≤ w²` for `w ≥ 0`. -/
private lemma abs_log_one_add_sub_le (w : ℝ) (hw : 0 ≤ w) :
    |Real.log (1 + w) - w| ≤ w ^ 2 := by
  have hpos : (0 : ℝ) < 1 + w := by linarith
  have hup : Real.log (1 + w) ≤ w := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlow : w - w ^ 2 ≤ Real.log (1 + w) := by
    have h := Real.log_le_sub_one_of_pos (x := (1 + w)⁻¹) (by positivity)
    rw [Real.log_inv] at h
    have hne : (1 : ℝ) + w ≠ 0 := ne_of_gt hpos
    have hkey : 1 - (1 + w)⁻¹ = w / (1 + w) := by field_simp; ring
    have h3 : w - w ^ 2 ≤ 1 - (1 + w)⁻¹ := by
      rw [hkey, le_div_iff₀ hpos]
      nlinarith [pow_nonneg hw 3]
    linarith
  rw [abs_le]
  constructor <;> nlinarith

/-- `u³ ≤ 6 t⁻³ e^{t u}` for `u ≥ 0`, `t > 0`. -/
private lemma cube_le_exp (t : ℝ) (ht : 0 < t) (u : ℝ) (hu : 0 ≤ u) :
    u ^ 3 ≤ 6 / t ^ 3 * Real.exp (t * u) := by
  have h := Real.sum_le_exp_of_nonneg (x := t * u) (by positivity) 4
  have hsum : ∑ m ∈ Finset.range 4, (t * u) ^ m / (Nat.factorial m)
      = 1 + t * u + (t * u) ^ 2 / 2 + (t * u) ^ 3 / 6 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have htu : 0 ≤ t * u := by positivity
  have hcube : (t * u) ^ 3 / 6 ≤ Real.exp (t * u) := by nlinarith [sq_nonneg (t * u)]
  have ht3 : (0 : ℝ) < t ^ 3 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ ht3]
  nlinarith


/-! ### Envelope integrability from the natural parameter set -/

/-- **Sign-vector envelope.** If every exponential tilt `e^{⟪θ, ψ(x)⟫}` is `P₀`-integrable,
then so is `e^{t ∑ⱼ |ψⱼ(x)|}` for every `t ≥ 0`: the `ℓ¹` exponential is dominated by the
sum of the `2^k` sign tilts. -/
private lemma integrable_exp_l1 {k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} (hψmeas : ∀ j, Measurable (ψ j))
    (hint : ∀ θ : EuclideanSpace ℝ (Fin k),
      Integrable (fun x => Real.exp ⟪θ, psiVec' ψ x⟫_ℝ) P₀)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => Real.exp (t * ∑ j, |ψ j x|)) P₀ := by
  classical
  set Θ : Finset (Fin k) → EuclideanSpace ℝ (Fin k) :=
    fun s => WithLp.toLp 2 (fun j => if j ∈ s then t else -t) with hΘ
  have hmeas : Measurable (fun x => Real.exp (t * ∑ j, |ψ j x|)) :=
    Real.continuous_exp.measurable.comp
      ((Finset.univ.measurable_sum fun j _ => (hψmeas j).abs).const_mul t)
  have hbound : ∀ x, Real.exp (t * ∑ j, |ψ j x|)
      ≤ ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, Real.exp ⟪Θ s, psiVec' ψ x⟫_ℝ := by
    intro x
    have hprod : Real.exp (t * ∑ j, |ψ j x|) = ∏ j, Real.exp (t * |ψ j x|) := by
      rw [← Real.exp_sum, Finset.mul_sum]
    have hpt : ∀ j : Fin k,
        Real.exp (t * |ψ j x|) ≤ Real.exp (t * ψ j x) + Real.exp (-(t * ψ j x)) := by
      intro j
      rcases abs_cases (ψ j x) with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]
        nlinarith [Real.exp_pos (-(t * ψ j x)), le_refl (Real.exp (t * ψ j x))]
      · rw [h1, mul_neg, ← neg_mul]
        nlinarith [Real.exp_pos (t * ψ j x)]
    have hle : ∏ j, Real.exp (t * |ψ j x|)
        ≤ ∏ j, (Real.exp (t * ψ j x) + Real.exp (-(t * ψ j x))) :=
      Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le) (fun j _ => hpt j)
    have hexpand : ∏ j, (Real.exp (t * ψ j x) + Real.exp (-(t * ψ j x)))
        = ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, Real.exp ⟪Θ s, psiVec' ψ x⟫_ℝ := by
      rw [Finset.prod_add]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsub : s ⊆ (Finset.univ : Finset (Fin k)) := Finset.subset_univ s
      have hL : (∏ j ∈ s, Real.exp (t * ψ j x))
          * ∏ j ∈ (Finset.univ : Finset (Fin k)) \ s, Real.exp (-(t * ψ j x))
          = Real.exp ((∑ j ∈ s, t * ψ j x)
              + ∑ j ∈ (Finset.univ : Finset (Fin k)) \ s, -(t * ψ j x)) := by
        rw [Real.exp_add, Real.exp_sum, Real.exp_sum]
      rw [hL]
      congr 1
      rw [inner_psiVec']
      rw [← Finset.sum_sdiff hsub]
      have h1 : ∑ j ∈ (Finset.univ : Finset (Fin k)) \ s, (Θ s) j * ψ j x
          = ∑ j ∈ (Finset.univ : Finset (Fin k)) \ s, -(t * ψ j x) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjs : j ∉ s := (Finset.mem_sdiff.mp hj).2
        show (if j ∈ s then t else -t) * ψ j x = -(t * ψ j x)
        rw [if_neg hjs]; ring
      have h2 : ∑ j ∈ s, (Θ s) j * ψ j x = ∑ j ∈ s, t * ψ j x := by
        refine Finset.sum_congr rfl fun j hj => ?_
        show (if j ∈ s then t else -t) * ψ j x = t * ψ j x
        rw [if_pos hj]
      rw [h1, h2, add_comm]
    calc Real.exp (t * ∑ j, |ψ j x|) = ∏ j, Real.exp (t * |ψ j x|) := hprod
      _ ≤ ∏ j, (Real.exp (t * ψ j x) + Real.exp (-(t * ψ j x))) := hle
      _ = _ := hexpand
  have hsumint : Integrable (fun x => ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset,
      Real.exp ⟪Θ s, psiVec' ψ x⟫_ℝ) P₀ :=
    integrable_finset_sum (Finset.univ : Finset (Fin k)).powerset (fun s _ => hint (Θ s))
  refine Integrable.mono' hsumint hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact hbound x


/-! ### The quadratic expansion of the log-partition function -/

/-- `|θ j| ≤ ‖θ‖` in `EuclideanSpace`. -/
private lemma abs_coord_le_norm {k : ℕ} (θ : EuclideanSpace ℝ (Fin k)) (j : Fin k) :
    |θ j| ≤ ‖θ‖ := by
  have hle : (θ j) ^ 2 ≤ ‖θ‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (f := fun i => (θ i) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [sq_abs (θ j), abs_nonneg (θ j), norm_nonneg θ]

/-- Integrability facts for an orthonormal centred score system. -/
private lemma score_L2_facts {k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} (hψmeas : ∀ j, Measurable (ψ j))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0) :
    (∀ i, Integrable (ψ i) P₀) ∧ (∀ i j, Integrable (fun x => ψ i x * ψ j x) P₀) := by
  have hsqint : ∀ i, Integrable (fun x => ψ i x ^ 2) P₀ := by
    intro i
    have h1 : (∫ x, ψ i x * ψ i x ∂P₀) = 1 := by rw [hortho i i]; simp
    simpa [sq] using integrable_of_integral_eq_one h1
  have hψL2 : ∀ i, MemLp (ψ i) 2 P₀ := fun i =>
    (memLp_two_iff_integrable_sq (hψmeas i).aestronglyMeasurable).2 (hsqint i)
  exact ⟨fun i => (hψL2 i).integrable one_le_two,
    fun i j => by simpa using (hψL2 i).integrable_mul (hψL2 j)⟩

/-- **Quadratic expansion of the log-partition function of the smooth model.**  For a centred
orthonormal score system whose exponential tilts are all integrable, the log-partition
function `A(θ) = log ∫ e^{⟪θ,ψ⟫} dP₀` satisfies `|A(θ) − ‖θ‖²/2| ≤ C‖θ‖³` on the ball of
radius `r`.  Purely elementary: a third-order Taylor bound on `e^z`, the moment identities
`∫⟪θ,ψ⟫ = 0` and `∫⟪θ,ψ⟫² = ‖θ‖²`, and `|log(1+w) − w| ≤ w²`. -/
private lemma logPartition_quadratic_bound {k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} (hψmeas : ∀ j, Measurable (ψ j))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    (hint : ∀ θ : EuclideanSpace ℝ (Fin k),
      Integrable (fun x => Real.exp ⟪θ, psiVec' ψ x⟫_ℝ) P₀)
    {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ‖ ≤ r →
      |Real.log (∫ x, Real.exp ⟪θ, psiVec' ψ x⟫_ℝ ∂P₀) - ‖θ‖ ^ 2 / 2| ≤ C * ‖θ‖ ^ 3 := by
  classical
  obtain ⟨hψint, hψψint⟩ := score_L2_facts hψmeas hortho
  set W : 𝓧 → ℝ := fun x => ∑ j, |ψ j x| with hW
  have hWnn : ∀ x, 0 ≤ W x := fun x => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hWmeas : Measurable W := Finset.univ.measurable_sum fun j _ => (hψmeas j).abs
  -- the cubic envelope `G` and its integral `K`
  set G : 𝓧 → ℝ := fun x => (W x) ^ 3 * Real.exp (r * W x) with hG
  have hGnn : ∀ x, 0 ≤ G x := fun x => by positivity
  have hGmeas : Measurable G :=
    (hWmeas.pow_const 3).mul (Real.continuous_exp.measurable.comp (hWmeas.const_mul r))
  have hGint : Integrable G P₀ := by
    have hdom : Integrable (fun x => 6 / r ^ 3 * Real.exp (2 * r * W x)) P₀ := by
      have h2 := integrable_exp_l1 (P₀ := P₀) hψmeas hint (t := 2 * r) (by positivity)
      exact h2.const_mul _
    refine hdom.mono' hGmeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (hGnn x)]
    have hcube := cube_le_exp r hr (W x) (hWnn x)
    have hexp : Real.exp (r * W x) * Real.exp (r * W x) = Real.exp (2 * r * W x) := by
      rw [← Real.exp_add]; ring_nf
    calc (W x) ^ 3 * Real.exp (r * W x)
        ≤ (6 / r ^ 3 * Real.exp (r * W x)) * Real.exp (r * W x) := by
          exact mul_le_mul_of_nonneg_right hcube (Real.exp_pos _).le
      _ = 6 / r ^ 3 * Real.exp (2 * r * W x) := by rw [mul_assoc, hexp]
  set K : ℝ := ∫ x, G x ∂P₀ with hK
  have hKnn : 0 ≤ K := integral_nonneg hGnn
  refine ⟨4 * K + r * (1 / 2 + 4 * K * r) ^ 2, by positivity, ?_⟩
  intro θ hθ
  have hθ0 : 0 ≤ ‖θ‖ := norm_nonneg θ
  set z : 𝓧 → ℝ := fun x => ⟪θ, psiVec' ψ x⟫_ℝ with hz
  have hzval : ∀ x, z x = ∑ j, θ j * ψ j x := fun x => inner_psiVec' ψ θ x
  have hzmeas : Measurable z := by
    have : z = fun x => ∑ j, θ j * ψ j x := funext hzval
    rw [this]
    exact Finset.univ.measurable_sum fun j _ => (hψmeas j).const_mul _
  have hzint : Integrable z P₀ := by
    have : z = fun x => ∑ j, θ j * ψ j x := funext hzval
    rw [this]
    exact integrable_finset_sum _ fun j _ => (hψint j).const_mul _
  have hzsqint : Integrable (fun x => z x ^ 2) P₀ := by
    have hpt : (fun x => z x ^ 2) = fun x => ∑ i, ∑ j, (θ i * θ j) * (ψ i x * ψ j x) := by
      funext x
      rw [hzval x, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hpt]
    exact integrable_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => (hψψint i j).const_mul _
  -- the two moment identities
  have hmom1 : ∫ x, z x ∂P₀ = 0 := by
    have : z = fun x => ∑ j, θ j * ψ j x := funext hzval
    rw [this, integral_finset_sum _ fun j _ => (hψint j).const_mul _]
    simp_rw [integral_const_mul, hcentred, mul_zero, Finset.sum_const_zero]
  have hmom2 : ∫ x, z x ^ 2 ∂P₀ = ‖θ‖ ^ 2 := by
    have hpt : (fun x => z x ^ 2) = fun x => ∑ i, ∑ j, (θ i * θ j) * (ψ i x * ψ j x) := by
      funext x
      rw [hzval x, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hpt, integral_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => (hψψint i j).const_mul _,
      EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => (hψψint i j).const_mul _]
    simp_rw [integral_const_mul, hortho i]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [if_neg (Ne.symm hji), mul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [if_pos rfl, mul_one, sq]
  -- the pointwise third-order bound
  have hzbd : ∀ x, |z x| ≤ ‖θ‖ * W x := by
    intro x
    rw [hzval x]
    calc |∑ j, θ j * ψ j x| ≤ ∑ j, |θ j * ψ j x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ‖θ‖ * |ψ j x| := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_coord_le_norm θ j) (abs_nonneg _)
      _ = ‖θ‖ * W x := by rw [hW, Finset.mul_sum]
  have hptbd : ∀ x, |Real.exp (z x) - (1 + z x + (z x) ^ 2 / 2)| ≤ 4 * ‖θ‖ ^ 3 * G x := by
    intro x
    refine (abs_exp_sub_quadratic_le (z x)).trans ?_
    have h1 : |z x| ^ 3 ≤ ‖θ‖ ^ 3 * (W x) ^ 3 := by
      have := hzbd x
      have hpow : |z x| ^ 3 ≤ (‖θ‖ * W x) ^ 3 :=
        pow_le_pow_left₀ (abs_nonneg _) this 3
      calc |z x| ^ 3 ≤ (‖θ‖ * W x) ^ 3 := hpow
        _ = ‖θ‖ ^ 3 * (W x) ^ 3 := by ring
    have h2 : Real.exp |z x| ≤ Real.exp (r * W x) := by
      refine Real.exp_le_exp.mpr ((hzbd x).trans ?_)
      exact mul_le_mul_of_nonneg_right hθ (hWnn x)
    calc 4 * |z x| ^ 3 * Real.exp |z x|
        ≤ 4 * (‖θ‖ ^ 3 * (W x) ^ 3) * Real.exp (r * W x) := by
          have hc : (0 : ℝ) ≤ 4 * |z x| ^ 3 := by positivity
          have := mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
          nlinarith [Real.exp_pos (r * W x), pow_nonneg (abs_nonneg (z x)) 3]
      _ = 4 * ‖θ‖ ^ 3 * G x := by rw [hG]; ring
  -- the integral of the exponential
  set M : ℝ := ∫ x, Real.exp (z x) ∂P₀ with hM
  have hMint : Integrable (fun x => Real.exp (z x)) P₀ := hint θ
  have hquadint : Integrable (fun x => 1 + z x + (z x) ^ 2 / 2) P₀ :=
    ((integrable_const 1).add hzint).add (hzsqint.div_const 2)
  have hlinint : Integrable (fun x : 𝓧 => (1 : ℝ) + z x) P₀ := (integrable_const 1).add hzint
  have hquadval : ∫ x, (1 + z x + (z x) ^ 2 / 2) ∂P₀ = 1 + ‖θ‖ ^ 2 / 2 := by
    rw [show (∫ x, (1 + z x + (z x) ^ 2 / 2) ∂P₀)
          = (∫ x, ((1 : ℝ) + z x) ∂P₀) + ∫ x, (z x) ^ 2 / 2 ∂P₀ from
        integral_add hlinint (hzsqint.div_const 2),
      show (∫ x, ((1 : ℝ) + z x) ∂P₀) = (∫ _x : 𝓧, (1 : ℝ) ∂P₀) + ∫ x, z x ∂P₀ from
        integral_add (integrable_const 1) hzint,
      integral_div, hmom1, hmom2]
    simp
  have hMbd : |M - (1 + ‖θ‖ ^ 2 / 2)| ≤ 4 * ‖θ‖ ^ 3 * K := by
    have hdiff : M - (1 + ‖θ‖ ^ 2 / 2)
        = ∫ x, (Real.exp (z x) - (1 + z x + (z x) ^ 2 / 2)) ∂P₀ := by
      rw [integral_sub hMint hquadint, hquadval]
    rw [hdiff]
    refine (abs_integral_le_integral_abs).trans ?_
    have hb : ∫ x, |Real.exp (z x) - (1 + z x + (z x) ^ 2 / 2)| ∂P₀
        ≤ ∫ x, 4 * ‖θ‖ ^ 3 * G x ∂P₀ := by
      refine integral_mono ((hMint.sub hquadint).abs) (hGint.const_mul _) ?_
      intro x; exact hptbd x
    rw [integral_const_mul] at hb
    calc _ ≤ 4 * ‖θ‖ ^ 3 * K := hb
      _ = 4 * ‖θ‖ ^ 3 * K := rfl
  -- `M ≥ 1`
  have hM1 : 1 ≤ M := by
    have hmono : ∫ x, ((1 : ℝ) + z x) ∂P₀ ≤ M := by
      refine integral_mono hlinint hMint fun x => ?_
      have := Real.add_one_le_exp (z x)
      linarith
    rw [show (∫ x, ((1 : ℝ) + z x) ∂P₀) = (∫ _x : 𝓧, (1 : ℝ) ∂P₀) + ∫ x, z x ∂P₀ from
      integral_add (integrable_const 1) hzint, hmom1] at hmono
    simpa using hmono
  set w : ℝ := M - 1 with hw
  have hwnn : 0 ≤ w := by simp [hw]; linarith
  have hwbd : |w - ‖θ‖ ^ 2 / 2| ≤ 4 * K * ‖θ‖ ^ 3 := by
    have : w - ‖θ‖ ^ 2 / 2 = M - (1 + ‖θ‖ ^ 2 / 2) := by rw [hw]; ring
    rw [this]
    calc |M - (1 + ‖θ‖ ^ 2 / 2)| ≤ 4 * ‖θ‖ ^ 3 * K := hMbd
      _ = 4 * K * ‖θ‖ ^ 3 := by ring
  have hlog : |Real.log M - ‖θ‖ ^ 2 / 2| ≤ w ^ 2 + 4 * K * ‖θ‖ ^ 3 := by
    have hMw : M = 1 + w := by rw [hw]; ring
    have h1 := abs_log_one_add_sub_le w hwnn
    rw [hMw]
    calc |Real.log (1 + w) - ‖θ‖ ^ 2 / 2|
        ≤ |Real.log (1 + w) - w| + |w - ‖θ‖ ^ 2 / 2| := by
          have hsum : (Real.log (1 + w) - w) + (w - ‖θ‖ ^ 2 / 2)
              = Real.log (1 + w) - ‖θ‖ ^ 2 / 2 := by ring
          rw [← hsum]
          exact abs_add_le _ _
      _ ≤ w ^ 2 + 4 * K * ‖θ‖ ^ 3 := add_le_add h1 hwbd
  have hwle : w ≤ (1 / 2 + 4 * K * r) * ‖θ‖ ^ 2 := by
    have h1 : w ≤ ‖θ‖ ^ 2 / 2 + 4 * K * ‖θ‖ ^ 3 := by
      have := (abs_le.mp hwbd).2; linarith
    have h2 : 4 * K * ‖θ‖ ^ 3 ≤ 4 * K * r * ‖θ‖ ^ 2 := by
      have : ‖θ‖ ^ 3 = ‖θ‖ ^ 2 * ‖θ‖ := by ring
      rw [this]
      have hkk : (0 : ℝ) ≤ 4 * K * ‖θ‖ ^ 2 := by positivity
      nlinarith [sq_nonneg ‖θ‖]
    linarith
  have hwsq : w ^ 2 ≤ r * (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 := by
    have hc : (0 : ℝ) ≤ 1 / 2 + 4 * K * r := by positivity
    have h1 : w ^ 2 ≤ ((1 / 2 + 4 * K * r) * ‖θ‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ hwnn hwle 2
    have h2 : ((1 / 2 + 4 * K * r) * ‖θ‖ ^ 2) ^ 2
        = (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * ‖θ‖ := by ring
    have h3 : (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * ‖θ‖
        ≤ (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * r := by
      have hnn : (0 : ℝ) ≤ (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 := by positivity
      exact mul_le_mul_of_nonneg_left hθ hnn
    calc w ^ 2 ≤ ((1 / 2 + 4 * K * r) * ‖θ‖ ^ 2) ^ 2 := h1
      _ = (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * ‖θ‖ := h2
      _ ≤ (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * r := h3
      _ = r * (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 := by ring
  calc |Real.log M - ‖θ‖ ^ 2 / 2| ≤ w ^ 2 + 4 * K * ‖θ‖ ^ 3 := hlog
    _ ≤ r * (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 + 4 * K * ‖θ‖ ^ 3 := by linarith
    _ = (4 * K + r * (1 / 2 + 4 * K * r) ^ 2) * ‖θ‖ ^ 3 := by ring

end StatLean.HypothesisTesting
