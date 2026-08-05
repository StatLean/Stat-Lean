import StatLean.TimeSeries.Stationarity.ARMAExistence
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal NNReal

namespace StatLean.TimeSeries

/-! ### L1: Cauchy product with a polynomial -/

lemma hasSum_poly_mul_scratch {c : ℕ → ℂ} {z S : ℂ} (P : Polynomial ℂ)
    (h : HasSum (fun n => c n * z ^ n) S) :
    HasSum (fun n => (∑ k ∈ Finset.range (n + 1), P.coeff k * c (n - k)) * z ^ n)
      (P.eval z * S) := by
  classical
  have hcz : ∀ k, P.natDegree < k → P.coeff k = 0 := fun k hk =>
    Polynomial.coeff_eq_zero_of_natDegree_lt hk
  have hkey : ∀ k : ℕ, HasSum (fun m => (if k ≤ m then P.coeff k * c (m - k) else 0) * z ^ m)
      (P.coeff k * z ^ k * S) := by
    intro k
    have h1 : HasSum (fun n => P.coeff k * z ^ k * (c n * z ^ n)) (P.coeff k * z ^ k * S) :=
      h.mul_left _
    have hg : Function.Injective (fun n : ℕ => k + n) := add_right_injective k
    have hzero : ∀ x ∉ Set.range (fun n : ℕ => k + n),
        (if k ≤ x then P.coeff k * c (x - k) else 0) * z ^ x = 0 := by
      intro x hx
      rw [if_neg, zero_mul]
      intro hkx
      exact hx ⟨x - k, by show k + (x - k) = x; omega⟩
    refine (hg.hasSum_iff hzero).1 ?_
    have heq : ((fun m => (if k ≤ m then P.coeff k * c (m - k) else 0) * z ^ m) ∘
        fun n : ℕ => k + n) = fun n => P.coeff k * z ^ k * (c n * z ^ n) := by
      funext n
      simp only [Function.comp_apply, if_pos (Nat.le_add_right k n), Nat.add_sub_cancel_left,
        pow_add]
      ring
    rw [heq]
    exact h1
  have hsum := hasSum_sum (s := Finset.range (P.natDegree + 1)) (fun k _ => hkey k)
  have hrhs : ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * z ^ k * S = P.eval z * S := by
    rw [← Finset.sum_mul, ← Polynomial.eval_eq_sum_range]
  rw [hrhs] at hsum
  have hfun : (fun m => ∑ k ∈ Finset.range (P.natDegree + 1),
        (if k ≤ m then P.coeff k * c (m - k) else 0) * z ^ m)
      = fun n => (∑ k ∈ Finset.range (n + 1), P.coeff k * c (n - k)) * z ^ n := by
    funext m
    rw [← Finset.sum_mul]
    congr 1
    obtain ⟨N, hNd, hNm⟩ : ∃ N : ℕ, P.natDegree ≤ N ∧ m ≤ N :=
      ⟨max P.natDegree m, le_max_left _ _, le_max_right _ _⟩
    have e1 : ∑ k ∈ Finset.range (P.natDegree + 1),
          (if k ≤ m then P.coeff k * c (m - k) else 0)
        = ∑ k ∈ Finset.range (N + 1), (if k ≤ m then P.coeff k * c (m - k) else 0) := by
      have hsub : Finset.range (P.natDegree + 1) ⊆ Finset.range (N + 1) := by
        intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
      refine Finset.sum_subset hsub fun k _ hk => ?_
      simp only [Finset.mem_range, not_lt] at hk
      rw [hcz k (by omega)]
      simp
    have e2 : ∑ k ∈ Finset.range (m + 1), P.coeff k * c (m - k)
        = ∑ k ∈ Finset.range (N + 1), (if k ≤ m then P.coeff k * c (m - k) else 0) := by
      have hsub : Finset.range (m + 1) ⊆ Finset.range (N + 1) := by
        intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
      rw [← Finset.sum_subset hsub (fun k _ hk => by
        simp only [Finset.mem_range, not_lt] at hk
        rw [if_neg (by omega)])]
      exact Finset.sum_congr rfl fun k hk => by
        simp only [Finset.mem_range] at hk
        rw [if_pos (by omega)]
    rw [e1, e2]
  rwa [hfun] at hsum

/-! ### L2: a polynomial is its own (finitely supported) power series -/

lemma hasSum_poly_scratch (P : Polynomial ℂ) (z : ℂ) :
    HasSum (fun n => P.coeff n * z ^ n) (P.eval z) := by
  classical
  have h : HasSum (fun n => P.coeff n * z ^ n)
      (∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * z ^ n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      show P.coeff n * z ^ n = 0
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul])
  rwa [← Polynomial.eval_eq_sum_range] at h

/-! ### L3: crude exponential bound -/

lemma coeff_arPoly_zero' {p : ℕ} (b : Fin p → ℝ) : (arPoly b).coeff 0 = 1 := by
  simp [arPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

lemma coeff_maPoly_zero' {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  simp [maPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

lemma exists_crude_bound_scratch {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) :
    ∃ C M : ℝ, 0 ≤ C ∧ 1 ≤ M ∧ ∀ n, |armaPsi b a n| ≤ C * M ^ n := by
  classical
  have hbound : ∀ (P : Polynomial ℝ) (n : ℕ),
      |P.coeff n| ≤ ∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j| := by
    intro P n
    by_cases hn : n ≤ P.natDegree
    · exact Finset.single_le_sum (f := fun j => |P.coeff j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), abs_zero]
      exact Finset.sum_nonneg fun j _ => abs_nonneg _
  obtain ⟨Ca, hCa0, hCa⟩ : ∃ C : ℝ, 1 ≤ C ∧ ∀ n, |(maPoly a).coeff n| ≤ C := by
    refine ⟨_, ?_, hbound (maPoly a)⟩
    have h := hbound (maPoly a) 0
    rwa [coeff_maPoly_zero', abs_one] at h
  obtain ⟨Cb, hCb0, hCb⟩ : ∃ C : ℝ, 1 ≤ C ∧ ∀ n, |(arPoly b).coeff n| ≤ C := by
    refine ⟨_, ?_, hbound (arPoly b)⟩
    have h := hbound (arPoly b) 0
    rwa [coeff_arPoly_zero', abs_one] at h
  refine ⟨Ca, 1 + Cb, by linarith, by linarith, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hrec := arPoly_conv_armaPsi b a n
    rw [Finset.sum_range_succ', coeff_arPoly_zero', one_mul, Nat.sub_zero] at hrec
    have hpsi : armaPsi b a n = (maPoly a).coeff n
        - ∑ i ∈ Finset.range n, (arPoly b).coeff (i + 1) * armaPsi b a (n - (i + 1)) := by
      linarith
    have htri : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
      calc |x - y| = |x + -y| := by rw [sub_eq_add_neg]
        _ ≤ |x| + |-y| := abs_add_le _ _
        _ = |x| + |y| := by rw [abs_neg]
    have h1 : |armaPsi b a n| ≤ |(maPoly a).coeff n|
        + ∑ i ∈ Finset.range n, |(arPoly b).coeff (i + 1) * armaPsi b a (n - (i + 1))| := by
      rw [hpsi]
      exact (htri _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    have h2 : ∑ i ∈ Finset.range n, |(arPoly b).coeff (i + 1) * armaPsi b a (n - (i + 1))|
        ≤ ∑ i ∈ Finset.range n, Cb * (Ca * (1 + Cb) ^ (n - 1 - i)) := by
      refine Finset.sum_le_sum fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [abs_mul, show n - (i + 1) = n - 1 - i by omega]
      exact mul_le_mul (hCb _) (ih _ (by omega)) (abs_nonneg _) (by linarith)
    have hrefl : ∑ j ∈ Finset.range n, (1 + Cb) ^ (n - 1 - j)
        = ∑ j ∈ Finset.range n, (1 + Cb) ^ j :=
      Finset.sum_range_reflect (fun j => (1 + Cb) ^ j) n
    have h3 : ∑ i ∈ Finset.range n, Cb * (Ca * (1 + Cb) ^ (n - 1 - i))
        = Cb * Ca * ∑ j ∈ Finset.range n, (1 + Cb) ^ j := by
      rw [← hrefl, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hgeom : (∑ j ∈ Finset.range n, (1 + Cb) ^ j) * Cb = (1 + Cb) ^ n - 1 := by
      have h := geom_sum_mul (1 + Cb) n
      rwa [add_sub_cancel_left] at h
    calc |armaPsi b a n|
        ≤ |(maPoly a).coeff n|
          + ∑ i ∈ Finset.range n, |(arPoly b).coeff (i + 1) * armaPsi b a (n - (i + 1))| := h1
      _ ≤ Ca + Cb * Ca * ∑ j ∈ Finset.range n, (1 + Cb) ^ j := by
          rw [← h3]; exact add_le_add (hCa n) h2
      _ = Ca + Ca * ((1 + Cb) ^ n - 1) := by rw [← hgeom]; ring
      _ = Ca * (1 + Cb) ^ n := by ring

/-! ### L4: assembly -/

open Polynomial in
lemma exists_geometric_scratch {p q : ℕ} {b : Fin p → ℝ} (a : Fin q → ℝ)
    (hb : NoRootClosedDisc b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n, |armaPsi b a n| ≤ C * r ^ n := by
  classical
  obtain ⟨A, hAdef⟩ : ∃ A : Polynomial ℂ, A = (maPoly a).map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Polynomial ℂ, B = (arPoly b).map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  have hAc : ∀ k, A.coeff k = ((maPoly a).coeff k : ℂ) := by
    intro k; rw [hAdef, Polynomial.coeff_map]; simp
  have hBc : ∀ k, B.coeff k = ((arPoly b).coeff k : ℂ) := by
    intro k; rw [hBdef, Polynomial.coeff_map]; simp
  have hBev : ∀ z : ℂ, B.eval z = Polynomial.aeval z (arPoly b) := by
    intro z; rw [hBdef, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hBne : B ≠ 0 := by
    intro h
    have h0 := hBc 0
    rw [h, coeff_arPoly_zero'] at h0
    simp at h0
  have hBdisc : ∀ z : ℂ, ‖z‖ ≤ 1 → B.eval z ≠ 0 := fun z hz => by rw [hBev]; exact hb z hz
  -- a radius `R > 1` free of roots of `B`
  obtain ⟨R, hR1, hRroot⟩ : ∃ R : ℝ, 1 < R ∧ ∀ z : ℂ, ‖z‖ ≤ R → B.eval z ≠ 0 := by
    obtain ⟨S, hS⟩ : ∃ S : Finset ℝ, S = insert (2 : ℝ) (B.roots.toFinset.image fun z => ‖z‖) :=
      ⟨_, rfl⟩
    have hSne : S.Nonempty := ⟨2, by rw [hS]; exact Finset.mem_insert_self _ _⟩
    have hSgt : ∀ x ∈ S, 1 < x := by
      intro x hx
      rw [hS, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · norm_num
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
        have hzr : B.eval z = 0 := (Polynomial.mem_roots'.1 (Multiset.mem_toFinset.1 hz)).2
        by_contra hcon
        exact hBdisc z (by linarith [not_lt.1 hcon]) hzr
    refine ⟨(1 + S.min' hSne) / 2, by linarith [hSgt _ (S.min'_mem hSne)], ?_⟩
    intro z hz hzero
    have hmem : ‖z‖ ∈ S := by
      rw [hS]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
        (Multiset.mem_toFinset.2 (Polynomial.mem_roots'.2 ⟨hBne, hzero⟩)))
    have := S.min'_le _ hmem
    have := hSgt _ (S.min'_mem hSne)
    linarith
  obtain ⟨R', hR'1, hR'R⟩ : ∃ R' : NNReal, 1 < (R' : ℝ) ∧ ((R' : ℝ)) ≤ R := by
    refine ⟨R.toNNReal, ?_, ?_⟩ <;> rw [Real.coe_toNNReal _ (by linarith)]
    · exact hR1
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun z => A.eval z / B.eval z := ⟨_, rfl⟩
  have hdiff : DifferentiableOn ℂ g (Metric.closedBall 0 (R' : ℝ)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    refine DifferentiableAt.differentiableWithinAt ?_
    rw [hgdef]
    exact A.differentiableAt.div B.differentiableAt (hRroot z (le_trans hz hR'R))
  have hR'pos : (0 : NNReal) < R' := by
    have : (0:ℝ) < (R' : ℝ) := by linarith
    exact_mod_cast this
  have hcauchy := hdiff.hasFPowerSeriesOnBall hR'pos
  -- the formal series of the ARMA coefficients
  obtain ⟨C0, M, hC0, hM1, hcrude⟩ := exists_crude_bound_scratch b a
  obtain ⟨ψc, hψc⟩ : ∃ f : ℕ → ℂ, f = fun n => ((armaPsi b a n : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      P = FormalMultilinearSeries.ofScalars ℂ ψc := ⟨_, rfl⟩
  have hΨnorm : ∀ n, ‖Ψ n‖ = |armaPsi b a n| := by
    intro n
    rw [hΨ, FormalMultilinearSeries.ofScalars_norm, hψc]
    simp
  have hMpos : (0:ℝ) < M := by linarith
  have hradpos : 0 < Ψ.radius := by
    have hcoe : ((M⁻¹).toNNReal : ℝ) = M⁻¹ := Real.coe_toNNReal _ (by positivity)
    have hle : (((M⁻¹).toNNReal : NNReal) : ENNReal) ≤ Ψ.radius := by
      refine Ψ.le_radius_of_bound C0 (r := (M⁻¹).toNNReal) fun n => ?_
      rw [hΨnorm, hcoe, inv_pow]
      have hpow : (0:ℝ) < M ^ n := by positivity
      calc |armaPsi b a n| * (M ^ n)⁻¹ ≤ (C0 * M ^ n) * (M ^ n)⁻¹ := by
            exact mul_le_mul_of_nonneg_right (hcrude n) (by positivity)
        _ = C0 := by field_simp
    refine lt_of_lt_of_le ?_ hle
    have : (0:ℝ) < ((M⁻¹).toNNReal : ℝ) := by rw [hcoe]; positivity
    exact_mod_cast this
  have hΨball : HasFPowerSeriesOnBall Ψ.sum Ψ 0 Ψ.radius :=
    Ψ.hasFPowerSeriesOnBall hradpos
  obtain ⟨r1, hr1pos, hr1rad, hr1one⟩ :
      ∃ r1 : ENNReal, 0 < r1 ∧ r1 ≤ Ψ.radius ∧ r1 ≤ 1 :=
    ⟨min Ψ.radius 1, lt_min hradpos (by norm_num), min_le_left _ _, min_le_right _ _⟩
  have hΨsmall : HasFPowerSeriesOnBall Ψ.sum Ψ 0 r1 := hΨball.mono hr1pos hr1rad
  have heqon : Set.EqOn Ψ.sum g (Metric.eball (0 : ℂ) r1) := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := by
      have h1 : (‖z‖₊ : ENNReal) < r1 := by
        simpa [Metric.eball, edist_eq_enorm_sub] using hz
      have h2 : (‖z‖₊ : ENNReal) < 1 := lt_of_lt_of_le h1 hr1one
      have : ‖z‖₊ < 1 := by exact_mod_cast h2
      exact le_of_lt (by exact_mod_cast this)
    have hsum : HasSum (fun n => ψc n * z ^ n) (Ψ.sum z) := by
      have h := hΨsmall.hasSum (y := z) hz
      rw [zero_add] at h
      have h' : ∀ n : ℕ, Ψ n (fun _ => z) = ψc n * z ^ n := fun n => by
        rw [hΨ, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
      simpa only [h'] using h
    have h1 := hasSum_poly_mul_scratch B hsum
    have hcoef : ∀ n, (∑ k ∈ Finset.range (n + 1), B.coeff k * ψc (n - k)) = A.coeff n := by
      intro n
      rw [hAc, ← arPoly_conv_armaPsi b a n]
      push_cast [hBc, hψc]
      rfl
    simp only [hcoef] at h1
    have h2 := hasSum_poly_scratch A z
    have hkey := h1.unique h2
    rw [hgdef]
    rw [eq_div_iff (hBdisc z hzn)]
    simpa [mul_comm] using hkey
  have hΨg : HasFPowerSeriesOnBall g Ψ 0 r1 := hΨsmall.congr heqon
  have hfinal : HasFPowerSeriesOnBall g Ψ 0 (R' : ENNReal) := hΨg.exchange_radius hcauchy
  have h1rad : ((1 : NNReal) : ENNReal) < Ψ.radius := by
    refine lt_of_lt_of_le ?_ hfinal.r_le
    exact_mod_cast hR'1
  obtain ⟨α, hα, C, hC, hbnd⟩ := Ψ.norm_mul_pow_le_mul_pow_of_lt_radius h1rad
  refine ⟨C, le_of_lt hC, α, le_of_lt hα.1, hα.2, fun n => ?_⟩
  have h := hbnd n
  rw [hΨnorm] at h
  simpa using h

end StatLean.TimeSeries
