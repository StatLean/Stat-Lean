import StatLean.TimeSeries.Process.LinearProcess
import StatLean.TimeSeries.Models.Linear
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Stationary ARMA processes: existence, causality, Yule–Walker (FY §2.1.2, §2.2.1)

The transfer coefficients `ψ = a(z)/b(z)` of an ARMA(p, q) model as formal power-series
coefficients (`armaPsi`, via `PowerSeries.inv` — well-defined since `b(0) = 1`), and:

* **FY Theorem 2.1**: if `b(z) ≠ 0` on the closed unit disc, the coefficients decay
  geometrically (Cauchy estimates on the analytic function `a/b` on a disc of radius
  `> 1`), are absolutely summable, and the linear process `X = Σ ψ_j ε_{t−j}` is a
  stationary, causal solution of the ARMA equation;
* **Definition 2.3** (causality) as `IsCausalFor`;
* the **Yule–Walker recurrences** (FY eq. (2.21)): `γ(k) = Σᵢ bᵢ γ(k−1−i)` for `k > q`;
* **Proposition 2.2(i)**: exponential decay of the ACVF of a causal ARMA process;
* the Brockwell–Davis iff-facts (causality ⇔ no roots in the closed disc; uniqueness ⇔
  no roots on the circle) as statement-level DEBTS (FY cites them without proof).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.2
(Theorem 2.1, Definition 2.3, eqs. (2.3)–(2.5), pp. 30–32) and §2.2.1 (eqs. (2.20)–(2.22),
Proposition 2.2, pp. 40–41). (`FY §2.1.2 Thm 2.1, Def 2.3; §2.2.1 eq. (2.21), Prop 2.2`.)

**Proof formalization notes.**
* `armaPsi` is defined through the formal inverse in `ℝ⟦X⟧` (constant coefficient of
  `arPoly b` is `1`); the analytic content enters only through the geometric bound.
* FY proves Theorem 2.1 by the geometric expansion of `1/b`; we route the coefficient
  bound through `HasFPowerSeriesOnBall` Cauchy estimates
  (`FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius`) after identifying the
  formal and analytic expansions (both are power-series solutions of `b · ψ = a`).
* The Yule–Walker derivation replaces the book's "independent" by "uncorrelated"
  (flagged in the inventory): causality kills the covariances of future innovations
  against the past through `L²`-limit continuity.
* Prop 2.2(i) avoids the book's distinct-roots partial-fraction argument entirely (the
  inventory flags the repeated-root gap): geometric decay of `ψ` gives
  `|γ(k)| ≤ σ² C² r^k/(1−r²)` directly.

**Bibliographic comments.** The MA(∞) solution of stationary ARMA equations is H. Wold
(1938); the systematic causality/invertibility theory is P. J. Brockwell and R. A. Davis,
*Time Series: Theory and Methods*, 2nd ed., Springer, 1991, §3.1 (Thm 3.1.1, Prop 3.1.2).
Yule–Walker equations: G. U. Yule (1927), G. T. Walker (1931).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **ARMA transfer coefficients** `ψ_n = [zⁿ] a(z)/b(z)` (FY eq. (2.5)'s `d_j`),
as formal power-series coefficients; well-defined because `b(0) = 1` makes `arPoly b`
invertible in `ℝ⟦X⟧`. -/
noncomputable def armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) : ℝ :=
  PowerSeries.coeff n
    (((maPoly a : Polynomial ℝ) : PowerSeries ℝ) *
      (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)

/-- `b` has **no roots in the closed unit disc** (over ℂ) — FY's standing condition
`b(z) ≠ 0` for `|z| ≤ 1`. -/
def NoRootClosedDisc {p : ℕ} (b : Fin p → ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ 1 → Polynomial.aeval z (arPoly b) ≠ 0

section Coeff

/-- The coefficients of the AR polynomial `b(z) = 1 - b₁z - ⋯ - b_pz^p`. -/
private lemma coeff_arPoly {p : ℕ} (b : Fin p → ℝ) (m : ℕ) :
    (arPoly b).coeff m
      = (if m = 0 then (1 : ℝ) else 0) - ∑ i : Fin p, if m = (i : ℕ) + 1 then b i else 0 := by
  simp [arPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite]

private lemma coeff_arPoly_zero {p : ℕ} (b : Fin p → ℝ) : (arPoly b).coeff 0 = 1 := by
  rw [coeff_arPoly]; simp

/-- The coefficients of the MA polynomial `a(z) = 1 + a₁z + ⋯ + a_qz^q`. -/
private lemma coeff_maPoly {q : ℕ} (a : Fin q → ℝ) (m : ℕ) :
    (maPoly a).coeff m
      = (if m = 0 then (1 : ℝ) else 0) + ∑ j : Fin q, if m = (j : ℕ) + 1 then a j else 0 := by
  simp [maPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite]

private lemma coeff_maPoly_zero {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  rw [coeff_maPoly]; simp

/-- The constant coefficient of `arPoly b` as a power series is `1`, hence nonzero: this is
what makes the formal inverse in `ℝ⟦X⟧` available. -/
private lemma constantCoeff_arPoly_ne_zero {p : ℕ} (b : Fin p → ℝ) :
    PowerSeries.constantCoeff (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
  rw [Polynomial.constantCoeff_coe, coeff_arPoly_zero]
  exact one_ne_zero

end Coeff

/-- `ψ_0 = 1` (both polynomials have constant coefficient `1`). -/
theorem armaPsi_zero {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) :
    armaPsi b a 0 = 1 := by
  rw [armaPsi, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_inv,
    Polynomial.constantCoeff_coe, Polynomial.constantCoeff_coe, coeff_arPoly_zero,
    coeff_maPoly_zero, inv_one, mul_one]

/-- The defining convolution identity `b ∗ ψ = a` (FY eq. (2.5) read coefficientwise):
`Σ_{k≤n} (arPoly b).coeff k · ψ_{n−k} = (maPoly a).coeff n`. -/
theorem arPoly_conv_armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (arPoly b).coeff k * armaPsi b a (n - k)
      = (maPoly a).coeff n := by
  have key : (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
      ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
        (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
      = (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) := by
    rw [← mul_assoc, mul_comm (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)),
      mul_assoc, PowerSeries.mul_inv_cancel _ (constantCoeff_arPoly_ne_zero b), mul_one]
  have hcoeff := congrArg (PowerSeries.coeff n) key
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.coeff_coe] at hcoeff
  rw [← hcoeff]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_coe]; rfl

section AnalyticCore

private lemma hasSum_poly_mul {c : ℕ → ℂ} {z S : ℂ} (P : Polynomial ℂ)
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

private lemma hasSum_poly (P : Polynomial ℂ) (z : ℂ) :
    HasSum (fun n => P.coeff n * z ^ n) (P.eval z) := by
  classical
  have h : HasSum (fun n => P.coeff n * z ^ n)
      (∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * z ^ n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      show P.coeff n * z ^ n = 0
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul])
  rwa [← Polynomial.eval_eq_sum_range] at h

private lemma exists_crude_bound_armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) :
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
    rwa [coeff_maPoly_zero, abs_one] at h
  obtain ⟨Cb, hCb0, hCb⟩ : ∃ C : ℝ, 1 ≤ C ∧ ∀ n, |(arPoly b).coeff n| ≤ C := by
    refine ⟨_, ?_, hbound (arPoly b)⟩
    have h := hbound (arPoly b) 0
    rwa [coeff_arPoly_zero, abs_one] at h
  refine ⟨Ca, 1 + Cb, by linarith, by linarith, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hrec := arPoly_conv_armaPsi b a n
    rw [Finset.sum_range_succ', coeff_arPoly_zero, one_mul, Nat.sub_zero] at hrec
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


end AnalyticCore

/-- **Geometric decay of the transfer coefficients** (the analytic core of FY Theorem
2.1): with no roots of `b` in the closed unit disc, `|ψ_n| ≤ C rⁿ` for some `r < 1`. -/
theorem exists_geometric_bound_armaPsi {p q : ℕ} {b : Fin p → ℝ} (a : Fin q → ℝ)
    -- USER-INPUT: no roots of b(z) in the closed unit disc; FY §2.1.2 Thm 2.1
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
    rw [h, coeff_arPoly_zero] at h0
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
  obtain ⟨C0, M, hC0, hM1, hcrude⟩ := exists_crude_bound_armaPsi b a
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
    have h1 := hasSum_poly_mul B hsum
    have hcoef : ∀ n, (∑ k ∈ Finset.range (n + 1), B.coeff k * ψc (n - k)) = A.coeff n := by
      intro n
      rw [hAc, ← arPoly_conv_armaPsi b a n]
      push_cast [hBc, hψc]
      rfl
    simp only [hcoef] at h1
    have h2 := hasSum_poly A z
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


/-- Absolute summability of the transfer coefficients (FY Theorem 2.1's `Σ|d_j| < ∞`). -/
theorem summable_abs_armaPsi {p q : ℕ} {b : Fin p → ℝ} (a : Fin q → ℝ)
    (hb : NoRootClosedDisc b) :
    Summable fun n => |armaPsi b a n| := by
  obtain ⟨C, hC, r, hr0, hr1, hbnd⟩ := exists_geometric_bound_armaPsi a hb
  exact Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbnd
    ((summable_geometric_of_lt_one hr0 hr1).mul_left C)


section Aux

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

/-- `inner ℝ` on the reals is multiplication. -/
private lemma real_inner_mul (x y : ℝ) : inner ℝ x y = x * y := by
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp [mul_comm]

/-- The `L²` inner product of two classes is the integral of the product. -/
private lemma inner_toLp {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [real_inner_mul, h1, h2]

/-- Cauchy–Schwarz for the `L²` pairing. -/
private lemma abs_integral_mul_le {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  rw [← inner_toLp hf hg]
  calc |(inner ℝ (hf.toLp f) (hg.toLp g) : ℝ)| ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ :=
        abs_real_inner_le_norm _ _
    _ = (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by rw [Lp.norm_toLp, Lp.norm_toLp]

/-- Distinct white-noise times have vanishing mixed moment. -/
private lemma integral_noise_mul_eq_zero [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    {s t : ℤ} (hst : s ≠ t) : ∫ ω, ε s ω * ε t ω ∂μ = 0 := by
  have h := covariance_eq_sub (hε.memLp s) (hε.memLp t)
  rw [hε.integral_eq_zero s, zero_mul, sub_zero, hε.uncorrelated s t hst] at h
  have h2 : μ[ε s * ε t] = ∫ ω, ε s ω * ε t ω ∂μ := by simp [Pi.mul_apply]
  rw [h2] at h
  exact h.symm

/-- The `L²` norm of the noise is the same at every time. -/
private lemma eLpNorm_noise_eq [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ) (t : ℤ) :
    eLpNorm (ε t) 2 μ = ENNReal.ofReal (Real.sqrt σ2) := by
  have hsq : ‖(hε.memLp t).toLp (ε t)‖ ^ 2 = σ2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp]
    have h := covariance_eq_sub (hε.memLp t) (hε.memLp t)
    rw [hε.integral_eq_zero t, zero_mul, sub_zero,
      covariance_self (hε.memLp t).aestronglyMeasurable.aemeasurable, hε.variance_eq t] at h
    have h2 : μ[ε t * ε t] = ∫ ω, ε t ω * ε t ω ∂μ := by simp [Pi.mul_apply]
    rw [h2] at h
    exact h.symm
  have hnorm : ‖(hε.memLp t).toLp (ε t)‖ = Real.sqrt σ2 := by
    have := Real.sqrt_sq (norm_nonneg ((hε.memLp t).toLp (ε t)))
    rw [hsq] at this
    exact this.symm
  rw [Lp.norm_toLp] at hnorm
  rw [← hnorm, ENNReal.ofReal_toReal (hε.memLp t).2.ne]

/-- The `L²` norm of a finite noise combination. -/
private lemma eLpNorm_noise_comb_le [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → ℤ) :
    eLpNorm (fun ω => ∑ i ∈ s, c i * ε (u i) ω) 2 μ
      ≤ ENNReal.ofReal (∑ i ∈ s, |c i|) * ENNReal.ofReal (Real.sqrt σ2) := by
  have hfun : (fun ω => ∑ i ∈ s, c i * ε (u i) ω) = ∑ i ∈ s, fun ω => c i * ε (u i) ω := by
    funext ω; simp
  rw [hfun]
  refine (eLpNorm_sum_le (fun i _ => ((hε.measurable (u i)).const_mul (c i)).aestronglyMeasurable)
    one_le_two).trans ?_
  have hterm : ∀ i, eLpNorm (fun ω => c i * ε (u i) ω) 2 μ
      = ENNReal.ofReal |c i| * ENNReal.ofReal (Real.sqrt σ2) := by
    intro i
    have : (fun ω => c i * ε (u i) ω) = c i • (ε (u i)) := by funext ω; simp
    rw [this, eLpNorm_const_smul, eLpNorm_noise_eq hε]
    congr 1
    simp [Real.enorm_eq_ofReal_abs]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]

end Aux

private lemma cov_noise_lin_eq_zero [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (hX : IsLinearProcessOf ψ X ε μ) (hε : IsWhiteNoise ε σ2 μ) (hmX : ∀ t, MemLp (X t) 2 μ)
    {u : ℤ} (hu : 0 < u) : cov[ε u, X 0; μ] = 0 := by
  have hcov : cov[ε u, X 0; μ] = ∫ ω, ε u ω * X 0 ω ∂μ := by
    have h := covariance_eq_sub (hε.memLp u) (hmX 0)
    rw [hε.integral_eq_zero u, zero_mul, sub_zero] at h
    have h2 : μ[ε u * X 0] = ∫ ω, ε u ω * X 0 ω ∂μ := by simp [Pi.mul_apply]
    rw [h2] at h
    exact h
  rw [hcov]
  -- the partial sums pair to zero
  have hmemP : ∀ N : ℕ, MemLp (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) 2 μ :=
    fun N => memLp_finset_sum _ fun j _ => (hε.memLp _).const_mul _
  have hzero : ∀ N : ℕ,
      ∫ ω, ε u ω * (∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) ∂μ = 0 := by
    intro N
    have hexp : ∀ ω, ε u ω * (∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω)
        = ∑ j ∈ Finset.range N, ψ j * (ε u ω * ε (0 - (j : ℕ)) ω) := by
      intro ω; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have hint : ∀ j : ℕ, Integrable (fun ω => ψ j * (ε u ω * ε (0 - (j : ℕ)) ω)) μ := fun j =>
      ((hε.memLp u).integrable_mul (hε.memLp (0 - (j : ℕ)))).const_mul (ψ j)
    simp_rw [hexp]
    rw [integral_finset_sum _ fun j _ => hint j]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, integral_noise_mul_eq_zero hε (by omega), mul_zero]
  -- the pairing with the defect tends to zero
  have hsplit : ∀ N : ℕ, ∫ ω, ε u ω * X 0 ω ∂μ
      = ∫ ω, ε u ω * (X 0 ω - ∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) ∂μ := by
    intro N
    have hint1 : Integrable (fun ω => ε u ω * X 0 ω) μ := (hε.memLp u).integrable_mul (hmX 0)
    have hint2 : Integrable
        (fun ω => ε u ω * (∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω)) μ :=
      (hε.memLp u).integrable_mul (hmemP N)
    have : ∫ ω, ε u ω * X 0 ω ∂μ
        - ∫ ω, ε u ω * (∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) ∂μ
        = ∫ ω, ε u ω * (X 0 ω - ∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) ∂μ := by
      rw [← integral_sub hint1 hint2]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    rw [← this, hzero N, sub_zero]
  have hbd : ∀ N : ℕ, |∫ ω, ε u ω * X 0 ω ∂μ|
      ≤ (eLpNorm (ε u) 2 μ).toReal
        * (eLpNorm (fun ω => X 0 ω - ∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) 2 μ).toReal := by
    intro N
    rw [hsplit N]
    exact abs_integral_mul_le (hε.memLp u) ((hmX 0).sub (hmemP N))
  have hlim : Tendsto (fun N : ℕ => (eLpNorm (ε u) 2 μ).toReal
      * (eLpNorm (fun ω => X 0 ω - ∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) 2 μ).toReal)
      atTop (𝓝 0) := by
    have h := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp (hX 0)
    simpa using h.const_mul ((eLpNorm (ε u) 2 μ).toReal)
  have habs : |∫ ω, ε u ω * X 0 ω ∂μ| ≤ 0 := by
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbd
  exact abs_eq_zero.1 (le_antisymm habs (abs_nonneg _))

/-- Covariance only sees the a.e. class of each argument. -/
private lemma covariance_congr_ae {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIX : ∫ x, X x ∂μ = ∫ x, X' x ∂μ := integral_congr_ae hX
  have hIY : ∫ x, Y x ∂μ = ∫ x, Y' x ∂μ := integral_congr_ae hY
  simp only [covariance, hIX, hIY]
  exact integral_congr_ae (by filter_upwards [hX, hY] with ω h1 h2 using by rw [h1, h2])

/-- **Causality** (FY §2.1.2, Definition 2.3): `X` is a causal function of the noise `ε`
when it is an MA(∞) over `ε` with absolutely summable coefficients. -/
def IsCausalFor (X ε : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ ψ : ℕ → ℝ, (Summable fun n => |ψ n|) ∧ IsLinearProcessOf ψ X ε μ

/-- **FY Theorem 2.1 (existence of a stationary causal ARMA solution)**: with no roots
of `b` in the closed unit disc and white noise `ε`, the linear process with the transfer
coefficients is a stationary, causal solution of the ARMA(p, q) equation. -/
theorem exists_stationary_arma [IsProbabilityMeasure μ] {p q : ℕ} {b : Fin p → ℝ}
    {a : Fin q → ℝ} {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: no roots of b(z) in the closed unit disc; FY §2.1.2 Thm 2.1
    (hb : NoRootClosedDisc b)
    -- USER-INPUT: white-noise innovations; FY eq. (2.3)
    (hε : IsWhiteNoise ε σ2 μ) :
    ∃ X : ℤ → Ω → ℝ, (∀ t, Measurable (X t)) ∧
      IsLinearProcessOf (armaPsi b a) X ε μ ∧ IsARMA b a σ2 X ε μ ∧
      IsStationary X μ ∧ IsCausalFor X ε μ := by
  sorry

/-- **Yule–Walker recurrences** (FY §2.2.1, eq. (2.21)): for a causal stationary ARMA
process and lags beyond the MA order, `γ(k) = Σᵢ bᵢ γ(k−1−i)`. -/
theorem IsARMA.acvf_yule_walker [IsProbabilityMeasure μ] {p q : ℕ} {b : Fin p → ℝ}
    {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hstat : IsStationary X μ)
    -- USER-INPUT: causality (FY: eq. (2.21) is derived for the causal solution); FY §2.2.1
    (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    (hb : NoRootClosedDisc b)
    {k : ℤ}
    -- USER-INPUT: lag beyond the MA order; FY eq. (2.21)
    (hk : (q : ℤ) < k) :
    acvf X μ k = ∑ i : Fin p, b i * acvf X μ (k - 1 - (i : ℕ)) := by
  have hψ := summable_abs_armaPsi a hb
  have hmX : ∀ t, MemLp (X t) 2 μ := hcausal.memLp hψ h.whiteNoise h.measurableX
  have hmε : ∀ t, MemLp (ε t) 2 μ := h.whiteNoise.memLp
  have hcovε : ∀ u : ℤ, 0 < u → cov[ε u, X 0; μ] = 0 :=
    fun u hu => cov_noise_lin_eq_zero hcausal h.whiteNoise hmX hu
  have hmem1 : MemLp (fun ω => ∑ i, b i * X (k - 1 - (i : ℕ)) ω) 2 μ :=
    memLp_finset_sum _ fun i _ => (hmX _).const_mul _
  have hmem3 : MemLp (fun ω => ∑ j, a j * ε (k - 1 - (j : ℕ)) ω) 2 μ :=
    memLp_finset_sum _ fun j _ => (hmε _).const_mul _
  have hstep : cov[X k, X 0; μ]
      = cov[fun ω => ∑ i, b i * X (k - 1 - (i : ℕ)) ω, X 0; μ] + cov[ε k, X 0; μ]
        + cov[fun ω => ∑ j, a j * ε (k - 1 - (j : ℕ)) ω, X 0; μ] := by
    rw [covariance_congr_ae (h.recurrence k) (EventuallyEq.refl _ (X 0))]
    have hfun : (fun ω => (∑ i, b i * X (k - 1 - (i : ℕ)) ω) + ε k ω
        + ∑ j, a j * ε (k - 1 - (j : ℕ)) ω)
        = ((fun ω => ∑ i, b i * X (k - 1 - (i : ℕ)) ω) + ε k)
          + (fun ω => ∑ j, a j * ε (k - 1 - (j : ℕ)) ω) := rfl
    rw [hfun, covariance_add_left (hmem1.add (hmε k)) hmem3 (hmX 0),
      covariance_add_left hmem1 (hmε k) (hmX 0)]
  have hz1 : cov[ε k, X 0; μ] = 0 := hcovε k (by omega)
  have hz2 : cov[fun ω => ∑ j, a j * ε (k - 1 - (j : ℕ)) ω, X 0; μ] = 0 := by
    rw [covariance_fun_sum_left (fun j => (hmε _).const_mul _) (hmX 0)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [covariance_const_mul_left, hcovε _ (by have := j.isLt; omega), mul_zero]
  have hb1 : cov[fun ω => ∑ i, b i * X (k - 1 - (i : ℕ)) ω, X 0; μ]
      = ∑ i : Fin p, b i * acvf X μ (k - 1 - (i : ℕ)) := by
    rw [covariance_fun_sum_left (fun i => (hmX _).const_mul _) (hmX 0)]
    exact Finset.sum_congr rfl fun i _ => by rw [covariance_const_mul_left]; rfl
  rw [show acvf X μ k = cov[X k, X 0; μ] from rfl, hstep, hz1, hz2, hb1]
  ring


/-- **Proposition 2.2(i)** (FY §2.2.1): the ACVF of a causal stationary ARMA process
decays exponentially. (Proved from the geometric `ψ`-bound — no distinct-roots caveat.) -/
theorem IsARMA.acvf_exponential_decay [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    (hb : NoRootClosedDisc b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ k : ℤ, |acvf X μ k| ≤ C * r ^ k.natAbs := by
  obtain ⟨C, hC, r, hr0, hr1, hbnd⟩ := exists_geometric_bound_armaPsi a hb
  have hψ := summable_abs_armaPsi a hb
  have hform := (hcausal.isStationary hψ h.whiteNoise h.measurableX).2
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hr2' : (0:ℝ) ≤ r ^ 2 := by positivity
  have hden : (0:ℝ) < 1 - r ^ 2 := by linarith
  refine ⟨|σ2| * C ^ 2 * (1 - r ^ 2)⁻¹, by positivity, r, hr0, hr1, fun k => ?_⟩
  set m := k.natAbs with hm
  have hle : ∀ j : ℕ, |armaPsi b a j * armaPsi b a (j + m)| ≤ C ^ 2 * r ^ m * (r ^ 2) ^ j := by
    intro j
    rw [abs_mul]
    have h1 : |armaPsi b a j| * |armaPsi b a (j + m)| ≤ (C * r ^ j) * (C * r ^ (j + m)) :=
      mul_le_mul (hbnd j) (hbnd (j + m)) (abs_nonneg _) (by positivity)
    refine h1.trans_eq ?_
    have hpow : (r ^ 2) ^ j = (r ^ j) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [pow_add, hpow]
    ring
  have hmaj : Summable fun j : ℕ => C ^ 2 * r ^ m * (r ^ 2) ^ j :=
    (summable_geometric_of_lt_one hr2' hr2).mul_left _
  have hsum : Summable fun j : ℕ => |armaPsi b a j * armaPsi b a (j + m)| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle hmaj
  have habs : |∑' j : ℕ, armaPsi b a j * armaPsi b a (j + m)|
      ≤ ∑' j : ℕ, |armaPsi b a j * armaPsi b a (j + m)| := by
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun j : ℕ => armaPsi b a j * armaPsi b a (j + m))
        (by simpa only [Real.norm_eq_abs] using hsum)
  have hmajsum : ∑' j : ℕ, |armaPsi b a j * armaPsi b a (j + m)|
      ≤ C ^ 2 * r ^ m * (1 - r ^ 2)⁻¹ := by
    refine (hsum.tsum_le_tsum hle hmaj).trans_eq ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr2' hr2]
  rw [hform k, abs_mul, ← hm]
  calc |σ2| * |∑' j : ℕ, armaPsi b a j * armaPsi b a (j + m)|
      ≤ |σ2| * (C ^ 2 * r ^ m * (1 - r ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (habs.trans hmajsum) (abs_nonneg _)
    _ = |σ2| * C ^ 2 * (1 - r ^ 2)⁻¹ * r ^ m := by ring


/-- **DEBT (Brockwell & Davis 1996, p. 83; FY §2.1.2 cited fact (i))**: an ARMA process
with a stationary solution is causal **iff** `b` has no roots in the closed unit disc.
The ⇐ half is `exists_stationary_arma`; the ⇒ half is a literature-level debt. -/
theorem arma_causal_of_stationary_debt [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hstat : IsStationary X μ)
    (hσ : 0 < σ2) (hcausal : IsCausalFor X ε μ) :
    NoRootClosedDisc b := by
  sorry

/-- **DEBT (Brockwell & Davis 1996, p. 82; FY §2.1.2 cited fact (ii))**: uniqueness of
the stationary solution when `b` has no roots on the unit circle: two stationary
solutions driven by the same noise agree a.e. at every time. -/
theorem arma_stationary_unique_debt [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X X' ε : ℤ → Ω → ℝ}
    -- USER-INPUT: no roots of b(z) on the unit circle; FY §2.1.2 cited fact (ii)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → Polynomial.aeval z (arPoly b) ≠ 0)
    (h : IsARMA b a σ2 X ε μ) (hstat : IsStationary X μ)
    (h' : IsARMA b a σ2 X' ε μ) (hstat' : IsStationary X' μ) (t : ℤ) :
    X t =ᵐ[μ] X' t := by
  sorry

end StatLean.TimeSeries
