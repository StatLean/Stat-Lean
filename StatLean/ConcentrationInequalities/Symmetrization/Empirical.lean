import StatLean.ConcentrationInequalities.Symmetrization.Symmetrization
import StatLean.ConcentrationInequalities.Symmetrization.GaussianMax
import StatLean.ConcentrationInequalities.ForMathlib.IndepTransport
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Symmetrization for empirical processes (HDP Exercise 8.11)

For i.i.d. data $X_1, \dots, X_n \sim P$ and a uniformly bounded class of
functions $\{f_k\}_{k \in \iota}$ with $|f_k| \le 1$,
$$ \mathbb{E}\,\sup_{k}\Bigl|\frac1n \sum_{i=1}^n f_k(X_i)
     - \mathbb{E}_P f_k\Bigr|
   \;\le\; 2\, \mathbb{E}\,\sup_{k}\Bigl|\frac1n \sum_{i=1}^n
     \varepsilon_i f_k(X_i)\Bigr|, $$
with the book's factor `2` exactly; the signs live on the product extension
`μ.prod (signVec n)`. Finite-index core plus a `Countable`-index lift per the
batch sup policy. **The RHS is deliberately uncentered** — this is the point
of the exercise.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3, Exercise 8.11 (Symmetrization for empirical
processes).

**Proof formalization notes.** Instantiate `symmetrization_upper_pi` at
`E := ι → ℝ` with the `Fintype` Pi sup-norm (Mathlib's default norm on a
finite Pi type *is* the sup norm — no `PiLp ∞` machinery) and vectors
`Zᵢ(ω) := fun k => n⁻¹ · f_k(Xᵢ(ω))`: the centering constant cancels in
`Zᵢ − Zᵢ'`, which is exactly the book's "modify the proof of Lemma 6.3.2" and
why the RHS is uncentered. Transport by `ForMathlib/IndepTransport`; norm ↔
`iSup` bridge as in `GaussianMax.pi_norm_eq_ciSup_abs`; coordinates of the
Bochner mean via `ContinuousLinearMap.proj` + `integral_comp_comm`. The
i.i.d. hypothesis is `iIndepFun X μ` + per-index pushforward `μ.map (Xᵢ) = P`
with `P` explicit (Mathlib's `HasLaw` is absent at our pin), since
`∫ f_k dP` appears in the statement. `[NeZero n]` is genuine: the statement
is **false** at `n = 0` (LHS is the sup of population means, RHS is `0`).
We state `|f_k| ≤ 1` rather than `{0,1}`-valued — free mild generality over
the book's Boolean class. Countable lift by `exists_surjective_nat` +
monotone convergence of finite sups (`tendsto_atTop_ciSup`) + dominated
convergence with constant dominators `2` resp. `1` from the class bound.
Consumer note (VC cluster, Theorem 8.3.15): a `Finset` class is consumed as
the subtype `↥s` with `F := Subtype.val`; the RHS integral over
`μ.prod (signVec n)` is designed to be Fubini'd (`integral_prod`) and
attacked per-`ω` by `FiniteMaximal` over the sign coordinate. Named-sorry
fallback of this work item: `empirical_symmetrization_countable` (the
finite-index core — the VC cluster's actual consumption shape — fully
proven).

**Bibliographic comments.** Symmetrization of empirical processes is the
Giné–Zinn school's basic tool, going back to V. N. Vapnik and A. Ya.
Chervonenkis (1971) and formalized in E. Giné and J. Zinn, "Some limit
theorems for empirical processes," *Ann. Probab.* 12 (1984), 929–989; the
textbook treatment is van der Vaart–Wellner, *Weak Convergence and Empirical
Processes* (1996), §2.3.2, and HDP §8.3 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Symmetrization for empirical processes, finite class** (HDP §8.3,
Exercise 8.11): `E sup_k |n⁻¹ ∑ᵢ f_k(Xᵢ) − E_P f_k| ≤ 2 E sup_k |n⁻¹ ∑ᵢ εᵢ
f_k(Xᵢ)|`, signs on the product extension `μ.prod (signVec n)`. The RHS is
deliberately uncentered. -/
theorem empirical_symmetrization {α : Type*} [MeasurableSpace α] {ι : Type*}
    [Fintype ι] [Nonempty ι] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    [NeZero n] {X : Fin n → Ω → α} {P : Measure α} [IsProbabilityMeasure P]
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent sample; HDP Exercise 8.11
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: identically distributed with law P; HDP Exercise 8.11
    (hX_law : ∀ i, μ.map (X i) = P)
    {F : ι → α → ℝ}
    -- LEAN-ONLY: measurability of the class members
    (hF_meas : ∀ k, Measurable (F k))
    -- USER-INPUT: uniformly bounded (Boolean) class, |f_k| ≤ 1; HDP Exercise 8.11
    (hF_bdd : ∀ k x, |F k x| ≤ 1) :
    ∫ ω, ⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P| ∂μ
      ≤ 2 * ∫ p, ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)|
          ∂(μ.prod (signVec n)) := by
  classical
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  -- The `E := ι → ℝ`-valued data `Zᵢ(ω) = fun k => n⁻¹ · f_k(Xᵢ ω)`.
  set Z : Fin n → Ω → (ι → ℝ) := fun i ω k => (n : ℝ)⁻¹ * F k (X i ω) with hZ
  have hZ_meas : ∀ i, Measurable (Z i) := by
    intro i
    rw [measurable_pi_iff]
    intro k
    exact measurable_const.mul ((hF_meas k).comp (hX_meas i))
  have hZ_indep : iIndepFun Z μ := by
    rw [hZ]
    exact hX_indep.comp (fun (_ : Fin n) (a : α) (k : ι) => (n : ℝ)⁻¹ * F k a)
      (fun _ => by rw [measurable_pi_iff]; intro k; exact measurable_const.mul (hF_meas k))
  haveI hνp : ∀ i, IsProbabilityMeasure (μ.map (Z i)) :=
    fun i => Measure.isProbabilityMeasure_map (hZ_meas i).aemeasurable
  -- Boundedness ⇒ integrability of the class members and of `Zᵢ`.
  have hFX_int : ∀ i k, Integrable (fun ω => F k (X i ω)) μ := by
    intro i k
    refine Integrable.of_mem_Icc (-1) 1 ((hF_meas k).comp (hX_meas i)).aemeasurable ?_
    filter_upwards with ω
    exact Set.mem_Icc.mpr (abs_le.mp (hF_bdd k (X i ω)))
  have hZ_int : ∀ i, Integrable (Z i) μ := by
    intro i
    rw [integrable_pi_iff]
    intro k
    simp only [hZ]
    exact (hFX_int i k).const_mul _
  have hν_int : ∀ i, Integrable id (μ.map (Z i)) := fun i =>
    (integrable_map_measure aestronglyMeasurable_id (hZ_meas i).aemeasurable).mpr
      (by simpa using hZ_int i)
  have hev : ∀ i, ∀ j : ι, Integrable (fun z : ι → ℝ => z j) (μ.map (Z i)) := by
    intro i j
    simpa using (integrable_pi_iff.mp (hν_int i)) j
  -- The coordinate mean is `n⁻¹ ∫ f_k dP` (law transfer).
  have hc : ∀ i (k : ι), (∫ z, z ∂(μ.map (Z i))) k = (n : ℝ)⁻¹ * ∫ x, F k x ∂P := by
    intro i k
    rw [eval_integral (hev i) k,
      integral_map (hZ_meas i).aemeasurable (measurable_pi_apply k).aestronglyMeasurable]
    simp only [hZ]
    rw [integral_const_mul]
    congr 1
    rw [← hX_law i, integral_map (hX_meas i).aemeasurable (hF_meas k).aestronglyMeasurable]
  -- Pointwise: the LHS integrand is the centered-sum norm on `ι → ℝ`.
  have hpt_L : ∀ ω, ⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|
      = ‖∑ i, (Z i ω - ∫ z, z ∂(μ.map (Z i)))‖ := by
    intro ω
    rw [pi_norm_eq_ciSup_abs]
    refine iSup_congr fun k => ?_
    congr 1
    have e1 : ∀ i : Fin n, (Z i ω - ∫ z, z ∂(μ.map (Z i))) k
        = (n : ℝ)⁻¹ * F k (X i ω) - (n : ℝ)⁻¹ * ∫ x, F k x ∂P := by
      intro i
      rw [Pi.sub_apply, hc i k]
    rw [Finset.sum_apply, Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib,
      Finset.sum_const, ← Finset.mul_sum, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  -- Pointwise: the RHS integrand is the sign-randomized sum norm.
  have hpt_R : ∀ p : Ω × (Fin n → ℝ),
      ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)| = ‖∑ i, p.2 i • Z i p.1‖ := by
    intro p
    rw [pi_norm_eq_ciSup_abs]
    refine iSup_congr fun k => ?_
    congr 1
    rw [Finset.sum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.smul_apply, smul_eq_mul]
    simp only [hZ]
    ring
  -- Measurability of the two integrands over the canonical products.
  have hG : AEStronglyMeasurable
      (fun y : Fin n → (ι → ℝ) => ‖∑ i, (y i - ∫ z, z ∂(μ.map (Z i)))‖)
      (Measure.pi fun i => μ.map (Z i)) := by
    have hm : Measurable
        (fun y : Fin n → (ι → ℝ) => ∑ i, (y i - ∫ z, z ∂(μ.map (Z i)))) :=
      Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).sub measurable_const)
    exact hm.norm.aestronglyMeasurable
  have hH : AEStronglyMeasurable
      (fun q : (Fin n → (ι → ℝ)) × (Fin n → ℝ) => ‖∑ i, q.2 i • q.1 i‖)
      ((Measure.pi fun i => μ.map (Z i)).prod (signVec n)) := by
    have hm : Measurable
        (fun q : (Fin n → (ι → ℝ)) × (Fin n → ℝ) => ∑ i, q.2 i • q.1 i) := by
      apply Finset.measurable_sum
      intro i _
      exact ((measurable_pi_apply i).comp measurable_snd).smul
        ((measurable_pi_apply i).comp measurable_fst)
    exact hm.norm.aestronglyMeasurable
  -- Transport both sides to the canonical product laws.
  have hLHS : ∫ ω, ⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P| ∂μ
      = ∫ y, ‖∑ i, (y i - ∫ z, z ∂(μ.map (Z i)))‖
          ∂(Measure.pi fun i => μ.map (Z i)) := by
    rw [integral_congr_ae (ae_of_all _ hpt_L)]
    exact integral_eq_integral_pi_map (fun i => (hZ_meas i).aemeasurable) hZ_indep hG
  have hRHS : ∫ p, ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)| ∂(μ.prod (signVec n))
      = ∫ q, ‖∑ i, q.2 i • q.1 i‖
          ∂((Measure.pi fun i => μ.map (Z i)).prod (signVec n)) := by
    rw [integral_congr_ae (ae_of_all _ hpt_R)]
    exact integral_prod_eq_integral_pi_prod hZ_meas hZ_indep hH
  rw [hLHS, hRHS]
  exact symmetrization_upper_pi (fun i => μ.map (Z i)) hν_int

/-- **Symmetrization for empirical processes, countable class** (HDP §8.3,
Exercise 8.11): the `Countable ι` lift of `empirical_symmetrization` per the
batch sup policy, by exhaustion along a surjective enumeration + dominated
convergence (constant dominators from the class bound). Named-sorry debt
candidate of this work item. -/
theorem empirical_symmetrization_countable {α : Type*} [MeasurableSpace α]
    {ι : Type*} [Countable ι] [Nonempty ι] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} [NeZero n] {X : Fin n → Ω → α}
    {P : Measure α} [IsProbabilityMeasure P]
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent sample; HDP Exercise 8.11
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: identically distributed with law P; HDP Exercise 8.11
    (hX_law : ∀ i, μ.map (X i) = P)
    {F : ι → α → ℝ}
    -- LEAN-ONLY: measurability of the class members
    (hF_meas : ∀ k, Measurable (F k))
    -- USER-INPUT: uniformly bounded (Boolean) class, |f_k| ≤ 1; HDP Exercise 8.11
    (hF_bdd : ∀ k x, |F k x| ≤ 1) :
    ∫ ω, ⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P| ∂μ
      ≤ 2 * ∫ p, ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)|
          ∂(μ.prod (signVec n)) := by
  sorry

end StatLean.ConcentrationInequalities
