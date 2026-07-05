import StatLean.ConcentrationInequalities.Symmetrization.Symmetrization
import StatLean.ConcentrationInequalities.ForMathlib.IndepTransport

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
  sorry

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
