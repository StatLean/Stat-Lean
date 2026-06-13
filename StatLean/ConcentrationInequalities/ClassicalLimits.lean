import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Classical limit theorems (Lu, *Big Data Analysis* §2.1)

Book-faithful statements of the two classical limit theorems for i.i.d. real-valued
random variables, each proved by a thin delegation to Mathlib.

* `law_of_large_numbers_in_probability` — the (weak) law of large numbers:
  for i.i.d. integrable `X i`, the sample mean converges *in probability*
  to `μ := E[X 0]`.  Delegates to `ProbabilityTheory.strong_law_ae`
  (a.e. ⟹ in-measure on a probability space).

* `central_limit_theorem` — the i.i.d. CLT:
  `(√n)⁻¹ · (∑_{k<n} X k − n · μ)` converges *in distribution* to `N(0, σ²)`,
  where `σ² = Var(X 0)`.  Delegates to
  `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`.

## Book → Lean hypothesis strengthening

The book (Lu BDA §2.1) states the LLN under "i.i.d., finite mean" and the CLT under
"i.i.d., finite mean and variance".  Mathlib requires:

* Strong-law form (`strong_law_ae`): `Integrable (X 0)`, pairwise independence,
  identical distribution.  We take the (book-equivalent, slightly stronger) mutual
  independence `iIndepFun X P` and derive pairwise independence via `iIndepFun.indepFun`.

* CLT form (`tendstoInDistribution_inv_sqrt_mul_sum_sub`): `MemLp (X 0) 2 P`
  (the textbook's "finite variance" — equivalent on a probability space to
  `Integrable` + finite second moment), `iIndepFun X P`, identical distribution,
  and a witness `Y` on a (possibly different) probability space `(Ω', P')`
  carrying the target Gaussian law `N(0, σ²)`.  We mirror these hypotheses
  verbatim; the `MemLp 2` strengthening over the book's bare "finite variance"
  is harmless on a probability space.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace StatLean.ConcentrationInequalities

/-- **Law of Large Numbers, in probability** (Lu BDA §2.1).

For an i.i.d. sequence `X 0, X 1, …` of real-valued random variables on a
probability space `(Ω, P)` with `E |X 0| < ∞`, the sample mean
`n⁻¹ · ∑_{i<n} X i` converges *in probability* to `μ := E[X 0]`.

Proof: Mathlib's `strong_law_ae` gives a.e. convergence; on a probability
(hence finite) measure, a.e. convergence implies convergence in measure
via `MeasureTheory.tendstoInMeasure_of_tendsto_ae`.

The book's "i.i.d." is encoded here as mutual independence (`iIndepFun`) plus
identical distribution — the standard formalization. Pairwise independence
(what `strong_law_ae` consumes) is derived internally. -/
theorem law_of_large_numbers_in_probability
    {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    -- USER-INPUT: integrability of X 0 (book: "finite mean"); Lu-BDA §2.1
    (hint : Integrable (X 0) P)
    -- USER-INPUT: mutual independence of the sequence (book: "i.i.d."); Lu-BDA §2.1
    (hindep : iIndepFun X P)
    -- USER-INPUT: identical distributions (book: "i.i.d."); Lu-BDA §2.1
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) atTop
      (fun _ => ∫ x, X 0 x ∂P) := by
  have hpair : Pairwise (Function.onFun (fun x y => IndepFun x y P) X) :=
    fun _ _ hij => hindep.indepFun hij
  have hae := ProbabilityTheory.strong_law_ae X hint hpair hident
  have hX_ae : ∀ i, AEStronglyMeasurable (X i) P :=
    fun i => (hident i).aestronglyMeasurable_fst
  have hf_ae : ∀ (n : ℕ), AEStronglyMeasurable
      (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) P := fun (n : ℕ) =>
    ((Finset.aestronglyMeasurable_sum (Finset.range n) (fun i _ => hX_ae i)).congr
        (Filter.Eventually.of_forall fun ω => Finset.sum_apply ω _ X)).const_smul' _
  exact MeasureTheory.tendstoInMeasure_of_tendsto_ae hf_ae hae

/-- **Central Limit Theorem** (Lu BDA §2.1).

For an i.i.d. sequence `X 0, X 1, …` of real-valued random variables on a
probability space `(Ω, P)` with `X 0 ∈ L²(P)`, the centered-and-scaled partial
sums
  `(√n)⁻¹ · (∑_{k<n} X k − n · E[X 0])`
converge *in distribution* (under `P`) to a real Gaussian random variable
`Y` with mean `0` and variance `σ² = Var(X 0)`, defined on an auxiliary
probability space `(Ω', P')`.

This is the book's CLT in the standard "sum-form" Lindeberg–Lévy normalization;
the more familiar `√n · ((X̄ₙ − μ)/σ) → N(0,1)` form is obtained by dividing
through by `σ > 0` (i.e. by composing with the affine `y ↦ y/σ`, which sends
`N(0, σ²)` to `N(0,1)`).

Proof: direct delegation to `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`. -/
theorem central_limit_theorem
    {Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    -- USER-INPUT: target Gaussian witness on (Ω', P') with variance σ² = Var(X 0); Lu-BDA §2.1
    (hY : HasLaw Y (gaussianReal 0 (variance (X 0) P).toNNReal) P')
    -- USER-INPUT: finite second moment of X 0 (book: "finite variance"); Lu-BDA §2.1
    -- LEAN-ONLY strengthening: Mathlib's CLT statement is phrased with `MemLp _ 2`,
    -- which on a probability space is equivalent to the book's "finite variance".
    (hX : MemLp (X 0) 2 P)
    -- USER-INPUT: mutual independence of the sequence (book: "i.i.d."); Lu-BDA §2.1
    (hindep : iIndepFun X P)
    -- USER-INPUT: identical distributions (book: "i.i.d."); Lu-BDA §2.1
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, X k ω - (n : ℝ) * ∫ x, X 0 x ∂P))
      atTop Y (fun _ => P) P' :=
  ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hindep hident

end StatLean.ConcentrationInequalities
