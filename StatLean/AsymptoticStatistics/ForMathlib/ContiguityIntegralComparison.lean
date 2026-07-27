import StatLean.AsymptoticStatistics.ForMathlib.Contiguity

/-!
# Le Cam's first lemma from an asymptotic integral comparison

`Contiguity.mutuallyContiguous_of_asymptotically_log_normal` requires the **exact**
change-of-measure identity `Q n = (P n).withDensity (exp ∘ L n)`, which for a
quadratic-mean-differentiable family holds only under a per-`n` common-support hypothesis.
This file proves the **support-free** version: the exact identity is replaced by the
asymptotic integral comparison
`|∫ g dQₙ − ∫ g · exp(Lₙ) dPₙ| ≤ C · ρₙ` (all measurable `|g| ≤ C`), with `ρₙ → 0` —
exactly the output shape of
`AsymptoticRepresentation.productMeasure_integral_comparison_boundedMeasurable`.

Main declarations:
* `Contiguity.Contiguous.comp_subseq` — contiguity restricts along a strictly monotone
  subsequence (events padded by `∅` off the subsequence);
* `Contiguity.mutuallyContiguous_of_log_normal_of_integral_comparison` — the headline
  support-free Le Cam first lemma.

**Proof formalization notes.** Direction `Q ⊲ P`: for events `Aₙ` with `Pₙ(Aₙ) → 0`,
`Qₙ(Aₙ) ≤ ∫_{Aₙ} exp(Lₙ) dPₙ + ρₙ`, and the first term `→ 0` by the uniform-integrability
argument already packaged in `Contiguity.uniform_integrability_exp_L_of_integral_tendsto_one`
(the total-mass comparison at `g ≡ 1` gives `∫ exp(Lₙ) dPₙ → 1`). Direction `P ⊲ Q`: split on
`{Lₙ ≥ −M}` for a continuity-point `M` of the Gaussian limit:
`Pₙ(Aₙ) ≤ Pₙ(Lₙ < −M) + e^M · (Qₙ(Aₙ) + ρₙ)`, and let first `n → ∞` then `M → ∞` along
continuity points (portmanteau for the weak limit of `Pₙ.map Lₙ`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics
namespace Contiguity

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Contiguity along a subsequence.** If `Q ⊲ P` along `atTop`, the same holds for the
subsequences `P ∘ φ`, `Q ∘ φ` for any strictly monotone `φ` (pad the events by `∅` off the
range of `φ`). -/
theorem Contiguous.comp_subseq {P Q : ∀ n, Measure (Ω n)}
    (hPQ : Contiguous (ι := ℕ) (Ω := Ω) atTop P Q) {φ : ℕ → ℕ}
    -- LEAN-ONLY: subsequence extraction (regularity of the index map)
    (hφ : StrictMono φ) :
    Contiguous (ι := ℕ) (Ω := fun n => Ω (φ n)) atTop
      (fun n => P (φ n)) (fun n => Q (φ n)) := by
  sorry

/-- **Le Cam's first lemma, support-free integral-comparison form.** Suppose

* `Lₙ` is a measurable "asymptotic log-likelihood" with
  `Pₙ.map Lₙ ⇝ N(−v/2, v)` (asymptotic log-normality), and
* the integral comparison holds: there is `ρₙ → 0` with
  `|∫ g dQₙ − ∫ g · exp(Lₙ) dPₙ| ≤ C · ρₙ` for every uniformly bounded measurable family
  `g` (bound `C`).

Then `P` and `Q` are mutually contiguous. This replaces the exact identity
`Qₙ = Pₙ.withDensity (exp ∘ Lₙ)` of `mutuallyContiguous_of_asymptotically_log_normal` by
asymptotic singular-mass control, which is what a DQM family actually provides (vdV §6.4,
Example 6.5, combined with the §7.2 remainder control). -/
theorem mutuallyContiguous_of_log_normal_of_integral_comparison
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ)
    -- LEAN-ONLY: measurability of the log-likelihood statistics (regularity)
    (hL_meas : ∀ n, Measurable (L n))
    -- USER-INPUT: asymptotic integral comparison replacing the exact change of measure;
    -- vdV §7.2 (supplied by `productMeasure_integral_comparison_boundedMeasurable`)
    (h_comparison : ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧
      ∀ (g : ∀ n, Ω n → ℝ) (C : ℝ), (∀ n, Measurable (g n)) → 0 ≤ C →
        (∀ n ω, |g n ω| ≤ C) → ∀ n,
        |∫ ω, g n ω ∂(Q n) - ∫ ω, g n ω * Real.exp (L n ω) ∂(P n)| ≤ C * ρ n)
    (v : NNReal)
    -- USER-INPUT: asymptotic log-normality of `Lₙ` under `Pₙ`; vdV Example 6.5
    (h_weak : WeakConverges (fun n => (P n).map (L n))
      (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    MutuallyContiguous (ι := ℕ) (Ω := Ω) atTop P Q := by
  sorry

end Contiguity
end AsymptoticStatistics
