import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Deterministic argmin consistency

The elementary analytic lemma behind vdV's application of the argmax theorem in Theorem 10.8
(Corollary 5.58 there): if a sequence of `ℝ≥0∞`-valued criteria converges to a **fixed**
continuous function `g` with a unique minimizer, uniformly on a ball containing the relevant
points, then approximate minimizers converge to the minimizer. Deterministic sequences only —
the in-probability version is obtained pointwise on good events in `Theorem10_8.lean`.

* `exists_gap_of_unique_argmin` — well-separation on balls: continuity + uniqueness of the
  minimizer produce a positive gap `g(u₀) + η ≤ g(u)` for `‖u − u₀‖ ≥ ρ`, `‖u‖ ≤ R`
  (compactness of the annulus; no coercivity needed);
* `argmin_tendsto_of_uniform_approx` — approximate minimizers of criteria that two-sidedly
  approximate `g` on a ball, and stay in the ball, converge to `u₀`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 5, §5.9
(Corollary 5.58) and Chapter 10, §10.3 (its use in Theorem 10.8, p. 149).

**Proof formalization notes.** This replaces the `ℓ^∞(K)`-valued weak-convergence route of
the book by a direct in-probability argument (the limit criterion in Theorem 10.8 is `g`
recentred by the random `Δₙ`, so after recentring the limit is *deterministic*); recorded as
a formalization deviation in the Theorem 10.8 file.
-/

open Filter Topology
open scoped ENNReal

namespace StatLean.Bayesian

variable {k : ℕ}

/-- **Well-separation of a unique minimizer on balls**: if `g` is continuous with
`g u₀ < g u` for every `u ≠ u₀`, then for every radius `R > ‖u₀‖` and every `ρ > 0` there is
a positive gap `η` with `g u₀ + η ≤ g u` whenever `‖u‖ ≤ R` and `ρ ≤ ‖u − u₀‖`. -/
theorem exists_gap_of_unique_argmin {g : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    -- LEAN-ONLY: continuity of the limit criterion (derived from the Gaussian density)
    (hg : Continuous g) {u₀ : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: uniqueness of the minimizer; vdV Thm 10.8 ("any two minimizers coincide")
    (hunique : ∀ u, u ≠ u₀ → g u₀ < g u)
    {R : ℝ}
    -- LEAN-ONLY: the ball contains the minimizer
    (hR : ‖u₀‖ < R) {ρ : ℝ}
    -- LEAN-ONLY: nontrivial exclusion radius
    (hρ : 0 < ρ) :
    ∃ η : ℝ≥0∞, 0 < η ∧
      ∀ u, ‖u‖ ≤ R → ρ ≤ ‖u - u₀‖ → g u₀ + η ≤ g u := by
  sorry

/-- **Deterministic argmin consistency**: let `τₘ` be `εₘ`-approximate minimizers over the
ball `B̄(0,R)` of criteria `zₘ` that two-sidedly approximate `g` on the ball within `δₘ`,
with `εₘ, δₘ → 0` and `‖τₘ‖ ≤ R`; if `g` is continuous with unique minimizer `u₀`,
`‖u₀‖ < R`, then `τₘ → u₀`. -/
theorem argmin_tendsto_of_uniform_approx {g : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    -- LEAN-ONLY: continuity of the limit criterion (derived from the Gaussian density)
    (hg : Continuous g) {u₀ : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: uniqueness of the minimizer; vdV Thm 10.8 ("any two minimizers coincide")
    (hunique : ∀ u, u ≠ u₀ → g u₀ < g u)
    {R : ℝ}
    -- LEAN-ONLY: the ball contains the minimizer
    (hR : ‖u₀‖ < R)
    {z : ℕ → EuclideanSpace ℝ (Fin k) → ℝ≥0∞} {τ : ℕ → EuclideanSpace ℝ (Fin k)}
    {εseq δseq : ℕ → ℝ≥0∞}
    -- LEAN-ONLY: vanishing approximation tolerances
    (hε : Tendsto εseq atTop (𝓝 0)) (hδ : Tendsto δseq atTop (𝓝 0))
    -- LEAN-ONLY: the candidate minimizers stay in the ball (tightness, established upstream)
    (hτR : ∀ m, ‖τ m‖ ≤ R)
    -- LEAN-ONLY: two-sided uniform approximation of `g` on the ball
    (happrox : ∀ m, ∀ u, ‖u‖ ≤ R →
      z m u ≤ g u + δseq m ∧ g u ≤ z m u + δseq m)
    -- USER-INPUT: `τₘ` approximately minimizes `zₘ` over the ball; vdV §10.3, p. 147
    (hτ : ∀ m, ∀ u, ‖u‖ ≤ R → z m (τ m) ≤ z m u + εseq m) :
    Tendsto τ atTop (𝓝 u₀) := by
  sorry

end StatLean.Bayesian
