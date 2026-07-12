import StatLean.Bayesian.DirichletLaplace.PriorDensityBounds
import StatLean.Bayesian.DirichletLaplace.PriorSmallBall
import StatLean.Bayesian.DirichletLaplace.CoordinateSplit
import StatLean.Bayesian.ForMathlib.GammaBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dirichlet–Laplace posterior contraction — prior mass ratios (C14, BPPD Lemma 6.1)

The prior-mass bookkeeping behind BPPD **Theorem 3.1** (§6). To convert the per-shell test bounds
(`ShellDecomposition.lean`) into a summable series we need, for each net piece, the ratio

`β_{S,j,i} = Π(net piece ∩ { ∀ i ∈ S, |θᵢ| > δ }) / Π(B(θ₀, r))`

of piece mass to the mass of the contraction ball around the truth (BPPD Lemma 6.1). This file gives
the two one-sided bounds and their combination.

Objects:
* `dlPrior_ball_near_ge` — lower bound on `Π(B(θ₀, ρ))` for a truth supported on `S`:
  `exp(−(|S|log(1/a) + C|S| + (7/2)|S|^{3/4}√‖θ₀‖ + (|S|+1)log(|S|+1)))` times the centered small
  ball (BPPD Lemma 3.2(14), product density lower bound `PriorDensityBounds`, `sum_sqrt_abs_le`).
* `dlPrior_piece_le` — upper bound on the piece mass intersected with `{ ∀ i ∈ S, |θᵢ| > δ }`:
  `(17a)^{|S|}·δ^{(a−1)|S|}` times the centered ball (BPPD Lemma 3.2(13), `dlDensity_le` on the `S`
  coordinates, box-correction on the rest).
* `dlPrior_fullBall_near_truth_ge` — the `n`-dimensional lower bound feeding the denominator threshold
  `dbar` used in `Theorem31.lean` (product over the `S` and `Sᶜ` coordinates, `CoordinateSplit`).
* `dlBetaRatio_le` — the combined ratio bound: with the shape contract `δ ≥ n^{−2}`, `t ≤ 2√q log²n`,
  `r² = q log n` substituted, the exponent collapses to `|S|log(64j) + C(|S|+q)log n + C'r²`
  (BPPD Lemma 6.1). The consumer (`Theorem31.lean`) uses only the combined exponent.

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*,
JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Lemma 6.1 (p. 15); Lemma 3.2 (density bounds (13)/(14),
p. 8); the ball-volume `Γ(q/2+1)` numerics via `GammaBounds` (`ForMathlib`).

**Proof formalization notes.** The skeleton is *density bounds → ball volumes → ratio*: bound the
product DL density above/below on the relevant coordinate blocks (`PriorDensityBounds`), integrate
against Euclidean ball volumes with `Γ(q/2+1)` control (`GammaBounds`), and divide. The constants
`C, C'` below are roomy explicit placeholders (CLAUDE.md §1), tightened at proof-closure time.

**Deviations.**
* **D5 (P4 constant).** The mixture-restriction density lower bound carries exponent `−(3/√2)√|x|`,
  not the sketched `−2√|x|`; the `(7/2)|S|^{3/4}√‖θ₀‖` term above absorbs the resulting slack.
* **D6 (Lemma 3.3 without Alzer / D8 a-range).** The upper bound genuinely needs `a ≤ 1/2`
  (`Γ(1−a)` blow-up); the lower bound needs only `a ≤ 1`. Both carried explicitly here, discharged
  eventually (`aₙ → 0`) in the assembly.

**Bibliographic comments.** Prior-mass / small-ball bookkeeping in the posterior-contraction program
of Ghosal, Ghosh, and van der Vaart (*Ann. Statist.* 28 (2000), 500–531) and Castillo and van der
Vaart (*Ann. Statist.* 40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Prior small-ball lower bound near the truth** (BPPD Lemma 6.1 / Lemma 3.2(14)). For a truth
`θ₀` supported on `S`, `Π(B(θ₀, ρ))` is at least an explicit exponential factor
`exp(−(|S|log(1/a) + |S| + (7/2)|S|^{3/4}√‖θ₀‖ + (|S|+1)log(|S|+1)))` times the centered small ball
`Π(B(0, ρ))`. The `√‖θ₀‖` term is `sum_sqrt_abs_le`; the `Γ(q/2+1)` volume factor is folded into the
centered ball. -/
theorem dlPrior_ball_near_ge {a : ℝ}
    -- LEAN-ONLY: 0 < a ≤ 1 — DL scale range for the density lower bound; engine-internal.
    (ha : 0 < a) (ha1 : a ≤ 1)
    (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι)
    -- LEAN-ONLY: θ₀ supported on S — the truth's δ-support; engine-internal (`S₀` in the assembly).
    (hθ₀ : ∀ i ∉ S, θ₀ i = 0) {ρ : ℝ}
    -- LEAN-ONLY: 0 < ρ — ball radius; engine-internal.
    (hρ : 0 < ρ) :
    ENNReal.ofReal (Real.exp (- ((S.card : ℝ) * Real.log (1 / a) + (S.card : ℝ)
          + (7 / 2) * (S.card : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt ‖θ₀‖
          + ((S.card : ℝ) + 1) * Real.log ((S.card : ℝ) + 1))))
        * (dlPrior a ι) (Metric.closedBall (0 : EuclideanSpace ℝ ι) ρ)
      ≤ (dlPrior a ι) (Metric.closedBall θ₀ ρ) := by
  sorry

/-- **Net-piece prior mass upper bound** (BPPD Lemma 6.1 / Lemma 3.2(13)). The mass of a net piece
intersected with `{ ∀ i ∈ S, |θᵢ| > δ }` is at most `(17a)^{|S|}·δ^{(a−1)|S|}` (written
`exp((a−1)|S|log δ)`) times the centered ball `Π(B(0, ρ))`. The `|S|` coordinates each contribute the
density upper bound `17aδ^{a−1}` (`PriorDensityBounds`), the rest the box correction. -/
theorem dlPrior_piece_le {a δ : ℝ}
    -- LEAN-ONLY: 0 < a ≤ 1/2 — DL scale range for the density upper bound (Γ(1−a), D8); engine-internal.
    (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    -- LEAN-ONLY: 0 < δ ≤ 1 — δ-window at fixed n; engine-internal.
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (S : Finset ι) (φ : EuclideanSpace ℝ ι) {ρ : ℝ}
    -- LEAN-ONLY: 0 < ρ — piece radius; engine-internal.
    (hρ : 0 < ρ) :
    (dlPrior a ι) (Metric.closedBall φ ρ ∩ {θ | ∀ i ∈ S, δ < |θ i|})
      ≤ ENNReal.ofReal ((17 * a) ^ S.card * Real.exp ((a - 1) * (S.card : ℝ) * Real.log δ))
          * (dlPrior a ι) (Metric.closedBall (0 : EuclideanSpace ℝ ι) ρ) := by
  sorry

/-- **Full-ball prior mass lower bound near the truth** (BPPD Lemma 6.1, `n`-dimensional). The mass of
the contraction ball `B(θ₀, r)` is at least `exp(−(|S|log(1/a) + |S|log n + ‖θ₀‖² + r²))`, obtained by
factoring the prior over the support coordinates `S` and their complement (`CoordinateSplit`). This is
the `dbar`-input consumed by the denominator event in `Theorem31.lean`. -/
theorem dlPrior_fullBall_near_truth_ge {a : ℝ}
    -- LEAN-ONLY: 0 < a ≤ 1 — DL scale range; engine-internal.
    (ha : 0 < a) (ha1 : a ≤ 1)
    (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι)
    -- LEAN-ONLY: θ₀ supported on S; engine-internal.
    (hθ₀ : ∀ i ∉ S, θ₀ i = 0) {r : ℝ}
    -- LEAN-ONLY: 0 < r — ball radius; engine-internal.
    (hr : 0 < r) :
    ENNReal.ofReal (Real.exp (- ((S.card : ℝ) * Real.log (1 / a)
          + (S.card : ℝ) * Real.log (Fintype.card ι : ℝ) + ‖θ₀‖ ^ 2 + r ^ 2)))
      ≤ (dlPrior a ι) (Metric.closedBall θ₀ r) := by
  sorry

/-- **Combined prior mass ratio** (BPPD Lemma 6.1). The ratio of a net-piece mass (radius `(√5/4)jr`,
intersected with `{ ∀ i ∈ S, |θᵢ| > δ }`) to the contraction-ball mass `Π(B(θ₀, r))` is at most
`exp(|S|log(64j) + C(|S|+n)log n + C'r²)`. Under the shape contract (`δ ≥ n^{−2}`, `‖θ₀‖-derived
`t ≤ 2√q log²n`, `r² = q log n`) this collapses to `|S|log j + C(A,β)q log n` — the exponent
`Theorem31.lean` sums. Constants `C = C' = 8` are roomy placeholders (CLAUDE.md §1). -/
theorem dlBetaRatio_le {a δ : ℝ}
    -- LEAN-ONLY: 0 < a ≤ 1/2 — DL scale range (both density bounds); engine-internal.
    (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    -- LEAN-ONLY: 0 < δ ≤ 1 — δ-window at fixed n; engine-internal.
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι)
    -- LEAN-ONLY: θ₀ supported on S; engine-internal.
    (hθ₀ : ∀ i ∉ S, θ₀ i = 0) (φ : EuclideanSpace ℝ ι) {j : ℕ}
    -- LEAN-ONLY: 2 ≤ j — tested radial range; engine-internal.
    (hj : 2 ≤ j) {r : ℝ}
    -- LEAN-ONLY: 0 < r — contraction radius; engine-internal.
    (hr : 0 < r) :
    (dlPrior a ι) (Metric.closedBall φ (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ∩ {θ | ∀ i ∈ S, δ < |θ i|})
          / (dlPrior a ι) (Metric.closedBall θ₀ r)
      ≤ ENNReal.ofReal (Real.exp ((S.card : ℝ) * Real.log (64 * (j : ℝ))
            + 8 * ((S.card : ℝ) + (Fintype.card ι : ℝ)) * Real.log (Fintype.card ι : ℝ)
            + 8 * r ^ 2)) := by
  sorry

end StatLean.Bayesian
