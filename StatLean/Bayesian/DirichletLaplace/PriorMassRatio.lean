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
  -- FROZEN-FALSE (obstruction, closure session bay/dl-massratio). The DL marginal density has an
  -- integrable singularity at 0: `dlDensity(0) = +∞` and `dlDensity x ~ C|x|^{a-1}` near 0 (see the
  -- `∫ ψ^{a-2} e^{-ψ/2}` divergence behind `dlDensity_le`, whose bound `17aδ^{a-1} → ∞` as `δ→0`).
  -- Hence in dimension `d = card ι` the CENTERED ball scales as `Π(B(0,ρ)) ~ c·ρ^{d·a}` (change of
  -- variables `θ = ρu` on `∏|θⱼ|^{a-1}`), while the OFF-CENTER ball scales as
  -- `Π(B(θ₀,ρ)) ~ vol(B ρ)·f(θ₀) ~ c'·ρ^d` (density smooth & finite at `θ₀ ≠ 0`). The ratio
  -- `Π(B(θ₀,ρ)) / Π(B(0,ρ)) ~ ρ^{d(1-a)} → 0` as `ρ → 0`, but `exp(-E)` is a FIXED positive
  -- constant. Concrete counterexample: `card ι = 1`, `S = univ`, `θ₀` a unit vector (so `hθ₀`
  -- vacuous), `0 < a < 1`; then for all small `ρ` the claimed `exp(-E)·Π(B(0,ρ)) ≤ Π(B(θ₀,ρ))`
  -- fails. The statement needs a `ρ`-dependent factor (e.g. the `Γ(d/2+1)` ball-volume term dropped
  -- in this frozen restatement, cf. the richer exponent in the prompt); unprovable as written.
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
  -- DEBT (closure session bay/dl-massratio): plausibly TRUE but not closed here. This is the "safe
  -- direction": the numerator `Π(B(φ,ρ) ∩ {∀i∈S, δ<|θᵢ|})` AVOIDS the density spike at 0 on the `S`
  -- coordinates (they are bounded away from 0 by `δ`), while the denominator `Π(B(0,ρ))` KEEPS the
  -- spike — so no small-`ρ` blowup (contrast `dlPrior_ball_near_ge`). Intended route:
  --   • `CoordinateSplit.dlPrior_prod_apply`: `B(φ,ρ) ⊆ projS⁻¹(B(φ_S,ρ)) ∩ projSᶜ⁻¹(B(φ_{Sᶜ},ρ))`
  --     (L² ball projects into the block balls), factoring `Π` into an `S`- and `Sᶜ`-block;
  --   • on the `S`-block every coord has `|θᵢ|>δ`, so `dlPrior_le_of_subset` + `prod_dlDensity_le`
  --     give `≤ (17aδ^{a-1})^{|S|}·vol_S(B ρ)`;
  --   • the `Sᶜ`-block and the `vol_S` factor must recombine into `Π(B(0,ρ))`.
  -- OBSTRUCTION: the last step. `vol_S(B ρ)·Π_{Sᶜ}(B(φ_{Sᶜ},ρ))` does not cleanly reconstruct the
  -- full-space `Π(B(0,ρ))` with the TIGHT constant `(17aδ^{a-1})^{|S|}` (no spare `(64/a)^{|S|}` or
  -- `√2^{|S|}` room), and the `Sᶜ` block would need a peak-at-0 comparison `Π_{Sᶜ}(B(φ_{Sᶜ},ρ)) ≤
  -- Π_{Sᶜ}(B(0,ρ))` (rearrangement, not in Mathlib API here). Content reduces to the marginal-tail
  -- bound `ζ_δ := Π₁(|θ|>δ) ≤ 17aδ^{a-1}` (the ρ→∞ limit), which is not among the provided lemmas.
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
  -- FROZEN-FALSE (obstruction, closure session bay/dl-massratio). This is an ABSOLUTE lower
  -- bound on `Π(B(θ₀,r))` whose exponent has no term that `→ -∞` as `r → 0`. But `dlPrior` is
  -- atomless (`dlBase = volume.withDensity …`, product, pushed along the `toLp` measurable equiv),
  -- so `Π(B(θ₀,r)) → Π({θ₀}) = 0` as `r → 0⁺`. Simplest counterexample: `S = ∅` forces `θ₀ = 0`
  -- (from `hθ₀`), giving LHS `= exp(-(0 + 0 + 0 + r²)) = exp(-r²) → 1`, while
  -- RHS `= Π(B(0,r)) → 0`. So `exp(-r²) ≤ Π(B(0,r))` fails for every small `r` (any nonempty `ι`).
  -- The frozen exponent dropped the ball-volume / small-ball radius dependence present in the
  -- prompt version (`(q+1)log(q+1)`, `(√π r)^q/Γ(q/2+1)`, `2(n-q)w`); unprovable as written. Note
  -- the companion `dlPrior_ball_zero_ge` (C5) evades exactly this via its `hw2 : w ≤ 1/2` guard,
  -- unsatisfiable for small `r`; this statement carries no such guard.
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
  -- DEBT (closure session bay/dl-massratio): plausibly TRUE (a genuine `Π/Π` ratio — the radius `r`
  -- cancels, so no small-`r` blowup), but NOT closed here, and — crucially — the INTENDED ASSEMBLY
  -- IS BROKEN. The prompt directs assembling this from `dlPrior_piece_le` (numerator upper) and
  -- `dlPrior_fullBall_near_truth_ge` (denominator lower), but the latter is FROZEN-FALSE (see its
  -- comment: absolute lower bound, false as `r → 0`), and the natural alternative through
  -- `dlPrior_ball_near_ge` is ALSO FROZEN-FALSE (centered-ball spike, false as `ρ → 0`). A correct
  -- proof must route the denominator `Π(B(θ₀,r))` bound WITHOUT either false lemma — e.g. directly
  -- via `dlPrior_ball_ge_volume` (density lower bound over the off-center ball) combined with an
  -- upper bound on the numerator's centered sub-ball, so that the ball VOLUMES cancel between
  -- numerator and denominator (they share the same `Γ(q/2+1)` factor). The three sub-sorries the
  -- prompt allows (numerator-upper, denominator-lower, log-combine) collapse to two OPEN pieces:
  --   (1) numerator-upper = `dlPrior_piece_le` (itself open, see above);
  --   (2) denominator-lower = a *volume-form* lower bound on `Π(B(θ₀,r))` (NOT the false absolute
  --       `dlPrior_fullBall_near_truth_ge`), whose `(√π r)^q/Γ(q/2+1)` must cancel the numerator's.
  -- The log-combine step (pure ℝ-algebra: `Real.log_le_log`, `Real.exp_le_exp`, `S.card ≤ card ι`)
  -- is routine once (1),(2) land with a matching volume factor. Left as debt: the two false
  -- blocks make the prescribed path infeasible without an out-of-touch-set (Defs/volume) redesign.
  sorry

end StatLean.Bayesian
