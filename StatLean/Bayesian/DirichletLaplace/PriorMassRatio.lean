import StatLean.Bayesian.DirichletLaplace.PriorDensityBounds
import StatLean.Bayesian.DirichletLaplace.PriorSmallBall
import StatLean.Bayesian.DirichletLaplace.CoordinateSplit
import StatLean.Bayesian.ForMathlib.GammaBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dirichlet–Laplace posterior contraction — prior mass ratio (C14, BPPD Lemma 6.1)

The prior-mass bookkeeping behind BPPD **Theorem 3.1** (§6). To convert the per-shell test bounds
(`ShellDecomposition.lean`) into a summable series we need, for each net piece, the ratio

`β_{S,j} = Π(net piece ∩ { ∀ i ∈ S, |θᵢ| > δ }) / Π(B(θ₀, r))`

of piece mass to the mass of the contraction ball around the truth (BPPD Lemma 6.1). This file gives
the single consumer-facing bound `dlBetaRatio_le` on that ratio.

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*,
JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Lemma 6.1 (p. 15); Lemma 3.2 (density bounds (13)/(14),
p. 8).

## Formalization notes — corrected statement (D10, D11) and what the paper elides

The stub for this file originally carried FOUR lemmas, two of which (`dlPrior_ball_near_ge`,
`dlPrior_fullBall_near_truth_ge`) were **false as stated** and have been removed; a third
(`dlPrior_piece_le`) was an awkward intermediate folded into the proof of `dlBetaRatio_le`. The reasons,
and the corrected route, are the substance of this milestone:

* **D10 (no absolute lower bound on `Π(B(θ₀,r))`; the ratio is what matters).** The removed
  `dlPrior_fullBall_near_truth_ge` claimed `Π(B(θ₀,r)) ≥ exp(−E)` with `E` free of any `r → 0` blow-up
  term. That is false: `dlPrior` is atomless, so `Π(B(θ₀,r)) → 0` as `r → 0` while `exp(−E)` is a fixed
  positive constant (take `S = ∅`, forcing `θ₀ = 0`: the claim becomes `exp(−r²) ≤ Π(B(0,r))`, false for
  small `r`). It was believed to feed the denominator threshold `dbar`, but the assembly (`Theorem31`)
  never needs an *absolute* denominator bound: with `dbar = e^{−r²}·Π(B(θ₀,r))` the shell contribution
  `Π(shell)·e^{−j²r²/12}/dbar = [Π(shell)/Π(B(θ₀,r))]·e^{−j²r²/12}·e^{r²}` has `Π(B(θ₀,r))` **cancel**
  into the ratio `β`. Only `dlBetaRatio_le` (a genuine `Π/Π`, with `r` cancelling) is consumed — no
  absolute ball-mass bound exists or is needed. Likewise the removed `dlPrior_ball_near_ge` (a
  centered-vs-offset ball comparison) was false for the same atomless/spike reason and unused.

* **D11 (the exponent depends on `‖θ₀‖`; the paper's Lemma 6.1 hides it in a constant).** The stub's
  exponent `|S|log(64j) + C(|S|+n)log n + C'r²` **omits any dependence on the truth `θ₀`**, which is
  incorrect: the denominator ball `B(θ₀,r)` charges less mass the larger `‖θ₀‖` is (the DL density
  decays like `exp(−(7/2)Σ√|θᵢ|)`, Lemma 3.2(14)), so `β` genuinely grows with `‖θ₀‖`. The honest
  exponent (below) carries a `|S|^{3/4}√‖θ₀‖` term. It is harmless in the assembly precisely because of
  Theorem 3.1's hypothesis `‖θ₀‖² ≤ q log⁴n`: then `|S|^{3/4}√‖θ₀‖ ≤ (A'q)^{3/4}(q log⁴n)^{1/4} =
  O(q log n) = O(r²)`, dominated by the shell decay. This is the role of `hnorm` in the paper's proof,
  left implicit there.

**Corrected route (block factorization, volume cancellation).** `β = Π(piece)/Π(B(θ₀,r))`. Factor both
over the support block `S` and its complement `Sᶜ` (`CoordinateSplit`), using
`B(θ₀,r) ⊇ B_S(θ₀_S, r/√2) × B_{Sᶜ}(0, r/√2)`:
* **`S`-block (|S| dims):** numerator `≤ (17aδ^{a−1})^{|S|}·vol_S(B_ρ)` (density upper on `{δ<|θ|}`,
  `PriorDensityBounds`), denominator `≥ exp(−[|S|log(1/a)+C|S|+(7/2)Σ√|θᵢ|])·vol_S(B_{r/√2})`
  (density lower, Lemma 3.2(14)). The Euclidean ball volumes share the `Γ(|S|/2+1)` factor, which
  **cancels**, leaving the radius ratio `(√2ρ/r)^{|S|} = (√10/4·j)^{|S|}`. The `a`-powers cancel
  (`17a·(1/a) = 17`). `Σ_{i∈S}√|θᵢ|` over the ball is controlled by Cauchy–Schwarz twice:
  `Σ√|θᵢ| ≤ |S|^{3/4}(‖θ₀‖+r)^{1/2} ≤ |S|^{3/4}(√‖θ₀‖+√r)` — the `√r` piece is `|S|^{3/4}√r = o(r²)`.
* **`Sᶜ`-block (card ι − |S| dims):** numerator `≤ 1` (probability), denominator
  `≥ exp(−2(card ι)w)` (`PriorSmallBall.dlPrior_ball_zero_ge` on the `Sᶜ` subtype), `w` a tail bound at
  the clamped radius. Under `a = n^{−(1+β)}` this term `→ 0`.

**Constants deviate from the paper (charter §1).** The radius-ratio constant is stated as `512` (roomy
for `√10/4·17·e^C`); the `4, 4, 2` multipliers are generous placeholders. A closure session **may
adjust these numerals and the precise form of the lower-order terms** to whatever the block bounds
actually deliver, provided the exponent keeps the shape `|S|·log(c·j) + (terms that Theorem31 bounds by
O(r²) or o(r²) or →0 under a=n^{−(1+β)}, δ≥n^{−2}, ‖θ₀‖²≤q log⁴n)`; report the final exponent so the
`Theorem31` assembly can sum it.

**Deviations (density bounds).** D5 (P4 exponent `−(3/√2)√|x|`, absorbed by the `4·|S|^{3/4}√‖θ₀‖`
slack); D8 (`a ≤ 1/2` for the density upper bound, `a ≤ 1` for the lower — both carried, discharged
`aₙ → 0` in the assembly).

**Bibliographic comments.** Prior-mass / small-ball bookkeeping in the posterior-contraction program
of Ghosal, Ghosh, and van der Vaart (*Ann. Statist.* 28 (2000), 500–531) and Castillo and van der
Vaart (*Ann. Statist.* 40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Combined prior mass ratio** (BPPD Lemma 6.1, corrected — see the file header D10/D11). The ratio
of a net-piece mass (radius `ρ = (√5/4)jr`, intersected with `{ ∀ i ∈ S, |θᵢ| > δ }`) to the
contraction-ball mass `Π(B(θ₀, r))` is at most `exp` of

`|S|·log(512 j) + |S|·log(1/δ) + 4|S|^{3/4}(√‖θ₀‖ + √r) + 2·(card ι)·w`,

where `w` bounds the `Sᶜ`-block coordinate tail at the clamped denominator radius (mirroring
`PriorSmallBall.dlPrior_ball_zero_ge`; the assembly `Theorem31` supplies `w` via the `C3` marginal-tail
bound and checks `w ≤ 1/2`). The radius `r` cancels between numerator and denominator (both carry the
same `Γ(|S|/2+1)` ball volume), so unlike the removed absolute bounds this ratio has no `r → 0`
pathology. Under the shape contract (`a = n^{−(1+β)}`, `δ ≥ n^{−2}`, `‖θ₀‖² ≤ q log⁴n`, `r² = q log n`)
every non-`j` term is `O(r²)`, `o(r²)`, or `→ 0`, and `|S|·log(512j)` sums against the shell decay
`e^{−j²r²/12}` — this is the exponent `Theorem31.lean` sums. Constants are roomy placeholders adjustable
at proof-closure (charter §1). -/
theorem dlBetaRatio_le {a δ : ℝ}
    -- LEAN-ONLY: 0 < a ≤ 1/2 — DL scale range (both density bounds); engine-internal (BPPD Lemma 6.1).
    (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    -- LEAN-ONLY: 0 < δ ≤ 1 — δ-window at fixed n; engine-internal.
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι)
    -- LEAN-ONLY: θ₀ supported on S — the truth's δ-support; engine-internal (`S₀` in the assembly).
    (hθ₀ : ∀ i ∉ S, θ₀ i = 0) (φ : EuclideanSpace ℝ ι) {j : ℕ}
    -- LEAN-ONLY: 2 ≤ j — tested radial range; engine-internal.
    (hj : 2 ≤ j) {r : ℝ}
    -- LEAN-ONLY: 0 < r — contraction radius; engine-internal.
    (hr : 0 < r)
    -- USER-INPUT: `w` bounds the `Sᶜ`-block coordinate tail at the clamped denominator radius `r/√2`
    -- (mirrors `dlPrior_ball_zero_ge`'s interface; `Theorem31` discharges it via C3). BPPD Lemma 6.1.
    (w : ℝ)
    (hw : (dlMarginal a {x : ℝ |
        min (r / Real.sqrt 2 / Real.sqrt (Fintype.card ι : ℝ)) (1 / 2) < |x|}).toReal ≤ w)
    -- USER-INPUT: `w ≤ 1/2` — unlocks the `Sᶜ` small-ball bound (deviation D7; `aₙ → 0` gives it).
    (hw2 : w ≤ 1 / 2) :
    (dlPrior a ι) (Metric.closedBall φ (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ∩ {θ | ∀ i ∈ S, δ < |θ i|})
          / (dlPrior a ι) (Metric.closedBall θ₀ r)
      ≤ ENNReal.ofReal (Real.exp (
            (S.card : ℝ) * Real.log (512 * (j : ℝ))
          + (S.card : ℝ) * Real.log (1 / δ)
          + 4 * (S.card : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt ‖θ₀‖
          + 4 * (S.card : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r
          + 2 * (Fintype.card ι : ℝ) * w)) := by
  -- PROOF RECIPE (corrected route; the two false absolute lemmas are gone — see file header D10/D11).
  --
  -- Write `ρ := (√5/4)·jr` (numerator radius). Factor the L² ball `B(θ₀,r) ⊇ B_S(θ₀_S, r/√2) ×
  -- B_{Sᶜ}(0, r/√2)` and both measures over `S ⊔ Sᶜ` via `CoordinateSplit.dlPrior_prod_apply`:
  --   `Π(piece ∩ {δ<|θ_S|}) = Π_S(B_S(φ_S,ρ) ∩ {δ<|θ|}) · Π_{Sᶜ}(B_{Sᶜ}(φ_{Sᶜ},ρ))`,
  --   `Π(B(θ₀,r))          ≥ Π_S(B_S(θ₀_S, r/√2))       · Π_{Sᶜ}(B_{Sᶜ}(0, r/√2))`.
  -- Then `β ≤ [S-ratio] · [Sᶜ-ratio]`.
  --
  -- S-BLOCK (|S| dims; `PriorDensityBounds`, `EuclideanSpace.volume_closedBall`):
  --   • numerator `≤ (17a·δ^{a−1})^{|S|} · vol_S(B_ρ)`  (density upper, coords `>δ`);
  --   • denominator `≥ exp(−[|S|log(1/a) + C|S| + (7/2)·Σ_{i∈S}√|θᵢ|]) · vol_S(B_{r/√2})`
  --       (`prod_dlDensity_ge`, Lemma 3.2(14)); over the ball `Σ√|θᵢ| ≤ |S|^{3/4}(‖θ₀‖+r)^{1/2}
  --       ≤ |S|^{3/4}(√‖θ₀‖ + √r)` (Cauchy–Schwarz twice + `Real.sqrt_add_le`);
  --   • the `Γ(|S|/2+1)` in both volumes cancels ⇒ `vol_S(B_ρ)/vol_S(B_{r/√2}) = (√2ρ/r)^{|S|} =
  --       (√10/4·j)^{|S|}`; the `a`-powers cancel (`17a/a = 17`) ⇒
  --       `S-ratio ≤ exp(|S|log(17·√10/4·e^C·j) + (1−a)|S|log(1/δ) + (7/2)|S|^{3/4}(√‖θ₀‖+√r))`
  --       `                 ≤ exp(|S|log(512 j) + |S|log(1/δ) + 4|S|^{3/4}(√‖θ₀‖+√r))`.
  -- Sᶜ-BLOCK (card ι − |S| dims): numerator `≤ 1`; denominator `≥ exp(−2(card ι)w)` by
  --   `dlPrior_ball_zero_ge` on the `{i // i ∉ S}` subtype (hw, hw2) ⇒ `Sᶜ-ratio ≤ exp(2(card ι)w)`.
  -- Multiply (add exponents), `Real.exp_le_exp` + `ENNReal.ofReal` monotone. ∎
  --
  -- A closure session MAY tune the numeric constants (512, 4, 4, 2) to whatever the block bounds
  -- deliver, keeping the shape; report the final exponent for the `Theorem31` summation.
  sorry

end StatLean.Bayesian
