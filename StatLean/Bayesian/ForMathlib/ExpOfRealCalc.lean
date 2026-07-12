import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# `ENNReal`-valued exponential calculus and a Gaussian-type series bound

Elementary `ℝ≥0∞` book-keeping for the term `ENNReal.ofReal (Real.exp ·)` —
positivity, finiteness, monotonicity, the additive law for products, and division
by an exponential — together with the two analytic facts the DL series endgame
needs:

* `tsum_ofReal_exp_neg_sq_le` — a Gaussian-type tail series
  `∑_{j≥0} exp(−c(M+j)²K)` is dominated by twice its first term, once the first
  inter-term gap forces the ratio below `1/2`.
* `tendsto_ofReal_exp_neg` — `ofReal (exp (−εₙ)) → 0` whenever `εₙ → ∞`.

**Reference.** Mathlib-level bricks (no book statement of their own) consumed by the
Dirichlet–Laplace posterior-contraction proof (Bhattacharya–Pati–Pillai–Dunson,
*Dirichlet–Laplace priors for optimal shrinkage*, JASA 2015 / arXiv:1401.5398;
tag `BPPD §X.Y`): they carry the `ℝ≥0∞` ratio algebra and the shell-sum bookkeeping
`∑_S ∑_{j≥M} ∑_i (1+β) exp(−j²r²/12) → 0` of Theorems 3.1 / 3.4 (§6).

**Proof formalization notes.** The five algebra lemmas are short consequences of
`ENNReal.ofReal_mul` / `ENNReal.ofReal_lt_top` / `ENNReal.ofReal_le_ofReal_iff`
together with `Real.exp_add` / `Real.exp_pos`; `tsum_ofReal_exp_neg_sq_le`
geometric-dominates the summand by comparing consecutive terms — the gap
`(M+j+1)² − (M+j)² ≥ 2M+1` gives ratio `≤ exp(−cK(2M+1)) ≤ 1/2` — and sums the
resulting geometric series (`ENNReal.tsum_geometric`); `tendsto_ofReal_exp_neg`
composes `Real.tendsto_exp_atBot` with the continuity of `ENNReal.ofReal` at `0`.

**Bibliographic comments.** Geometric domination of a Gaussian tail sum by its
leading term is standard elementary analysis.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- `ENNReal.ofReal (Real.exp x)` is strictly positive (the exponential is). -/
lemma ofReal_exp_pos (x : ℝ) : 0 < ENNReal.ofReal (Real.exp x) := by
  sorry

/-- `ENNReal.ofReal (Real.exp x)` is finite (it is the image of a real under
`ENNReal.ofReal`). -/
lemma ofReal_exp_ne_top (x : ℝ) : ENNReal.ofReal (Real.exp x) ≠ ⊤ := by
  sorry

/-- Monotonicity transfer: `ofReal (exp x) ≤ ofReal (exp y) ↔ x ≤ y` (exponentials
are positive, so `ENNReal.ofReal` neither clamps nor loses order). -/
lemma ofReal_exp_le_iff (x y : ℝ) :
    ENNReal.ofReal (Real.exp x) ≤ ENNReal.ofReal (Real.exp y) ↔ x ≤ y := by
  sorry

/-- The additive law for a product of exponentials in `ℝ≥0∞`:
`ofReal (exp x) * ofReal (exp y) = ofReal (exp (x + y))`. -/
lemma ofReal_exp_mul (x y : ℝ) :
    ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (Real.exp y)
      = ENNReal.ofReal (Real.exp (x + y)) := by
  sorry

/-- Division by an exponential is multiplication by its reciprocal exponential:
`a / ofReal (exp x) = a * ofReal (exp (−x))`. -/
lemma div_ofReal_exp_neg (a : ℝ≥0∞) (x : ℝ) :
    a / ENNReal.ofReal (Real.exp x) = a * ENNReal.ofReal (Real.exp (-x)) := by
  sorry

/-- **Gaussian-type tail series, dominated by twice its leading term.** For
`c, K` with positive curvature `c` and the first inter-term gap large enough
(`1 ≤ c(2M+1)K`, forcing the consecutive ratio below `1/2`),
`∑_{j≥0} exp(−c(M+j)²K) ≤ 2 · exp(−cM²K)`. -/
theorem tsum_ofReal_exp_neg_sq_le (c K : ℝ) (M : ℕ)
    -- LEAN-ONLY: positive curvature so the summand decays; genuine caller input
    (hc : 0 < c)
    -- LEAN-ONLY: first gap forces the consecutive ratio ≤ 1/2 (geometric domination); caller input
    (h : 1 ≤ c * (2 * M + 1) * K) :
    (∑' j : ℕ, ENNReal.ofReal (Real.exp (-c * ((M + j : ℕ) : ℝ) ^ 2 * K)))
      ≤ 2 * ENNReal.ofReal (Real.exp (-c * (M : ℝ) ^ 2 * K)) := by
  sorry

/-- **Series endgame.** If the real exponent diverges (`εₙ → ∞`) then
`ofReal (exp (−εₙ)) → 0` in `ℝ≥0∞`. -/
theorem tendsto_ofReal_exp_neg {ε : ℕ → ℝ}
    -- LEAN-ONLY: the exponent diverges (drives the contraction to 0); genuine caller input
    (h : Filter.Tendsto ε Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => ENNReal.ofReal (Real.exp (-(ε n))))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  sorry

end StatLean.Bayesian
