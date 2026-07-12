import StatLean.Bayesian.DirichletLaplace.MarginalDensity
import StatLean.Bayesian.ForMathlib.GammaBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dirichlet–Laplace density and tail bounds (C3)

Quantitative two-sided control of the DL marginal density `dlDensity a` (from `MarginalDensity`, C2)
and of the marginal tail `ℙ_{DL,a}(|θ| > δ)`. These are BPPD **Lemma 3.2** (density bounds (13)/(14))
and **Lemma 3.3** (tail bound), the analytic core consumed by the product-density estimates
(`PriorDensityBounds`, C4), the support-count Chernoff bound (`PriorSmallBall`, C5), and Lemma 6.1
(`PriorMassRatio`, C14).

Results:
* **P3** `dlDensity_le` — upper bound `f_{DL,a}(x) ≤ 17·a·δ^{a-1}` for `δ ≤ |x|` (BPPD eq. (13)).
* **P4** `dlDensity_ge_of_one_le` / `dlDensity_ge` — lower bounds `f_{DL,a}(x) ≥ (a/64)·|x|^{-1/2}
  e^{-3√|x|}` (`|x| ≥ 1`) and the uniform log-linear form `≥ (a/64) e^{-3-(7/2)√|x|}` (BPPD eq. (14)).
* **P5** `dlMarginal_abs_gt_le` (+ `dlMarginal_abs_gt_le'`, `dlMarginal_abs_le_ge`) — the tail bound
  `ℙ_{DL,a}(|θ| > δ) ≤ (8 + 2 log(1/δ))/Γ(a)`, its `ζ`-form `≤ e·a·(8 + 2 log(1/δ))`, and the
  complementary box-mass lower bound (BPPD Lemma 3.3).

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Lemma 3.2 (eq. (13)/(14)),
Lemma 3.3.

**Proof formalization notes.**
* **P3** (`dlDensity_le`): on the real integral form (C2, `dlDensity_eq_ofReal_integral`), substitute
  `u = |x|/ψ` and bound `∫ u^{-a} e^{-u} du` on `(0, |x|/… )`; combine with `dlNormConst_le` (C2).
  Deviation **D8**: the upper bound genuinely needs `a ≤ 1/2` — the small-`ψ` tail of the mixture
  produces a `Γ(1-a)` factor that blows up as `a → 1⁻`, so the paper's `a ≤ 1` is insufficient for a
  clean constant. `17` is a roomy explicit numeral, not the paper's unspecified constant.
* **P4** (`dlDensity_ge_of_one_le`, `dlDensity_ge`): restrict the mixture integral to
  `ψ ∈ [√(2|x|), 2√(2|x|)]` and bound both densities below there; combine with `dlNormConst_ge` (C2).
  Deviation **D5**: this restriction yields the exponent `-(3/√2)√|x|`, rounded up to `-3√|x|` (the
  paper sketches `-2√|x|`, which the restriction cannot deliver). The uniform log-linear form
  absorbs the algebraic factor via `|x|^{-1/2} e^{-3√|x|} ≥ e^{-3-(7/2)√|x|}` and is extended to
  `|x| < 1` by monotonicity (P2). Lower bounds need only `a ≤ 1` (contrast D8). `a/64` is roomy.
* **P5** (`dlMarginal_abs_gt_le`): from `dlMarginal_abs_gt_eq_mixture` (C2), split the `Gamma`-mixture
  tail `∫ e^{-δ/ψ} dGamma_{a,1/2}` at `ψ = 4δ`. Deviation **D6**: proved *without* Alzer's
  inequality — the small part (`ψ ≤ 4δ`) is `≤ 4` via `e^{-u} ≤ u^{-(1-a)}`, the large part
  (`ψ > 4δ`) is `≤ C + 2 log(1/δ)` via `ψ^{a-1} ≤ max(ψ^{-1}, 1)`; holds for all `δ ∈ (0,1)` (no
  "`δ` small"). `Γ` numerics go through `Γ(1+a) ∈ [e^{-1}, 2]` (F2), *not* the paper's "`Γ(x) ≥ 1/x`"
  (false as stated). The `ζ`-form uses `1/Γ(a) ≤ e·a` (`inv_e_mul_le_Gamma`, F2); the complement is
  `1 − (tail)` via `IsProbabilityMeasure`.

**Bibliographic comments.** Sharp tail and density estimates of this kind are the technical engine of
Bayesian posterior-contraction theory in the framework of Ghosal–Ghosh–van der Vaart (*Ann.
Statist.* 28 (2000), 500–531) and Castillo–van der Vaart (*Ann. Statist.* 40 (2012), 2069–2101);
here they quantify how the Dirichlet–Laplace marginal simultaneously concentrates near the origin
(box-mass lower bound) and retains heavy enough tails (`ℙ(|θ| > δ)` upper bound) to recover sparse
signals.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

variable {a δ : ℝ}

/-! ### P3 — density upper bound (BPPD Lemma 3.2, eq. (13)) -/

/-- **P3 / Lemma 3.2 upper bound (BPPD eq. (13)).** For a threshold `0 < δ ≤ 1` and any point with
`δ ≤ |x|`, the DL marginal density satisfies `f_{DL,a}(x) ≤ 17 · a · δ^{a-1}`.

Deviation **D8**: the bound needs `a ≤ 1/2` (the `Γ(1-a)` factor from the small-`ψ` tail blows up as
`a → 1⁻`; the paper's `a ≤ 1` is not enough). Lower bounds P4 need only `a ≤ 1`. The prefactor `17`
is a roomy explicit numeral. -/
lemma dlDensity_le
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1 (Lemma 3.2)
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1/2 (D8: Γ(1-a) control in the density upper bound); BPPD §3.1 (Lemma 3.2)
    (ha1 : a ≤ 1 / 2)
    -- USER-INPUT: positive threshold; BPPD §3.1 (Lemma 3.2)
    (hδ : 0 < δ)
    -- USER-INPUT: threshold ≤ 1; BPPD §3.1 (Lemma 3.2)
    (hδ1 : δ ≤ 1)
    -- USER-INPUT: point outside the δ-window; BPPD §3.1 (Lemma 3.2)
    {x : ℝ} (hx : δ ≤ |x|) :
    dlDensity a x ≤ ENNReal.ofReal (17 * a * δ ^ (a - 1)) := by
  sorry

/-! ### P4 — density lower bounds (BPPD Lemma 3.2, eq. (14); deviation D5) -/

/-- **P4 / Lemma 3.2 lower bound (BPPD eq. (14)), large-`|x|` form.** For `1 ≤ |x|`,
`f_{DL,a}(x) ≥ (a/64) · |x|^{-1/2} · e^{-3√|x|}`.

Deviation **D5**: restricting the mixture to `ψ ∈ [√(2|x|), 2√(2|x|)]` produces the exponent
`-(3/√2)√|x|`, rounded up to `-3√|x|` (the paper sketches `-2√|x|`, unattainable by this
restriction). `a/64` is a roomy explicit constant; lower bounds need only `a ≤ 1` (contrast D8). -/
lemma dlDensity_ge_of_one_le
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1 (Lemma 3.2)
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1 (lower-bound regime; cf. D8); BPPD §3.1 (Lemma 3.2)
    (ha1 : a ≤ 1)
    -- USER-INPUT: point with |x| ≥ 1; BPPD §3.1 (Lemma 3.2)
    {x : ℝ} (hx : 1 ≤ |x|) :
    ENNReal.ofReal ((a / 64) * |x| ^ (-(1 / 2) : ℝ) * Real.exp (-3 * Real.sqrt |x|))
      ≤ dlDensity a x := by
  sorry

/-- **P4 / Lemma 3.2 lower bound, uniform log-linear form (deviation D5).** Absorbing `|x|^{-1/2}`
into the exponential (`|x|^{-1/2} e^{-3√|x|} ≥ e^{-3-(7/2)√|x|}`) gives a bound with a purely
`√|x|`-linear exponent, valid for **every** `x` (the `|x| < 1` range via monotonicity P2):
`f_{DL,a}(x) ≥ (a/64) · e^{-3 - (7/2)√|x|}`. This is the form consumed by the prior small-ball and
Lemma 6.1 mass estimates (C5, C14). -/
lemma dlDensity_ge
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1 (Lemma 3.2)
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1 (lower-bound regime); BPPD §3.1 (Lemma 3.2)
    (ha1 : a ≤ 1) (x : ℝ) :
    ENNReal.ofReal ((a / 64) * Real.exp (-3 - (7 / 2) * Real.sqrt |x|)) ≤ dlDensity a x := by
  sorry

/-! ### P5 — marginal tail bound (BPPD Lemma 3.3; deviation D6) -/

/-- **P5 / Lemma 3.3 (BPPD tail bound).** The DL marginal tail obeys
`ℙ_{DL,a}(|θ| > δ) ≤ (8 + 2 log(1/δ)) / Γ(a)` for every `0 < a ≤ 1`, `0 < δ < 1`.

Deviation **D6**: proved *without* Alzer's inequality. Split the `Gamma`-mixture tail
`∫ e^{-δ/ψ} dGamma_{a,1/2}` at `ψ = 4δ`: the small part is `≤ 4` via `e^{-u} ≤ u^{-(1-a)}`, the large
part is `≤ C + 2 log(1/δ)` via `ψ^{a-1} ≤ max(ψ^{-1}, 1)`. Holds for all `δ ∈ (0,1)` (no "`δ`
small"). `Γ` numerics use `Γ(1+a) ∈ [e^{-1}, 2]` (F2), not the paper's false "`Γ(x) ≥ 1/x`". -/
lemma dlMarginal_abs_gt_le
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1 (Lemma 3.3)
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1; BPPD §3.1 (Lemma 3.3)
    (ha1 : a ≤ 1)
    -- USER-INPUT: positive threshold; BPPD §3.1 (Lemma 3.3)
    (hδ : 0 < δ)
    -- USER-INPUT: threshold < 1; BPPD §3.1 (Lemma 3.3)
    (hδ1 : δ < 1) :
    dlMarginal a {x | δ < |x|}
      ≤ ENNReal.ofReal ((8 + 2 * Real.log (1 / δ)) / Real.Gamma a) := by
  sorry

/-- **P5 / Lemma 3.3, `ζ`-form.** Bounding `1/Γ(a) ≤ e·a` (`inv_e_mul_le_Gamma`, F2) turns the tail
bound into `ζ(δ) := ℙ_{DL,a}(|θ| > δ) ≤ e·a·(8 + 2 log(1/δ))` — the estimate consumed by the
support-count Chernoff bound (C5) and the reduction of Theorem 3.4 (C15). -/
lemma dlMarginal_abs_gt_le'
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1 (Lemma 3.3)
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1; BPPD §3.1 (Lemma 3.3)
    (ha1 : a ≤ 1)
    -- USER-INPUT: positive threshold; BPPD §3.1 (Lemma 3.3)
    (hδ : 0 < δ)
    -- USER-INPUT: threshold < 1; BPPD §3.1 (Lemma 3.3)
    (hδ1 : δ < 1) :
    dlMarginal a {x | δ < |x|}
      ≤ ENNReal.ofReal (Real.exp 1 * a * (8 + 2 * Real.log (1 / δ))) := by
  sorry

/-- **P5 / Lemma 3.3, complement (box-mass lower bound).** The DL marginal puts most of its mass in
`[-δ, δ]`: `ℙ_{DL,a}(|θ| ≤ δ) ≥ 1 - e·a·(8 + 2 log(1/δ))`. Complement of `dlMarginal_abs_gt_le'` via
`IsProbabilityMeasure`; feeds the `ℙ(|θ₁| < δ)^{q-|S|}` box correction of Lemma 6.1 (C14). -/
lemma dlMarginal_abs_le_ge
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1 (Lemma 3.3)
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1; BPPD §3.1 (Lemma 3.3)
    (ha1 : a ≤ 1)
    -- USER-INPUT: positive threshold; BPPD §3.1 (Lemma 3.3)
    (hδ : 0 < δ)
    -- USER-INPUT: threshold < 1; BPPD §3.1 (Lemma 3.3)
    (hδ1 : δ < 1) :
    1 - ENNReal.ofReal (Real.exp 1 * a * (8 + 2 * Real.log (1 / δ)))
      ≤ dlMarginal a {x | |x| ≤ δ} := by
  sorry

end StatLean.Bayesian
