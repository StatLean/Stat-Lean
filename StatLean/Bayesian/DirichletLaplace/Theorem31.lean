import StatLean.Bayesian.DirichletLaplace.ShellDecomposition
import StatLean.Bayesian.DirichletLaplace.PriorMassRatio
import StatLean.Bayesian.DirichletLaplace.Theorem34
import StatLean.Bayesian.DirichletLaplace.DenominatorLowerBound
import StatLean.Bayesian.DirichletLaplace.TestingBound
import StatLean.Bayesian.ForMathlib.ExpOfRealCalc
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dirichlet–Laplace posterior contraction — BPPD Theorem 3.1 (C16)

Assembly of BPPD **Theorem 3.1**: in the normal-means model `y = θ + ε`, `ε ~ N(0, Iₙ)`, under the
Dirichlet–Laplace prior with scale `aₙ = n^{−(1+β)}` and the growth condition `‖θ₀‖² ≤ qₙ log⁴n`, the
posterior mass of `{ ‖θ − θ₀‖ > M√(qₙ log n) }` tends to `0` in `E_{θ₀}`.

Objects:
* `dl_contraction_engine` — the fixed-`n` bound assembled from three vanishing pieces: the Theorem 3.4
  compressibility term at `δ = r/n` (`Theorem34`), the denominator event on the full model at radius
  `2r` (`DenominatorLowerBound` + `PriorMassRatio.dlPrior_fullBall_near_truth_ge`), and the summed
  shell/net bound (`ShellDecomposition` per shell, `PriorMassRatio.dlBetaRatio_le` per piece).
* `dl_theorem31` — the headline (rate `M√(qₙ log n)`, deviation D1).
* `dl_theorem31_ball` — the equivalent `𝓝 1` form (posterior mass of the ball `{‖θ − θ₀‖ ≤ M√(qₙ log
  n)}` tends to `1`; BPPD eq. (12)).
* `dl_theorem31_paper_rate` — under `qₙ ≤ n^{1−c}`, the paper's minimax rate `sₙ = √(qₙ log(n/qₙ))`.
* `dl_theorem31_recip` — the `aₙ = 1/n` companion under `qₙ ≥ C₀ log n`.

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*,
JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Theorem 3.1 (statement p. 7, proof §6 pp. 14–16 with
Lemma 6.1); the §6 posterior-contraction assembly.

**Proof formalization notes.** The skeleton is *3.4-term + denominator event + Σ-shells*: split the
complement of the ball into radial shells (`ShellDecomposition`), cover each by a net and test it,
weight the Type II errors by the piece prior-mass ratio (`PriorMassRatio.dlBetaRatio_le`), and sum.
The outer support-pattern sum is `|{ |S| ≤ A'q }| ≤ (A'q+1)·n^{A'q}` via `Nat.choose_le_pow`
(`Mathlib.Data.Nat.Choose.Bounds`); the radial series `Σ_{j ≥ M} (1+β)e^{−j²r²/12} → 0` via
`ExpOfRealCalc` (`tsum_ofReal_exp_neg_sq_le`, `tendsto_ofReal_exp_neg`). The asymptotics live only in
the thin corollaries.

**Deviations.**
* **D1 (rate).** The paper states `sₙ² = qₙ log(n/qₙ)` but its proof fixes `rₙ² = qₙ log n` (p. 15) and
  only yields that. The headline `dl_theorem31` therefore states the rate `√(qₙ log n)`; the paper's
  `sₙ` is recovered as `dl_theorem31_paper_rate` under `qₙ ≤ n^{1−c}` (where `log(n/qₙ) ≍ log n`).
* **D2 (regime-dependent `r`).** `β`-regime uses `r² = qₙ log n`; `1/n`-regime (`dl_theorem31_recip`)
  uses `r² = qₙ` and needs `qₙ ≥ C₀ log n`. Same free-`r` engine, two instantiations.
* **D4 (net / test geometry).** Inherited from `ShellDecomposition`: `jr/4`-nets (`≤ 33^{|S|}`),
  pieces of radius `≤ (√5/4)jr`, two-parameter midpoint tests with errors `≤ e^{−j²r²/12}`.

**Bibliographic comments.** Posterior contraction rates after Ghosal, Ghosh, and van der Vaart
(*Ann. Statist.* 28 (2000), 500–531); sparse-normal-means Bayesian contraction after Castillo and van
der Vaart (*Ann. Statist.* 40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

/-- **Fixed-`n` contraction bound** (BPPD Thm 3.1 engine). For a `q`-sparse truth `θ₀`, the
`E_{θ₀}`-mean of the posterior mass of `{ ‖θ − θ₀‖ > M·r }` is bounded by three vanishing pieces: the
denominator event `e^{−r²/8}`, the Theorem 3.4 compressibility term at `δ = r/n`, and the summed shell
series `2·e^{−M²r²/12}` (`ShellDecomposition` + `PriorMassRatio`, `ExpOfRealCalc`). -/
theorem dl_contraction_engine {ι : Type*} [Fintype ι] {a r : ℝ}
    -- LEAN-ONLY: 0 < a ≤ 1/2 — DL scale range (both density bounds); engine-internal.
    (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    -- LEAN-ONLY: 0 < r — contraction radius (rₙ); engine-internal.
    (hr : 0 < r) (θ₀ : EuclideanSpace ℝ ι) {q : ℕ}
    -- LEAN-ONLY: θ₀ q-sparse; engine-internal.
    (hq : (Finset.univ.filter fun i => θ₀ i ≠ 0).card ≤ q)
    -- LEAN-ONLY: 0 < M — contraction multiplier; engine-internal.
    (M : ℝ) (hM : 0 < M)
    -- LEAN-ONLY: 0 < A — compressibility multiplier for the 3.4-term; engine-internal.
    (A : ℝ) (hA : 0 < A)
    -- LEAN-ONLY: 1 < c — Chernoff parameter; engine-internal.
    (c : ℝ) (hc : 1 < c) :
    ∫⁻ y, ((gaussShiftKernel ι)†(dlPrior a ι)) y {θ | M * r < ‖θ - θ₀‖}
          ∂(gaussShiftKernel ι θ₀)
      ≤ ENNReal.ofReal (Real.exp (- r ^ 2 / 8))
          + ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ)
                * (Real.exp 1 * a * (8 + 2 * Real.log ((Fintype.card ι : ℝ) / r))) * (c - 1)
                - (A - 1) * (q : ℝ) * Real.log c + 3 * r ^ 2))
          + 2 * ENNReal.ofReal (Real.exp (- M ^ 2 * r ^ 2 / 12)) := by
  sorry

/-- **BPPD Theorem 3.1 (posterior contraction).** In the normal-means model with the Dirichlet–Laplace
prior at scale `aₙ = n^{−(1+β)}`, under the growth condition `‖θ₀‖² ≤ qₙ log⁴n`, there is a constant
`M > 0` such that the posterior mass of `{ θ : ‖θ − θ₀‖ > M√(qₙ log n) }` tends to `0` in `E_{θ₀}`.

**Deviation D1 (rate).** The stated rate is `√(qₙ log n)`, which is what the paper's proof (`rₙ² = qₙ
log n`, p. 15) yields; the paper's headline `sₙ = √(qₙ log(n/qₙ))` is recovered under `qₙ ≤ n^{1−c}` in
`dl_theorem31_paper_rate`. -/
theorem dl_theorem31 {β : ℝ}
    -- USER-INPUT: β > 0 (DL scale exponent aₙ = n^{−(1+β)}); BPPD Thm 3.1.
    (hβ : 0 < β) {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (nonempty approximate support; D3); BPPD Thm 3.1.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n) (sub-linear sparsity); BPPD Thm 3.1.
    (hqn : Tendsto (fun n => (q n : ℝ)/n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ is qₙ-sparse; BPPD Thm 3.1.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    -- USER-INPUT: ‖θ₀‖² ≤ qₙ log⁴n (signal-size growth condition, BPPD (11)); BPPD Thm 3.1.
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖^2 ≤ (q n : ℝ) * (Real.log n)^4) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | M * Real.sqrt (q n * Real.log n) < ‖θ - θ₀ n‖}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  sorry

/-- **BPPD Theorem 3.1, ball / `𝓝 1` form** (BPPD eq. (12)). Equivalent restatement of `dl_theorem31`:
the posterior mass of the contraction ball `{ θ : ‖θ − θ₀‖ ≤ M√(qₙ log n) }` tends to `1` in
`E_{θ₀}`. -/
theorem dl_theorem31_ball {β : ℝ}
    -- USER-INPUT: β > 0; BPPD Thm 3.1.
    (hβ : 0 < β) {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (D3); BPPD Thm 3.1.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n); BPPD Thm 3.1.
    (hqn : Tendsto (fun n => (q n : ℝ)/n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ qₙ-sparse; BPPD Thm 3.1.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    -- USER-INPUT: ‖θ₀‖² ≤ qₙ log⁴n; BPPD Thm 3.1.
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖^2 ≤ (q n : ℝ) * (Real.log n)^4) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | ‖θ - θ₀ n‖ ≤ M * Real.sqrt (q n * Real.log n)}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 1) := by
  sorry

/-- **BPPD Theorem 3.1, paper rate** (D1 recovery). Under the polynomial-sparsity regime
`qₙ ≤ n^{1−c}` (so `log(n/qₙ) ≍ log n`), the posterior contracts at the paper's minimax rate
`sₙ = √(qₙ log(n/qₙ))`. -/
theorem dl_theorem31_paper_rate {β : ℝ}
    -- USER-INPUT: β > 0; BPPD Thm 3.1.
    (hβ : 0 < β) {c : ℝ}
    -- USER-INPUT: 0 < c < 1 (polynomial-sparsity exponent for qₙ ≤ n^{1−c}); BPPD Thm 3.1 / D1.
    (hc : 0 < c) (hc1 : c < 1) {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (D3); BPPD Thm 3.1.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n); BPPD Thm 3.1.
    (hqn : Tendsto (fun n => (q n : ℝ)/n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ qₙ-sparse; BPPD Thm 3.1.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    -- USER-INPUT: ‖θ₀‖² ≤ qₙ log⁴n; BPPD Thm 3.1.
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖^2 ≤ (q n : ℝ) * (Real.log n)^4)
    -- USER-INPUT: qₙ ≤ n^{1−c} (polynomial sparsity, D1 — makes sₙ ≍ √(qₙ log n)); BPPD Thm 3.1.
    (hqpoly : ∀ᶠ n in Filter.atTop, (q n : ℝ) ≤ (n:ℝ)^(1-c)) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | M * Real.sqrt (q n * Real.log ((n:ℝ)/q n)) < ‖θ - θ₀ n‖}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  sorry

/-- **BPPD Theorem 3.1, `1/n`-regime companion.** Same conclusion (rate `M√(qₙ log n)`) at scale
`aₙ = 1/n`, additionally requiring `qₙ ≥ C₀ log n` so the internal `r² = qₙ` (D2) makes the
denominator error vanish. -/
theorem dl_theorem31_recip {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (D3); BPPD Thm 3.1.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n); BPPD Thm 3.1.
    (hqn : Tendsto (fun n => (q n : ℝ)/n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ qₙ-sparse; BPPD Thm 3.1.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    -- USER-INPUT: ‖θ₀‖² ≤ qₙ log⁴n; BPPD Thm 3.1.
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖^2 ≤ (q n : ℝ) * (Real.log n)^4)
    -- USER-INPUT: qₙ ≥ C₀ log n (needed for the 1/n-regime denominator error, D2); BPPD Thm 3.1.
    (hqlog : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ (n : ℕ) in atTop, C₀ * Real.log n ≤ (q n : ℝ)) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)⁻¹) (Fin n))) y
          {θ | M * Real.sqrt (q n * Real.log n) < ‖θ - θ₀ n‖}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  sorry

end StatLean.Bayesian
