import StatLean.Bayesian.DirichletLaplace.CompressEngine
import StatLean.Bayesian.DirichletLaplace.CoordinateSplit
import StatLean.Bayesian.DirichletLaplace.NormalMeansModel
import StatLean.Bayesian.DirichletLaplace.DensityBounds
import StatLean.Bayesian.ForMathlib.ExpOfRealCalc
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dirichlet–Laplace posterior compressibility — BPPD Theorem 3.4 (C15)

Assembly of BPPD **Theorem 3.4**: in the normal-means model `y = θ + ε`, `ε ~ N(0, Iₙ)`, under the
Dirichlet–Laplace prior with scale `aₙ`, the posterior probability that more than `A·qₙ` coordinates
exceed `δₙ` in absolute value tends to `0` in `E_{θ₀}`.

Objects:
* `dl_compress_reduction` — the single passage from the abstract posterior `κ†Π` to the ratio
  functions (`NormalMeansModel` bridge) together with the count split `|supp_δ(θ)| ≤ q + |supp_δ|_{Sᶜ}`
  and the tensorization (BPPD eq. (26), `CoordinateSplit`): the general-`θ₀` compress event is bounded
  by the truth-`0` compress event on the `S₀ᶜ`-submodel.
* `dl_theorem34_engine` — the fixed-`n` explicit bound: reduction + `CompressEngine`
  (`compress_ratio_le_explicit`).
* `dl_theorem34_beta` — the headline for the `β`-regime `aₙ = n^{−(1+β)}`, with internal choice
  `r² = qₙ log n`, `c` chosen so the Chernoff exponent dominates (`A > 2(C+2)/β`).
* `dl_theorem34_recip` — the companion for `aₙ = 1/n`, with internal `r² = qₙ` (which requires
  `qₙ ≥ C₀ log n → ∞` for the denominator error to vanish).

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*,
JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Theorem 3.4 (statement p. 9, proof pp. 18–19).

**Proof formalization notes.** The skeleton is *reduction → denominator event → Chernoff*: bridge the
posterior once (`dl_compress_reduction`), split the ratio integral at the denominator threshold
(`DenominatorLowerBound`), identify the numerator mean with the prior mass (`NormalMeansModel`), and
bound the prior mass of a large δ-support by the support-count Chernoff bound (`PriorSmallBall`,
`DensityBounds` for `ζ`). The asymptotics live only in the two thin corollaries.

**Deviations.**
* **D2 (regime-dependent `r`).** `dl_theorem34_beta` uses `r² = qₙ log n` (failure term needs only
  `qₙ ≥ 1`); `dl_theorem34_recip` uses `r² = qₙ` (failure term `e^{−qₙ}` vanishes only via
  `qₙ ≥ C₀ log n → ∞`). No single `r` serves both regimes — hence two corollaries off one engine.
* **D3 (`1 ≤ qₙ`).** Necessary: for `qₙ = 0` the δ-support of a continuous prior is everything, so
  Theorem 3.4 is false. Carried as the explicit `hq1` hypothesis (implicit in the paper).

**Bibliographic comments.** Posterior contraction after Ghosal, Ghosh, and van der Vaart
(*Ann. Statist.* 28 (2000), 500–531); sparse-sequence compressibility after Castillo and van der Vaart
(*Ann. Statist.* 40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

/-- **Compressibility reduction** (BPPD §6, eq. (26)). The `E_{θ₀}`-mean of the posterior mass of
`{ |supp_δ(θ)| > |S₀| + k }` (for a truth `θ₀` supported on `S₀`) is bounded by the truth-`0`
compress-ratio integral on the `S₀ᶜ`-submodel: the posterior is bridged once
(`NormalMeansModel`), the count split off the `S₀` block, and the cylinder ratio tensorized
(`CoordinateSplit`). -/
theorem dl_compress_reduction {ι : Type*} [Fintype ι] {a δ : ℝ}
    -- LEAN-ONLY: 0 < a — DL scale at a junk-free index; engine-internal.
    (ha : 0 < a) (θ₀ : EuclideanSpace ℝ ι) (S₀ : Finset ι)
    -- LEAN-ONLY: θ₀ supported on S₀; engine-internal (the truth's support, `= o(n)` in the assembly).
    (hθ₀ : ∀ i ∉ S₀, θ₀ i = 0) (k : ℕ) :
    ∫⁻ y, ((gaussShiftKernel ι)†(dlPrior a ι)) y
            {θ | ((S₀.card : ℝ) + k) < (dlSuppCount δ θ : ℝ)}
          ∂(gaussShiftKernel ι θ₀)
      ≤ ∫⁻ y, dlNumer (0 : EuclideanSpace ℝ {i : ι // i ∉ S₀}) (dlPrior a {i : ι // i ∉ S₀})
              {θ | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y
            / dlDenom (0 : EuclideanSpace ℝ {i : ι // i ∉ S₀}) (dlPrior a {i : ι // i ∉ S₀}) y
          ∂(gaussShiftKernel {i : ι // i ∉ S₀} (0 : EuclideanSpace ℝ {i : ι // i ∉ S₀})) := by
  sorry

/-- **Fixed-`n` compressibility bound** (BPPD Thm 3.4 engine). For a `q`-sparse truth `θ₀`, the
`E_{θ₀}`-mean of the posterior mass of `{ |supp_δ(θ)| > A·q }` is at most an explicit exponential
(reduction + `compress_ratio_le_explicit`): the Chernoff exponent `−(A−1)q·log c` against the model
size, plus the denominator-event error `e^{−r²/8}`. -/
theorem dl_theorem34_engine {ι : Type*} [Fintype ι] {a δ r : ℝ}
    -- LEAN-ONLY: 0 < a ≤ 1/2 — DL scale range (both density bounds); engine-internal.
    (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    -- LEAN-ONLY: 0 < δ ≤ 1 — δ-window at fixed n; engine-internal.
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    -- LEAN-ONLY: 0 < r — denominator small-ball radius; engine-internal.
    (hr : 0 < r) (θ₀ : EuclideanSpace ℝ ι) {q : ℕ}
    -- LEAN-ONLY: θ₀ q-sparse; engine-internal.
    (hq : (Finset.univ.filter fun i => θ₀ i ≠ 0).card ≤ q)
    -- LEAN-ONLY: 0 < A — compressibility multiplier; engine-internal.
    (A : ℝ) (hA : 0 < A)
    -- LEAN-ONLY: 1 < c — Chernoff parameter; engine-internal.
    (c : ℝ) (hc : 1 < c) :
    ∫⁻ y, ((gaussShiftKernel ι)†(dlPrior a ι)) y {θ | A * (q : ℝ) < (dlSuppCount δ θ : ℝ)}
          ∂(gaussShiftKernel ι θ₀)
      ≤ ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ)
              * (Real.exp 1 * a * (8 + 2 * Real.log (1 / δ))) * (c - 1)
              - (A - 1) * (q : ℝ) * Real.log c + 3 * r ^ 2))
          + ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
  sorry

/-- **BPPD Theorem 3.4 (posterior compressibility, `β`-regime).** In the normal-means model with the
Dirichlet–Laplace prior at scale `aₙ = n^{−(1+β)}`, there is a threshold `A > 0` such that the
posterior probability of `{ θ : more than A·qₙ coordinates exceed δₙ }` tends to `0` in `E_{θ₀}`.
Internal radius `r² = qₙ log n` (D2). -/
theorem dl_theorem34_beta {β : ℝ}
    -- USER-INPUT: β > 0 (DL scale exponent aₙ = n^{−(1+β)}); BPPD Thm 3.4.
    (hβ : 0 < β) {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (nonempty approximate support; D3 — for qₙ = 0 Thm 3.4 is false); BPPD Thm 3.4.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n) (sparsity grows sub-linearly); BPPD Thm 3.4.
    (hqn : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ is qₙ-sparse (at most qₙ nonzero coordinates); BPPD Thm 3.4.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    {δ : ℕ → ℝ}
    -- USER-INPUT: δ-window n^{−2} ≤ δₙ ≤ 1/2 (thresholding level; D2 — supports the internal δ = rₙ/n); BPPD Thm 3.4.
    (hδ : ∀ᶠ n in atTop, (n : ℝ)^(-2 : ℝ) ≤ δ n ∧ δ n ≤ 1/2) :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | A * q n < (dlSuppCount (δ n) θ : ℝ)}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  sorry

/-- **BPPD Theorem 3.4 (posterior compressibility, `1/n`-regime).** Same conclusion with scale
`aₙ = 1/n`, additionally requiring `qₙ ≥ C₀ log n` so the internal `r² = qₙ` (D2) forces the
denominator error `e^{−qₙ}` to vanish. -/
theorem dl_theorem34_recip {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (D3); BPPD Thm 3.4.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n); BPPD Thm 3.4.
    (hqn : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ qₙ-sparse; BPPD Thm 3.4.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    {δ : ℕ → ℝ}
    -- USER-INPUT: δ-window n^{−2} ≤ δₙ ≤ 1/2 (D2); BPPD Thm 3.4.
    (hδ : ∀ᶠ n in atTop, (n : ℝ)^(-2 : ℝ) ≤ δ n ∧ δ n ≤ 1/2)
    -- USER-INPUT: qₙ ≥ C₀ log n (needed for the 1/n-regime denominator error, D2); BPPD Thm 3.4.
    (hqlog : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ n in atTop, C₀ * Real.log n ≤ (q n : ℝ)) :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)⁻¹) (Fin n))) y
          {θ | A * q n < (dlSuppCount (δ n) θ : ℝ)}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  sorry

end StatLean.Bayesian
