import StatLean.Bayesian.DirichletLaplace.PriorSmallBall
import StatLean.Bayesian.DirichletLaplace.NormalMeansModel
import StatLean.Bayesian.DirichletLaplace.DenominatorLowerBound
import StatLean.Bayesian.DirichletLaplace.TestingBound

/-!
# Dirichlet–Laplace posterior compressibility — the fixed-`n`, truth-`0` engine (C12)

The fixed-dimension core behind BPPD **Theorem 3.4** (posterior compressibility of the normal-means
model under the Dirichlet–Laplace prior). Working at the true parameter `θ₀ = 0` (the case the
`S₀ᶜ`-submodel reduction in `Theorem34.lean` produces), we bound

`E_{θ₀=0} [ posterior mass of { θ : |supp_δ(θ)| > k } ]`

expressed on the un-normalized ratio `dlNumer / dlDenom` (the passage to the abstract posterior `κ†Π`
happens once, in `Theorem34.lean`, via `NormalMeansModel`).

Objects:
* `compress_ratio_le` — the split bound: on the event `{ D ≥ dbar }` with `dbar = e^{−r²}·Π(B(0,r))` the
  ratio is `≤ dlNumer/dbar` and its `E_{θ₀=0}`-mean equals the prior mass (change-of-measure Tonelli,
  BPPD §6, `NormalMeansModel`); on `{ D < dbar }` the Castillo–van der Vaart denominator event
  (`DenominatorLowerBound`, a Jensen / one-dimensional-Gaussian argument) contributes `≤ e^{−r²/8}`.
* `compress_ratio_le_explicit` — plug the support-count MGF / Chernoff bound (`PriorSmallBall`,
  `Π{|supp_δ| > k}`) and the small-ball lower bound into `compress_ratio_le`, collapsing the RHS to a
  single exponential in the model size, the Chernoff parameter `c`, and the radius `r`.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Theorem 3.4 (statement p. 9,
proof pp. 18–19); the denominator-event lemma is the analogue of Ghosal–Ghosh–van der Vaart /
Castillo–van der Vaart Lemma 5.2.

**Proof formalization notes.** The skeleton is *reduction → denominator event → Chernoff*: the ratio
integral is split at `dbar`, the denominator event handled by `measure_dlDenom_lt_le`, the numerator
mean identified with the prior mass, and the prior mass bounded by the count Chernoff bound.

**Deviations.**
* **D2 (regime-dependent `r`).** The engine keeps `r` free. The `β`-regime (`Theorem34.lean`)
  instantiates `r² = qₙ log n`; the `1/n`-regime uses `r² = qₙ`. A fixed choice cannot serve both:
  `r² = qₙ` leaves the `β`-regime failure term `e^{−qₙ}` non-vanishing for bounded `qₙ`, while
  `r² = qₙ log n` breaks the `1/n`-regime Chernoff exponent. Hence the free-`r` statement here.
* **D3 (`1 ≤ qₙ`).** For an empty support the δ-support of a continuous prior is everything and the
  radius `r² → ∞` fails; the compressibility statement is vacuous. The dimensional hypotheses below
  are engine-internal regularity; the sequence-level `1 ≤ qₙ` is enforced in the assembly headline.

**Bibliographic comments.** Posterior contraction in the sense of Ghosal, Ghosh, and van der Vaart
(*Ann. Statist.* 28 (2000), 500–531); the sparse-sequence denominator-event technique follows
Castillo and van der Vaart (*Ann. Statist.* 40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Compressibility split bound** (BPPD Thm 3.4 core). At the true parameter `θ₀ = 0`, the
`E_{θ₀=0}`-mean of the un-normalized posterior ratio for `{ |supp_δ(θ)| > k }` is at most the prior
mass of that set divided by `dbar = e^{−r²}·Π(B(0,r))`, plus the denominator-event error `e^{−r²/8}`.
The two summands are the `{D ≥ dbar}` (testing/numerator) and `{D < dbar}` (denominator-event) pieces. -/
theorem compress_ratio_le {a δ r : ℝ}
    -- LEAN-ONLY: 0 < a — DL scale at a junk-free index; engine-internal regularity.
    (ha : 0 < a)
    -- LEAN-ONLY: 0 < r — working radius of the denominator small ball; engine-internal.
    (hr : 0 < r) (k : ℕ) :
    ∫⁻ y, dlNumer (0 : EuclideanSpace ℝ ι) (dlPrior a ι) {θ | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y
          / dlDenom (0 : EuclideanSpace ℝ ι) (dlPrior a ι) y
        ∂(gaussShiftKernel ι (0 : EuclideanSpace ℝ ι))
      ≤ (dlPrior a ι) {θ | (k : ℝ) < (dlSuppCount δ θ : ℝ)}
            / (ENNReal.ofReal (Real.exp (- r ^ 2))
                * (dlPrior a ι) (Metric.closedBall (0 : EuclideanSpace ℝ ι) r))
          + ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
  sorry

/-- **Explicit compressibility bound** (BPPD Thm 3.4 core). Feeding the support-count Chernoff bound
(`PriorSmallBall`, MGF parameter `c > 1`) and the small-ball lower bound into `compress_ratio_le`
collapses the RHS to a single exponential (`m·ζ·(c−1) − k·log c` Chernoff exponent, `ζ ≤ e·a·(8+2log
(1/δ))` from `DensityBounds`, `m = card ι`, roomy `3 r²` small-ball slack) plus `e^{−r²/8}`. -/
theorem compress_ratio_le_explicit {a δ r : ℝ}
    -- LEAN-ONLY: 0 < a ≤ 1 — DL scale range for the lower density / small-ball bounds; engine-internal.
    (ha : 0 < a) (ha1 : a ≤ 1)
    -- LEAN-ONLY: 0 < r — working radius; engine-internal.
    (hr : 0 < r)
    -- LEAN-ONLY: 0 < δ ≤ 1 — δ-window at fixed n; engine-internal (the sequence window is in the headline).
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k : ℕ)
    -- LEAN-ONLY: 1 < c — free Chernoff/MGF parameter for the support-count tail; engine-internal.
    (c : ℝ) (hc : 1 < c) :
    ∫⁻ y, dlNumer (0 : EuclideanSpace ℝ ι) (dlPrior a ι) {θ | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y
          / dlDenom (0 : EuclideanSpace ℝ ι) (dlPrior a ι) y
        ∂(gaussShiftKernel ι (0 : EuclideanSpace ℝ ι))
      ≤ ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ)
              * (Real.exp 1 * a * (8 + 2 * Real.log (1 / δ))) * (c - 1)
              - (k : ℝ) * Real.log c + 3 * r ^ 2))
          + ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
  sorry

end StatLean.Bayesian
