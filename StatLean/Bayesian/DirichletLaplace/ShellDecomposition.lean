import StatLean.Bayesian.DirichletLaplace.GaussianTests
import StatLean.Bayesian.DirichletLaplace.CoveringNets
import StatLean.Bayesian.DirichletLaplace.CoordinateSplit

/-!
# Dirichlet–Laplace posterior contraction — shell/net decomposition (C13)

The geometric decomposition behind BPPD **Theorem 3.1** (§6 assembly). The complement of the
contraction ball `{ ‖θ − θ₀‖ > M r }` is partitioned into *shells* indexed by a δ-support pattern
`S` and a radial index `j`; each shell is covered by a finite `jr/4`-net, and a two-parameter
midpoint test controls the posterior mass of each net piece.

Objects:
* `dlShell θ₀ S j r δ` — the set of `θ` whose δ-support equals `S` and whose distance from `θ₀` lies
  in the `j`-th radial shell `[jr, (j+1)r)`. Each admissible `θ` (with bounded δ-support) falls into
  exactly one shell, so the complement of the ball is `⋃_{S} ⋃_{j ≥ M} dlShell θ₀ S j r δ`.
* `exists_shell_net` — a `jr/4`-net of `dlShell θ₀ S j r δ` of cardinality `≤ 33^{|S|}`
  (`CoveringNets`, volumetric covering of a `|S|`-dimensional ball) whose pieces have radius
  `≤ (√5/4)·jr` (using `√n·δ ≤ r` and `j ≥ 2`).
* `shell_ratio_le` — the per-shell posterior bound assembled from the midpoint tests
  (`GaussianTests`, Type I/II errors `≤ e^{−(d−ρ)²/8}` with margin `d − ρ ≥ (7/8)jr`, whence
  `≤ e^{−j²r²/12}`) and the testing→posterior conversion (`TestingBound`, `CoordinateSplit`).

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*,
JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Theorem 3.1 (statement p. 7); the shell/test machinery
is the §6 posterior-contraction assembly, in the framework of Ghosal–Ghosh–van der Vaart.

**Proof formalization notes.** The skeleton is *shells → nets → per-piece tests → series*: cover each
shell by its net, test each net piece against `θ₀`, sum the Type I errors over the `≤ 33^{|S|}` pieces
and the Type II errors against the piece prior mass. The outer summation over `(S, j)` is closed in
`Theorem31.lean` (`Nat.choose_le_pow` for the support patterns, `ExpOfRealCalc` for the radial
series).

**Deviations.**
* **D4 (net / test geometry).** The paper's `jr`-net with `2jr`-balls degenerates (a net point may
  coincide with `θ₀`), and a `(jr/2)`-net is inconsistent with a `d/3`-margin test. We use `jr/4`-nets
  (`≤ 33^{|S|}` points), pieces of radius `ρ ≤ (√5/4)jr` (from `√n·δ ≤ r`, `j ≥ 2`), and the
  two-parameter midpoint test `{ y | d(d−ρ)/2 ≤ ⟪y−θ₀, φ−θ₀⟫ }` with both errors `≤ e^{−(d−ρ)²/8}` and
  `d − ρ ≥ (7/8)jr ⇒ ≤ e^{−j²r²/12}`. The non-optimized `(1+β)` testing bound replaces the paper's
  `2√β`, avoiding Neyman–Pearson machinery at no bookkeeping cost.
* **D9 (degenerate index sets).** The `S = ∅` shell is covered by the singleton net `{0}`; handled
  proof-internally, not as a hypothesis.

**Bibliographic comments.** Sieve/net posterior-contraction testing after Ghosal, Ghosh, and van der
Vaart (*Ann. Statist.* 28 (2000), 500–531) and Castillo and van der Vaart (*Ann. Statist.* 40 (2012),
2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Contraction shell** (BPPD §6): the set of `θ` whose δ-support is exactly `S` and whose distance
from `θ₀` lies in the `j`-th radial band `[jr, (j+1)r)`. The complement of the contraction ball is the
disjoint union of these over support patterns `S` and radial indices `j`. Degenerate inputs are not
special-cased in the definition (an empty band or `S` gives the empty shell). -/
noncomputable def dlShell (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι) (j : ℕ) (r δ : ℝ) :
    Set (EuclideanSpace ℝ ι) :=
  {θ | (Finset.univ.filter fun i => δ < |θ i|) = S ∧
       (j : ℝ) * r ≤ ‖θ - θ₀‖ ∧ ‖θ - θ₀‖ < ((j : ℝ) + 1) * r}

/-- **Shell net** (BPPD §6, D4). Every contraction shell `dlShell θ₀ S j r δ` is covered by a finite
`(√5/4)·jr`-net of cardinality `≤ 33^{|S|}` living in the `|S|`-dimensional support coordinates
(`CoveringNets` volumetric covering + `CoordinateSplit`). The radius `(√5/4)jr` uses `√n·δ ≤ r` and
`j ≥ 2` (D4); the `S = ∅` case is the singleton net `{0}` (D9). -/
theorem exists_shell_net (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι) {j : ℕ}
    -- LEAN-ONLY: 2 ≤ j — radial index in the tested range; geometry regularity for the (√5/4)jr radius.
    (hj : 2 ≤ j) {r δ : ℝ}
    -- LEAN-ONLY: 0 < r — radial band width; engine-internal.
    (hr : 0 < r)
    -- LEAN-ONLY: √n·δ ≤ r — box-vs-radius control (δ = r/n regime); engine-internal (D4).
    (hδ : Real.sqrt (Fintype.card ι : ℝ) * δ ≤ r) :
    ∃ net : Finset (EuclideanSpace ℝ ι),
      net.card ≤ 33 ^ S.card ∧
      dlShell θ₀ S j r δ ⊆ ⋃ φ ∈ net, Metric.closedBall φ (Real.sqrt 5 / 4 * ((j : ℝ) * r)) := by
  sorry

/-- **Per-shell posterior bound** (BPPD §6, D4). The `E_{θ₀}`-mean of the un-normalized posterior
ratio for a single shell is bounded by the sum over its `≤ 33^{|S|}` net pieces of the Type I test
error `e^{−j²r²/12}`, plus the shell prior mass weighted by the Type II error over the denominator
threshold `dbar`. Assembled from `GaussianTests` (the midpoint tests) and `TestingBound`. -/
theorem shell_ratio_le (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι) {j : ℕ}
    -- LEAN-ONLY: 2 ≤ j — tested radial range (margin d − ρ ≥ (7/8)jr needs j ≥ 2); engine-internal.
    (hj : 2 ≤ j) {a r δ : ℝ}
    -- LEAN-ONLY: 0 < a, 0 < r — DL scale and band width; engine-internal.
    (ha : 0 < a) (hr : 0 < r)
    -- LEAN-ONLY: √n·δ ≤ r — piece-radius control (D4); engine-internal.
    (hδ : Real.sqrt (Fintype.card ι : ℝ) * δ ≤ r)
    -- LEAN-ONLY: 0 < dbar — denominator lower threshold from `DenominatorLowerBound`; engine-internal.
    (dbar : ℝ≥0∞) (hdbar : 0 < dbar) :
    ∫⁻ y, dlNumer θ₀ (dlPrior a ι) (dlShell θ₀ S j r δ) y / dlDenom θ₀ (dlPrior a ι) y
        ∂(gaussShiftKernel ι θ₀)
      ≤ (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12))
          + (dlPrior a ι) (dlShell θ₀ S j r δ)
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12)) / dbar := by
  sorry

end StatLean.Bayesian
