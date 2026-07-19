import StatLean.HypothesisTesting.Invariance.Defs

/-!
# UMP invariant tests under a finite group with transitive induced action

When a testing problem is invariant under a **finite** group `G` and the induced group on
the parameter space acts **transitively** on the null class and on the alternative class
separately, the invariance reduction collapses a composite-vs-composite problem to a
simple-vs-simple one. The reason is that an invariant test has the same power at every
parameter of an induced orbit, so maximizing power against one alternative maximizes it
against all of them; the Neyman–Pearson lemma applied to the pair of **orbit-averaged**
densities then produces a uniformly most powerful invariant test.

Concretely, with the model dominated by a σ-finite measure and densities `p θ`, the test
rejects for large values of
$$ \frac{|G|^{-1}\sum_{g \in G} p_{\bar g\theta_1}(x)}
        {|G|^{-1}\sum_{g \in G} p_{\bar g\theta_0}(x)} , $$
where `θ₀` and `θ₁` are *any* members of the null and alternative classes — the ratio does
not depend on which representatives are chosen.

**Main results.**
* `isInvariantTest_orbitAverage` — the orbit average of any function is invariant;
* `orbitAverage_eq_avg_translated_density` — the orbit average of a density agrees a.e.
  with the average of the densities at the translated parameters, i.e. with the numerator
  and denominator of the displayed ratio, whenever the dominating measure is invariant;
* `isUMPInvariant_of_orbitAverage_ratio` — a Neyman–Pearson test for the orbit-averaged
  densities is UMP invariant at its size;
* `exists_isUMPInvariant_of_finite_transitive` — the existence statement.

**Proof formalization notes.**
* The book states the rejection region through the *parameter-side* average
  `∑ᵢ p_{ḡᵢθ}(x)/N`. The definitional device available here is `orbitAverage`, the
  *sample-side* average `|G|⁻¹ ∑_g p_θ(g·x)`. The two agree a.e. once the dominating
  measure is `G`-invariant (model invariance then reads `p_{ḡθ}(x) = p_θ(g⁻¹·x)` a.e.);
  `orbitAverage_eq_avg_translated_density` records exactly that bridge, so the headline
  theorem is stated on the sample side without any loss of faithfulness.
* Stability of the null and alternative classes under the induced action (`hΘ₀`, `hΘ₁`) is
  *separate* from transitivity and both are demanded: transitivity relates two points of a
  class, stability says the class is not left.
* Invariance of the candidate test is a hypothesis rather than a conclusion because the
  Neyman–Pearson prescription pins the test only off the boundary `{ratio = k}`, where the
  choice is free. `isInvariantTest_orbitAverage` shows that the ratio itself is always
  invariant, so the hypothesis only constrains that free choice.
* The Neyman–Pearson input is used through the declarations of the fundamental lemma
  planned for the sibling `Tests` layer (work item `ht/test-foundations`); the predicates
  `IsMostPowerful` / `IsLevel` / `power` used here all come from `Tests.Defs`.

**Bibliographic comments.** The reduction of an invariant testing problem with a transitive
induced group to a simple-vs-simple problem, and the resulting orbit-averaged likelihood
ratio, belong to the invariance program of G. A. Hunt and C. Stein ("Most stringent tests
of statistical hypotheses," unpublished manuscript, 1946) and C. Stein ("Some problems in
multivariate analysis, Part I," Technical Report 6, Department of Statistics, Stanford
University, 1956), as developed in E. L. Lehmann's lecture tradition of the 1950s. The
underlying optimality criterion is that of J. Neyman and E. S. Pearson ("On the problem of
the most efficient tests of statistical hypotheses," *Phil. Trans. R. Soc. A* **231**
(1933), 289–337).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation (IsInvariantModel)

variable {G Θ 𝓧 : Type*} [Group G] [MeasurableSpace 𝓧] [MulAction G 𝓧] [MulAction G Θ]

/-- **Orbit averages are invariant.** Averaging over a finite group produces a function
constant on orbits, since left translation permutes the group. -/
theorem isInvariantTest_orbitAverage [Fintype G] (f : 𝓧 → ℝ) :
    IsInvariantTest G (orbitAverage G f) := by
  sorry

/-- **Sample-side and parameter-side orbit averages agree.** For a dominated invariant
model whose dominating measure is itself `G`-invariant, the orbit average of the density
at a fixed parameter coincides almost everywhere with the average of the densities at the
translated parameters — the quantity appearing in the classical rejection region. -/
theorem orbitAverage_eq_avg_translated_density [Fintype G] {P : Θ → Measure 𝓧}
    {μ : Measure 𝓧} {p : Θ → 𝓧 → ℝ} (θ : Θ)
    -- USER-INPUT: the model intertwines the sample- and parameter-space actions
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the model is dominated by `μ` with densities `p`
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (p θ x))
    -- USER-INPUT: the densities are measurable and nonnegative
    (hpmeas : ∀ θ, Measurable (p θ)) (hpnonneg : ∀ θ x, 0 ≤ p θ x)
    -- USER-INPUT: the dominating measure is invariant under the group
    (hμ : ∀ g : G, μ.map (g • ·) = μ) :
    orbitAverage G (p θ) =ᵐ[μ] fun x => (Fintype.card G : ℝ)⁻¹ * ∑ g : G, p (g • θ) x := by
  sorry

/-- **A Neyman–Pearson test for the orbit-averaged densities is UMP invariant.** For a
finite group whose induced action is transitive on the null class and on the alternative
class, an invariant test that rejects where the orbit-averaged likelihood ratio exceeds a
threshold, accepts where it falls short, and has size `α`, is uniformly most powerful
among invariant level-`α` tests. -/
theorem isUMPInvariant_of_orbitAverage_ratio [Fintype G] {P : Θ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {μ : Measure 𝓧} [SigmaFinite μ] {p : Θ → 𝓧 → ℝ}
    {Θ₀ Θ₁ : Set Θ} {θ₀ θ₁ : Θ} {α k : ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: the model intertwines the sample- and parameter-space actions
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the null and alternative classes are preserved by the induced action
    (hΘ₀ : ∀ (g : G) (θ : Θ), θ ∈ Θ₀ → g • θ ∈ Θ₀)
    (hΘ₁ : ∀ (g : G) (θ : Θ), θ ∈ Θ₁ → g • θ ∈ Θ₁)
    -- USER-INPUT: the induced action is transitive on the null class
    (htrans₀ : ∀ θ ∈ Θ₀, ∀ θ' ∈ Θ₀, ∃ g : G, θ' = g • θ)
    -- USER-INPUT: the induced action is transitive on the alternative class
    (htrans₁ : ∀ θ ∈ Θ₁, ∀ θ' ∈ Θ₁, ∃ g : G, θ' = g • θ)
    -- USER-INPUT: the model is dominated by `μ` with measurable nonnegative densities `p`
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (p θ x))
    (hpmeas : ∀ θ, Measurable (p θ)) (hpnonneg : ∀ θ x, 0 ≤ p θ x)
    -- USER-INPUT: the chosen null and alternative representatives
    (hθ₀ : θ₀ ∈ Θ₀) (hθ₁ : θ₁ ∈ Θ₁)
    -- USER-INPUT: `φ` is a critical function, invariant under the group
    (hφ : IsCriticalFn φ) (hφinv : IsInvariantTest G φ)
    -- USER-INPUT: `φ` rejects above and accepts below the threshold `k` for the
    -- orbit-averaged likelihood ratio
    (hrej : ∀ x, k * orbitAverage G (p θ₀) x < orbitAverage G (p θ₁) x → φ x = 1)
    (hacc : ∀ x, orbitAverage G (p θ₁) x < k * orbitAverage G (p θ₀) x → φ x = 0)
    -- USER-INPUT: `φ` has size exactly `α` at the null representative
    (hsize : power P φ θ₀ = α) :
    IsUMPInvariant G P Θ₀ Θ₁ α φ := by
  sorry

/-- **Existence of a UMP invariant test under a finite transitive group.** -/
theorem exists_isUMPInvariant_of_finite_transitive [Fintype G] {P : Θ → Measure 𝓧}
    [∀ θ, IsProbabilityMeasure (P θ)] {μ : Measure 𝓧} [SigmaFinite μ] {p : Θ → 𝓧 → ℝ}
    {Θ₀ Θ₁ : Set Θ} {α : ℝ}
    -- USER-INPUT: the model intertwines the sample- and parameter-space actions
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT: the null and alternative classes are preserved by the induced action
    (hΘ₀ : ∀ (g : G) (θ : Θ), θ ∈ Θ₀ → g • θ ∈ Θ₀)
    (hΘ₁ : ∀ (g : G) (θ : Θ), θ ∈ Θ₁ → g • θ ∈ Θ₁)
    -- USER-INPUT: the induced action is transitive on each of the two classes
    (htrans₀ : ∀ θ ∈ Θ₀, ∀ θ' ∈ Θ₀, ∃ g : G, θ' = g • θ)
    (htrans₁ : ∀ θ ∈ Θ₁, ∀ θ' ∈ Θ₁, ∃ g : G, θ' = g • θ)
    -- USER-INPUT: both classes are nonempty
    (hne₀ : Θ₀.Nonempty) (hne₁ : Θ₁.Nonempty)
    -- USER-INPUT: the model is dominated by `μ` with measurable nonnegative densities `p`
    (hdens : ∀ θ, P θ = μ.withDensity fun x => ENNReal.ofReal (p θ x))
    (hpmeas : ∀ θ, Measurable (p θ)) (hpnonneg : ∀ θ x, 0 ≤ p θ x)
    -- USER-INPUT: the prescribed level is a probability
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ φ : 𝓧 → ℝ, IsUMPInvariant G P Θ₀ Θ₁ α φ := by
  sorry

end StatLean.HypothesisTesting
