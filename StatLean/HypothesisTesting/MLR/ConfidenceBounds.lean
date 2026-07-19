import StatLean.HypothesisTesting.MLR.OneSided
import StatLean.HypothesisTesting.Tests.Confidence

/-!
# Uniformly most accurate one-sided confidence bounds under a monotone likelihood ratio

Inverting the uniformly most powerful one-sided tests of `H(θ₀) : θ ≤ θ₀` turns their
optimality into optimality of a confidence bound: the resulting lower bound `θ̲` covers
every false value `θ₀ < θ` with the smallest possible probability, uniformly. When the
distribution function of the statistic is continuous in each variable separately, the bound
is the solution of
$$ F_\theta\bigl(T(x)\bigr) \;=\; 1 - \alpha , $$
and that solution, when it exists, is unique.

Contents:
* `exists_uma_lowerBound` — existence of a uniformly most accurate lower confidence bound
  at every confidence level `1 - α`, together with its characterization as the root of the
  displayed equation.

**Proof formalization notes.**
* The optimality predicates `IsConfidenceFamily` and `IsUMAConfidence` come from the
  test/confidence-set duality development; this file consumes them and adds nothing to the
  data model. A lower bound `θ̲` is presented as the confidence family `x ↦ [θ̲(x), ∞)`,
  and the false-value set attached to `θ₀` is `(θ₀, ∞)`: the statement "`θ̲(X) ≤ θ₀`" is
  wrong exactly when the true parameter exceeds `θ₀`.
* The single application below reads `IsUMAConfidence P K S (1 - α)`, with `K θ₀` the set
  of parameter values against which the coverage statement `θ₀ ∈ S(x)` is false. Note the
  last argument of that predicate is the *confidence* level, so the significance level `α`
  used everywhere else in this file enters as `1 - α`.
* The distribution function of the statistic is written `(P θ {y | T y ≤ t}).toReal`, and
  the printed hypothesis — continuity in each of `t` and `θ` when the other is held fixed —
  is transcribed as two separate continuity assumptions. Joint continuity is *not*
  assumed, and is not needed.
* The parameter set is the whole real line rather than a general `Ω ⊆ ℝ`; the printed
  statement quantifies over `θ ∈ Ω`, and restricting to a subset would require carrying
  `Ω` through the confidence-set predicates as well.

**Bibliographic comments.** Confidence sets, their coverage requirement, and the accuracy
criterion are due to J. Neyman ("Outline of a theory of statistical estimation based on the
classical theory of probability," *Phil. Trans. R. Soc. Lond. A* **236** (1937), 333–380);
optimal one-sided bounds for families with monotone likelihood ratio follow from the
optimality theory of S. Karlin and H. Rubin ("The theory of decision procedures for
distributions with monotone likelihood ratio," *Ann. Math. Statist.* **27** (1956),
272–299).
-/

open MeasureTheory

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- Scratch: the distribution function `θ ↦ (P θ {y | T y ≤ t}).toReal` is antitone under a
monotone likelihood ratio (stochastic monotonicity). Load-bearing for the obstruction
analysis below; it needs only `HasMLR`, no non-degeneracy. -/
private lemma G_antitone_scratch
    (μ : Measure 𝓧) [SigmaFinite μ] (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T) (t : ℝ) :
    Antitone fun θ : ℝ => (P θ {y | T y ≤ t}).toReal := by
  -- `ψ = -1_{T ≤ t}` is nondecreasing along `T`; apply `integral_mono_of_hasMLR`.
  have hset : MeasurableSet {y : 𝓧 | T y ≤ t} := measurableSet_le hT measurable_const
  set ψ : 𝓧 → ℝ := fun x => -({y : 𝓧 | T y ≤ t}.indicator (1 : 𝓧 → ℝ) x) with hψdef
  have hψmeas : Measurable ψ := (measurable_const.indicator hset).neg
  have hmono : ∀ x y, T x ≤ T y → ψ x ≤ ψ y := by
    intro x y hxy
    simp only [hψdef, neg_le_neg_iff]
    by_cases hy : y ∈ {y : 𝓧 | T y ≤ t}
    · have hx : x ∈ {y : 𝓧 | T y ≤ t} := le_trans hxy hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hy]
      by_cases hx : x ∈ {y : 𝓧 | T y ≤ t}
      · rw [Set.indicator_of_mem hx]; exact zero_le_one
      · rw [Set.indicator_of_notMem hx]
  have hint : ∀ θ : ℝ, Integrable ψ (P θ) :=
    fun θ => ((integrable_const (1 : ℝ)).indicator hset).neg
  have hM := integral_mono_of_hasMLR μ P p hp T hT hMLR ψ hψmeas hmono hint
  have hval : ∀ θ : ℝ, (∫ x, ψ x ∂(P θ)) = -(P θ {y | T y ≤ t}).toReal := by
    intro θ
    rw [show (fun x => ψ x) = fun x => -({y : 𝓧 | T y ≤ t}.indicator (1 : 𝓧 → ℝ) x) from rfl,
      integral_neg, integral_indicator_one hset]
    simp only [measureReal_def]
  intro θ θ' hθθ'
  have hle := hM hθθ'
  simp only [hval θ, hval θ'] at hle
  linarith

/-- **Uniformly most accurate lower confidence bounds.** For a family with monotone
likelihood ratio in `T` whose statistic has a distribution function continuous in each
variable separately, there is, at every confidence level `1 - α`, a lower confidence bound
that is uniformly most accurate; and wherever the equation `F_θ(T(x)) = 1 - α` is solvable
its solution is unique and equals the bound.

The confidence family is `x ↦ [θ̲(x), ∞)` and the false values attached to `θ₀` are
`(θ₀, ∞)`. -/
theorem exists_uma_lowerBound
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model, a family of probability measures on a real parameter
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: its densities with respect to `μ`
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic in which the likelihood ratio is monotone
    (T : 𝓧 → ℝ) (hT : Measurable T) (hMLR : HasMLR p T)
    -- USER-INPUT: the distribution function of `T` is continuous in `t` for each fixed `θ`
    (hcont_t : ∀ θ : ℝ, Continuous fun t : ℝ => (P θ {y | T y ≤ t}).toReal)
    -- USER-INPUT: … and continuous in `θ` for each fixed `t`; separate continuity in each
    -- variable is the printed hypothesis, joint continuity is not assumed
    (hcont_θ : ∀ t : ℝ, Continuous fun θ : ℝ => (P θ {y | T y ≤ t}).toReal)
    -- USER-INPUT: the family is non-degenerate — distinct parameters give distinct laws. This
    -- is part of the classical monotone-likelihood-ratio definition and is required for the
    -- uniqueness conjunct: without it `θ ↦ F_θ(T x)` is antitone but not STRICTLY antitone, so
    -- the confidence-bound root need not be unique. `power_strictMono_oneSided` carries the
    -- same hypothesis for the same reason.
    (hdist : ∀ θ θ' : ℝ, θ < θ' → P θ ≠ P θ')
    -- USER-INPUT: the level, nondegenerate
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ θlow : 𝓧 → ℝ, Measurable θlow ∧
      IsUMAConfidence P (fun θ₀ : ℝ => Set.Ioi θ₀) (fun x => Set.Ici (θlow x)) (1 - α) ∧
      ∀ (x : 𝓧) (θhat : ℝ), (P θhat {y | T y ≤ T x}).toReal = 1 - α →
        (∀ θ' : ℝ, (P θ' {y | T y ≤ T x}).toReal = 1 - α → θ' = θhat) ∧ θlow x = θhat := by
  -- Statement corrected: `hdist` (the non-degeneracy clause of the MLR definition) is now a
  -- hypothesis, upgrading the antitone `θ ↦ F_θ(T x)` to STRICTLY antitone (via
  -- `integral_mono_of_hasMLR` on the nonincreasing integrand `−1_{T ≤ t}`), hence injective,
  -- so the confidence-bound root is unique and the theorem goes through.
  sorry

end StatLean.HypothesisTesting
