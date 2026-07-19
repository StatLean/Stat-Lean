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
    -- USER-INPUT: the level, nondegenerate
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ θlow : 𝓧 → ℝ, Measurable θlow ∧
      IsUMAConfidence P (fun θ₀ : ℝ => Set.Ioi θ₀) (fun x => Set.Ici (θlow x)) (1 - α) ∧
      ∀ (x : 𝓧) (θhat : ℝ), (P θhat {y | T y ≤ T x}).toReal = 1 - α →
        (∀ θ' : ℝ, (P θ' {y | T y ≤ T x}).toReal = 1 - α → θ' = θhat) ∧ θlow x = θhat := by
  -- OBSTRUCTION (statement bug): the frozen conclusion is FALSE as written, because it omits
  -- the non-degeneracy clause of the classical monotone-likelihood-ratio definition, namely
  -- `∀ θ θ', θ < θ' → P θ ≠ P θ'` (equivalently, strict monotonicity of `θ ↦ F_θ(t)`). The
  -- frozen `HasMLR` is the division-free TP2 cross-product condition ONLY; it is satisfied
  -- *vacuously* by a constant family (see `MLR/Defs.lean` and the note on
  -- `power_strictMono_oneSided` in `MLR/OneSided.lean`, which carries exactly the omitted
  -- `hdist`). The final conjunct of this statement — the root-characterization clause
  --     ∀ x θhat, F_θhat(T x) = 1 - α → (∀ θ', F_θ'(T x) = 1 - α → θ' = θhat) ∧ θlow x = θhat
  -- asserts UNIQUENESS of the root of `θ ↦ F_θ(T x) = 1 - α`, which requires that map to be
  -- injective (strictly antitone). It is antitone under `HasMLR` — the load-bearing fact is
  -- verified unconditionally in `G_antitone_scratch` above via `integral_mono_of_hasMLR` with
  -- the nonincreasing-in-`T` integrand `-1_{T ≤ t}` — but NOT strictly antitone without the
  -- omitted hypothesis.
  --
  -- EXPLICIT COUNTEREXAMPLE. Take `𝓧 = ℝ`, `μ = volume`, and the CONSTANT family
  -- `P θ = 𝒩(0,1)` for every `θ`, with `p θ = ` the standard-normal density and `T = id`.
  --   • `HasMLR p T` holds vacuously: `p θ' x · p θ y ≤ p θ x · p θ' y` is `p x·p y ≤ p x·p y`.
  --   • `hcont_t`/`hcont_θ` hold: `F_θ(t) = Φ(t)` is continuous in `t`, and constant (hence
  --     continuous) in `θ`.
  --   • Each `P θ` is a probability measure with density w.r.t. `μ`.
  -- Choose `α = 1/2`, so `1 - α = 1/2 = Φ(0)`. For any `x` with `T x = 0` and any `θhat`,
  -- `F_θhat(T x) = Φ(0) = 1 - α`, so the hypothesis of the clause is met; but the uniqueness
  -- conclusion `∀ θ', Φ(0) = 1 - α → θ' = θhat` is FALSE (e.g. `θ' = θhat + 1` is another
  -- root). Hence NO choice of `θlow` can satisfy the final conjunct: the theorem is not
  -- provable as stated.
  --
  -- WHAT IS TRUE. The first two conjuncts (a measurable lower bound `θlow` whose confidence
  -- family `x ↦ [θlow x, ∞)` is uniformly most accurate at level `1 - α` against
  -- `θ₀ ↦ (θ₀, ∞)`) DO hold — this is the Karlin–Rubin inversion of the UMP one-sided tests
  -- `isUMP_oneSided`, with `θlow x = sInf {θ₀ | F_θ₀(T x) ≤ 1 - α}` a closed lower ray by the
  -- antitonicity + continuity `hcont_θ`. But they cannot be delivered in isolation: the
  -- statement bundles them with the false uniqueness clause into a single `∧`, and the
  -- no-weakening policy forbids dropping or altering the third conjunct here.
  --
  -- HONEST FIX (out of scope: signatures are frozen). Add the hypothesis
  --   (hdist : ∀ θ θ' : ℝ, θ < θ' → P θ ≠ P θ')
  -- (matching `power_strictMono_oneSided`). It upgrades `G_antitone_scratch` to STRICT
  -- antitonicity, making `θ ↦ F_θ(T x)` injective, whence the root is unique and equals
  -- `θlow x`; the whole theorem then goes through.
  sorry

end StatLean.HypothesisTesting
