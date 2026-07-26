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

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.5 (Confidence Bounds), Corollary 3.5.1 (uniformly most accurate one-sided
confidence bounds under a monotone likelihood ratio). (`TSH4 §3.5 Cor 3.5.1`.)

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
  -- FALSE AS STATED (verified counterexample below). `hdist` does repair the *uniqueness*
  -- conjunct — it upgrades the antitone `θ ↦ F_θ(T x)` of `G_antitone_scratch` to strictly
  -- antitone, hence injective — but the *existence* conjunct fails, because a real-valued
  -- `θlow : 𝓧 → ℝ` cannot represent the honest inverted-UMP confidence set when the latter
  -- is `∅` or all of `ℝ`.
  --
  -- COUNTEREXAMPLE. `𝓧 = ℝ`, `μ = volume`, `T = id`, `P θ = 𝒩(arctan θ, 1)`, i.e.
  -- `p θ x = ϕ(x − arctan θ)`. This is a one-parameter exponential family in `T = id` read
  -- through the strictly increasing `η = arctan`, so `hMLR` holds (`hasMLR_expFamily`);
  -- `F_θ(t) = Φ(t − arctan θ)` is continuous in each variable, giving `hcont_t`/`hcont_θ`;
  -- and `arctan` is injective, giving `hdist`. Fix any `α ∈ (0,1)` and put `z = Φ⁻¹(1 − α)`.
  --
  -- The inverted UMP family is `S(x) = {θ : x ≤ arctan θ + z}`, with exact coverage
  -- `P θ {x : x ≤ arctan θ + z} = Φ(z) = 1 − α`, and measurable slices `Iic (arctan θ₀ + z)`;
  -- so `S` is a legitimate competitor `S'` in the optimality clause. Since `arctan` has range
  -- `(−π/2, π/2)`, `S(x) = ∅` for `x ≥ z + π/2` — a set of positive `P θ`-probability for
  -- every `θ` — which no `Ici (θlow x)` can match.
  --
  -- Concretely, suppose `θlow : 𝓧 → ℝ` is measurable and satisfies the conclusion. Testing
  -- the optimality clause against `S'` at `θ₀ = j`, `θ = j + 1` gives, for every `j`,
  --   `P_{j+1} {x : θlow x ≤ j} ≤ P_{j+1} (Iic (arctan j + z)) = Φ(arctan j + z − arctan (j+1))`
  -- whose right-hand side tends to `Φ(z) = 1 − α`. Hence `P_{j+1}(B_j) ≥ α − o(1)` for
  -- `B_j = {x : θlow x > j}`. But `θlow` is real-valued, so `B_j ↓ ∅` and `N(B_j) → 0` for
  -- `N = 𝒩(π/2, 1)`, while `dTV(P_{j+1}, N) → 0` because `arctan (j+1) → π/2`; therefore
  -- `P_{j+1}(B_j) ≤ N(B_j) + dTV(P_{j+1}, N) → 0`. Since `α > 0`, this is a contradiction.
  --
  -- TODO(statement-bug): the conclusion needs either `θlow : 𝓧 → EReal` (allowing the
  -- vacuous/total confidence sets), or a hypothesis making the inverted family always a
  -- proper closed ray — e.g. surjectivity of `θ ↦ C(θ)` onto `ℝ`, which holds for genuine
  -- location families (`P θ = 𝒩(θ,1)`) but not for reparametrized ones as above. Under
  -- either fix the proof is: `C(θ)` from the intermediate value theorem applied to the
  -- continuous `F_θ` (`hcont_t`, `F_θ → 0/1` at `∓∞`), acceptance regions `A θ = {T ≤ C θ}`,
  -- UMP-ness of `acceptanceTest (A θ)` from `isMostPowerful_oneSided` (the boundary weight
  -- `γ` is irrelevant since `hcont_t` makes the `T`-marginal atomless), and then
  -- `Tests.Confidence.isUMA_of_UMP` transports optimality across the duality; `hdist` plus
  -- `power_strictMono_oneSided` gives the uniqueness conjunct. Reported per the
  -- no-weakening policy.
  sorry

end StatLean.HypothesisTesting
