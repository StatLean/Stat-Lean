import Mathlib.Probability.Decision.Risk.Basic
import Mathlib.Probability.Distributions.Uniform

/-!
# Minimax lower bounds — core definitions (Wainwright Ch. 15)

Laptop-only shared data model for the `Minimaxity` area (Wainwright,
*High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge, 2019, Ch. 15).

We build directly on Mathlib's decision-theoretic risk framework
(`ProbabilityTheory.minimaxRisk` / `bayesRisk` / `avgRisk`, in
`Mathlib/Probability/Decision/Risk/`):

* an **estimation problem** is a data-generating kernel `P : Kernel Θ 𝓧` (the family
  `{P_θ}` indexing Wainwright's class `𝒫`) together with a loss `ℓ : Θ → 𝓨 → ℝ≥0∞`;
* a **(randomized) estimator** is a Markov kernel `κ : Kernel 𝓧 𝓨`;
* `minimaxRisk ℓ P = ⨅_κ ⨆_θ ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)` — exactly Wainwright's
  `M(θ(𝒫); ℓ) = inf_θ̂ sup_P 𝔼_P[ℓ]` (Eq. (15.1)/(15.2)).

This file adds the Wainwright-specific wiring on top:

* `distortionLoss Φ g` — the loss `Φ(ρ(θ(P_θ), y))` (Eq. (15.2)), with the semimetric
  `ρ = edist` (Wainwright's `ρ` is a *semimetric*, footnote 1 = `PseudoEMetricSpace`);
* `minimaxRiskDist Φ g P` — the resulting minimax risk `M(θ(𝒫); Φ∘ρ)`;
* `zeroOneLoss` / `uniformPrior` / `multiwayTestingError` — the M-ary hypothesis test
  `inf_ψ ℚ[ψ(Z) ≠ J]` of §15.1.2 as a `bayesRisk` (0–1 loss, uniform prior);
* `mixture` — the mixture distribution `Q̄ = (1/M) Σⱼ P_{θʲ}` (Eq. (15.30));
* `IsSeparatedFamily g θ δ` — a `2δ`-separated finite family in the semimetric `ρ`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} {mΘ : MeasurableSpace Θ} {mΩ : MeasurableSpace Ω}
  {m𝓧 : MeasurableSpace 𝓧}

/-- The **distortion loss** `ℓ θ y = Φ(ρ(θ(P_θ), y))` of Wainwright's minimax-risk setup:
an increasing distortion `Φ : ℝ≥0∞ → ℝ≥0∞` of the semimetric `ρ = edist` between the
decision `y : Ω` and the functional value `g θ = θ(P_θ) : Ω` under parameter `θ`.

`Ω` carries the semimetric as a `PseudoEMetricSpace` (Wainwright's `ρ` is a *semimetric* —
a metric possibly with `ρ θ θ' = 0` for `θ ≠ θ'`, footnote 1 — i.e. a pseudo metric).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.1, Eq. (15.2). -/
noncomputable def distortionLoss [PseudoEMetricSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) : Θ → Ω → ℝ≥0∞ :=
  fun θ y => Φ (edist (g θ) y)

/-- Wainwright's **minimax risk** `M(θ(𝒫); Φ∘ρ) = inf_θ̂ sup_θ 𝔼_{P_θ}[Φ(ρ(θ̂, θ(P_θ)))]`,
as the Mathlib `minimaxRisk` of the `distortionLoss`. The model `P : Kernel Θ 𝓧` sends each
parameter `θ` (indexing the class `𝒫`) to its data law `P_θ`; the infimum ranges over all
(randomized) estimators `Kernel 𝓧 Ω`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.1, Eq. (15.2). -/
noncomputable def minimaxRiskDist [PseudoEMetricSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) : ℝ≥0∞ :=
  minimaxRisk (distortionLoss Φ g) P

/-- The **0–1 loss** `ℓ(j, k) = 𝟙[j ≠ k]` of an M-ary hypothesis test: zero when the
guessed index `k` equals the true index `j`, one otherwise.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2. -/
def zeroOneLoss (M : ℕ) : Fin M → Fin M → ℝ≥0∞ :=
  fun j k => if j = k then 0 else 1

/-- The **uniform prior** on the index set `Fin M` — the law of the random index `J`
drawn uniformly from `[M] = {1,…,M}` in an M-ary hypothesis test.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2. -/
noncomputable def uniformPrior (M : ℕ) [NeZero M] : Measure (Fin M) :=
  (PMF.uniformOfFintype (Fin M)).toMeasure

instance (M : ℕ) [NeZero M] : IsProbabilityMeasure (uniformPrior M) := by
  unfold uniformPrior; infer_instance

/-- The **M-ary testing error** `inf_ψ ℚ[ψ(Z) ≠ J]` of §15.1.2: the Bayes risk of the
M-ary hypothesis test with 0–1 loss and uniform prior, where `Q j = P_{θʲ}` is the data
law under hypothesis `j`. Equal to the infimum over (randomized) tests of the
misclassification probability, averaged over a uniformly random index `J`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2, Eq. (15.3). -/
noncomputable def multiwayTestingError {M : ℕ} [NeZero M]
    (Q : Kernel (Fin M) 𝓧) : ℝ≥0∞ :=
  bayesRisk (zeroOneLoss M) Q (uniformPrior M)

/-- The **mixture distribution** `Q̄ = (1/M) Σⱼ P_{θʲ}`: the marginal law of the
observation `Z` when the index `J` is drawn from the uniform prior and `Z ∼ Q J`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.1, Eq. (15.30). -/
noncomputable def mixture {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) : Measure 𝓧 :=
  Q ∘ₘ uniformPrior M

/-- A **`2δ`-separated family** in the semimetric `ρ = edist` on the functional values
(§15.1.2): a finite family of parameters `θfam : Fin M → Θ` whose functional values
`g (θfam j) = θ(P_{θʲ})` are pairwise at semimetric distance `≥ 2δ`. We enforce only the
milder `≥ 2δ` requirement (rather than `> 2δ`), as in Wainwright's footnote 2.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2. -/
def IsSeparatedFamily [PseudoEMetricSpace Ω] {M : ℕ}
    (g : Θ → Ω) (θfam : Fin M → Θ) (δ : ℝ≥0∞) : Prop :=
  ∀ j k, j ≠ k → 2 * δ ≤ edist (g (θfam j)) (g (θfam k))

end StatLean.Minimaxity
