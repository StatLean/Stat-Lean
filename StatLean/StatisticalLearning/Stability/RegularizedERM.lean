import StatLean.StatisticalLearning.Stability.Generalization

/-!
# Tikhonov regularization is a stabilizer

The Lipschitz track of SSBD §13.3–§13.4: strong convexity of the Tikhonov
objective (SSBD Lemma 13.5, parts 1–3), the RLM sensitivity bound
`‖A(S^{(i)}) − A(S)‖ ≤ 2ρ/(λn)` (SSBD Eqs. (13.7)–(13.11)), the pointwise and
on-average stability rate `2ρ²/(λn)` (SSBD Corollary 13.6), the oracle
inequality `E[L_D(A(S))] ≤ L_D(w⋆) + λ‖w⋆‖² + 2ρ²/(λn)` (SSBD Corollary
13.8), and the tuned rate `ρB√(8/n)` at `λ = √(2ρ²/(B²n))` for
convex-Lipschitz-bounded problems (SSBD Corollary 13.9).

**Reference.** SSBD Ch. 13 (Definitions 13.3/13.4, Lemma 13.5, Corollaries
13.6, 13.8, 13.9); Ch. 12 (Definition 12.12). Transcriptions:
`notes/statistical_learning/book_statements/ch12-13.md`.

**Formalization notes.** The smooth-loss track (Corollaries 13.7/13.10/13.11,
the `48β` constants) is excluded from Round 1. Hypotheses are `W` a real
inner-product space, loss convex in `w` for each `z` (`ConvexOn ℝ univ`) and
globally `ρ`-Lipschitz in `w`; the RLM selector is data (`IsRLMMin` per
sample). Lemma 13.5(1) is the exact inner-product identity
`‖aw + bu‖² = a‖w‖² + b‖u‖² − ab‖w − u‖²` (`a + b = 1`); 13.5(3) needs no
limits — instantiate the strong-convexity inequality and let `a ↓ 0` via
`le_of_forall_pos_le_add`-style bookkeeping.
-/

open MeasureTheory
open scoped ENNReal BigOperators RealInnerProductSpace

namespace StatLean.StatisticalLearning

variable {Z : Type*} [MeasurableSpace Z] {W : Type*} [NormedAddCommGroup W]
  [InnerProductSpace ℝ W] {n : ℕ} {ℓ : W → Z → ℝ} {lam ρ : ℝ}

/-- **SSBD Lemma 13.5(1)**: `w ↦ λ‖w‖²` is `2λ`-strongly convex (an exact
inner-product identity, no inequality slack). -/
theorem stronglyConvexWith_smul_norm_sq (hlam : 0 ≤ lam) :
    StronglyConvexWith (2 * lam) (fun w : W => lam * ‖w‖ ^ 2) := by
  sorry

/-- **SSBD Lemma 13.5(2)**: adding a convex function preserves `λ`-strong
convexity. -/
theorem StronglyConvexWith.add_convexOn {f g : W → ℝ}
    (hf : StronglyConvexWith lam f)
    -- USER-INPUT: `g` convex; SSBD Lemma 13.5(2)
    (hg : ConvexOn ℝ Set.univ g) :
    StronglyConvexWith lam (fun w => f w + g w) := by
  sorry

/-- **SSBD Lemma 13.5(3)** (quadratic growth at a minimizer): if `f` is
`λ`-strongly convex and `u` is a global minimizer, then
`f(w) − f(u) ≥ (λ/2)‖w − u‖²`. -/
theorem StronglyConvexWith.quadratic_growth {f : W → ℝ} {u : W}
    (hf : StronglyConvexWith lam f)
    -- USER-INPUT: `u` minimizes `f`; SSBD Lemma 13.5(3)
    (hu : ∀ v, f u ≤ f v) (w : W) :
    lam / 2 * ‖w - u‖ ^ 2 ≤ f w - f u := by
  sorry

/-- The Tikhonov objective is `2λ`-strongly convex for a convex loss
(SSBD Eq. (13.7) setup, via Lemma 13.5(1)–(2) and convexity of `L_S`). -/
theorem stronglyConvexWith_rlmObjective {s : Sample Z n}
    -- USER-INPUT: convex loss in `w`; SSBD Cor. 13.6 hypothesis
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    -- USER-INPUT: `λ > 0`; SSBD Eq. (13.2)
    (hlam : 0 < lam) :
    StronglyConvexWith (2 * lam) (rlmObjective ℓ lam s) := by
  sorry

/-- **RLM sensitivity** (SSBD Eqs. (13.7)–(13.11)): for a convex `ρ`-Lipschitz
loss, replace-one RLM minimizers are `2ρ/(λn)`-close. -/
theorem rlm_replaceOne_dist_le {s : Sample Z n} {i : Fin n} {z' : Z}
    {w w' : W}
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    -- USER-INPUT: `ρ`-Lipschitz loss in `w`; SSBD Cor. 13.6 hypothesis
    (hlip : ∀ z (v v' : W), |ℓ v z - ℓ v' z| ≤ ρ * ‖v - v'‖)
    (hlam : 0 < lam)
    -- USER-INPUT: `w` is RLM on `s`, `w'` is RLM on `s^{(i)}`; SSBD §13.3
    (hw : IsRLMMin ℓ lam s w) (hw' : IsRLMMin ℓ lam (replaceOne s i z') w')
    -- USER-INPUT: at least one example; SSBD §13.2 (implicit)
    (hn : 1 ≤ n) :
    ‖w' - w‖ ≤ 2 * ρ / (lam * n) := by
  sorry

/-- **SSBD Corollary 13.6, pointwise form**: the replace-one loss increment of
RLM is at most `2ρ²/(λn)` at every sample, index, and replacement point. -/
theorem rlm_pointwise_stability {s : Sample Z n} {i : Fin n} {z' : Z}
    {w w' : W} {z : Z}
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    (hlip : ∀ z (v v' : W), |ℓ v z - ℓ v' z| ≤ ρ * ‖v - v'‖)
    (hlam : 0 < lam)
    (hw : IsRLMMin ℓ lam s w) (hw' : IsRLMMin ℓ lam (replaceOne s i z') w')
    (hn : 1 ≤ n) :
    ℓ w' z - ℓ w z ≤ 2 * ρ ^ 2 / (lam * n) := by
  sorry

/-- **SSBD Corollary 13.6** (Tikhonov stability): an RLM selector is
on-average-replace-one stable with rate `2ρ²/(λn)`; combined with Theorem 13.2
its expected overfitting gap obeys the same bound. Stated at fixed `n` via the
`stabilityGap`. -/
theorem rlm_stabilityGap_le (D : Measure Z) [IsProbabilityMeasure D]
    {A : Sample Z n → W}
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    (hlip : ∀ z (v v' : W), |ℓ v z - ℓ v' z| ≤ ρ * ‖v - v'‖)
    -- USER-INPUT: `ρ ≥ 0`; SSBD Def. 12.6 (Lipschitz constant)
    (hρ : 0 ≤ ρ)
    (hlam : 0 < lam)
    -- USER-INPUT: `A` is an RLM selector; SSBD Eq. (13.2) (argmin is data)
    (hA : ∀ s : Sample Z n, IsRLMMin ℓ lam s (A s))
    -- LEAN-ONLY: integrability of the replace-one increments (the book's
    -- expectation presupposes it)
    (hint : ∀ i : Fin n, Integrable
      (fun p : Sample Z n × Z =>
        ℓ (A (replaceOne p.1 i p.2)) (p.1 i) - ℓ (A p.1) (p.1 i))
      ((sampleLaw D n).prod D))
    (hn : 1 ≤ n) :
    stabilityGap D ℓ A ≤ 2 * ρ ^ 2 / (lam * n) := by
  sorry

/-- **SSBD Corollary 13.8** (oracle inequality for RLM): for every competitor
`w⋆`, `E_S[L_D(A(S))] ≤ L_D(w⋆) + λ‖w⋆‖² + 2ρ²/(λn)`. -/
theorem rlm_oracle (D : Measure Z) [IsProbabilityMeasure D]
    {A : Sample Z n → W} (w⋆ : W)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    (hlip : ∀ z (v v' : W), |ℓ v z - ℓ v' z| ≤ ρ * ‖v - v'‖)
    (hρ : 0 ≤ ρ)
    (hlam : 0 < lam)
    (hA : ∀ s : Sample Z n, IsRLMMin ℓ lam s (A s))
    -- USER-INPUT: integrable competitor loss; SSBD Remark 3.1
    (hw⋆int : Integrable (ℓ w⋆) D)
    -- LEAN-ONLY: integrability bundle for Theorem 13.2 and Eq. (13.16)
    (hint₁ : Integrable
      (fun p : Sample Z n × Z => ℓ (A p.1) p.2) ((sampleLaw D n).prod D))
    (hint₂ : ∀ i : Fin n, Integrable
      (fun p : Sample Z n × Z => ℓ (A (replaceOne p.1 i p.2)) (p.1 i))
      ((sampleLaw D n).prod D))
    (hint₃ : ∀ i : Fin n, Integrable
      (fun s : Sample Z n => ℓ (A s) (s i)) (sampleLaw D n))
    (hint₄ : Integrable
      (fun s : Sample Z n => empRisk ℓ s (A s)) (sampleLaw D n))
    (hn : 1 ≤ n) :
    ∫ s, risk D ℓ (A s) ∂(sampleLaw D n) ≤
      risk D ℓ w⋆ + lam * ‖w⋆‖ ^ 2 + 2 * ρ ^ 2 / (lam * n) := by
  sorry

/-- **SSBD Corollary 13.9** (convex-Lipschitz-bounded learnability via RLM):
with `λ = √(2ρ²/(B²n))`, the RLM rule satisfies
`E_S[L_D(A(S))] ≤ inf_{‖w‖≤B} L_D(w) + ρB√(8/n)`. -/
theorem rlm_tuned_excess_risk (D : Measure Z) [IsProbabilityMeasure D]
    {A : Sample Z n → W} {B : ℝ}
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w : W => ℓ w z))
    (hlip : ∀ z (v v' : W), |ℓ v z - ℓ v' z| ≤ ρ * ‖v - v'‖)
    -- USER-INPUT: `ρ > 0`, `B > 0`; SSBD Def. 12.12 parameters
    (hρ : 0 < ρ) (hB : 0 < B)
    -- USER-INPUT: `A` is the RLM selector at the tuned
    -- `λ = √(2ρ²/(B²n))`; SSBD Cor. 13.9
    (hA : ∀ s : Sample Z n,
      IsRLMMin ℓ (Real.sqrt (2 * ρ ^ 2 / (B ^ 2 * n))) s (A s))
    -- USER-INPUT: integrable losses on the comparison ball; SSBD Remark 3.1
    (hint : ∀ w : W, ‖w‖ ≤ B → Integrable (ℓ w) D)
    -- LEAN-ONLY: integrability bundle as in `rlm_oracle`
    (hint₁ : Integrable
      (fun p : Sample Z n × Z => ℓ (A p.1) p.2) ((sampleLaw D n).prod D))
    (hint₂ : ∀ i : Fin n, Integrable
      (fun p : Sample Z n × Z => ℓ (A (replaceOne p.1 i p.2)) (p.1 i))
      ((sampleLaw D n).prod D))
    (hint₃ : ∀ i : Fin n, Integrable
      (fun s : Sample Z n => ℓ (A s) (s i)) (sampleLaw D n))
    (hint₄ : Integrable
      (fun s : Sample Z n => empRisk ℓ s (A s)) (sampleLaw D n))
    -- LEAN-ONLY: bounded-below risk image on the ball
    (hbdd : BddBelow (risk D ℓ '' {w : W | ‖w‖ ≤ B}))
    (hn : 1 ≤ n) :
    ∫ s, risk D ℓ (A s) ∂(sampleLaw D n) ≤
      bestRisk D {w : W | ‖w‖ ≤ B} ℓ + ρ * B * Real.sqrt (8 / n) := by
  sorry

end StatLean.StatisticalLearning
