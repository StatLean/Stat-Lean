import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
import StatLean.ConcentrationInequalities.Chaining.FinsetMaximal
import StatLean.ConcentrationInequalities.Chaining.PsiTwoMaximal
import StatLean.ConcentrationInequalities.Chaining.DyadicNets
import StatLean.ConcentrationInequalities.Chaining.EntropySum

/-!
# Discrete Dudley inequality (Theorem 8.1.4)

The chaining workhorse: for a process with sub-gaussian increments
(parameter $K$) on a finite index set $T$,
$$ \mathbb{E}\Bigl[\sup_{t \in T} X_t\Bigr]
     \;\le\; 6\sqrt{3}\; K \sum_{k \in \mathbb{Z}} 2^{-k}
       \sqrt{\log \mathcal{N}(T, d, 2^{-k})} $$
under mean-zero coordinates, and the no-mean-zero absolute deviation form
$$ \mathbb{E}\Bigl[\sup_{t \in T} |X_t - X_{t_0}|\Bigr]
     \;\le\; 20\, K \sum_{k \in \mathbb{Z}} 2^{-k}
       \sqrt{\log \mathcal{N}(T, d, 2^{-k})}. $$
Assembly file.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Theorem 8.1.4 and Eq. (8.2); the absolute
form is the discrete Remark 8.1.5 (the book stresses no mean-zero is needed
for the `|X_t − X_{t₀}|` forms).

**Proof formalization notes.** Book constant `C` frozen to `6√3` for the
mean-zero form: per level, the increment MGF bridge (B2 normalization
`C = 3`) gives each close-pair increment variance proxy `3·(3K·2^{−k})²`,
the pair count over `closePairs` is `≤ N_k²`, and
`expectation_max_finset_le` yields per-level cost
`√(3·(3K·2^{−k})²)·√(2·log N_k²) = 6√3·K·2^{−k}·√(log N_k)`; summing gives
`6√3·K·dudleySum`. (The per-link radius is `ε_k + ε_{k−1} = 3·2^{−k}`,
sharper than the book's rounding to `4·2^{−k}`.) The abs form re-anchors the
chain at the finest scale `κ'` with covering number `1` (so every window
level has `N_k ≥ 2`, killing spurious `√log 2` terms) and reconnects `t₀` by
ONE first-moment bound `E|X_{t₀'} − X_{t₀}| ≤ √π·K·diam T`
(`integral_abs_le_of_subGaussianNorm_le`), absorbed via
`diam·√log2 ≤ 4·dudleySum`; total frozen to `20` (`6√3 ≈ 10.4` chaining +
`4√π/√log 2 ≈ 8.52` re-anchoring, with slack). The mean-zero form carries
the LEAN-ONLY hypothesis `hint : ∀ t ∈ T, Integrable (X t) μ` ruling out
Bochner-junk means (a non-integrable `X t` satisfies `∫ X t = 0` vacuously);
increment means are then derived. The pseudometric chain end is identified
a.e. via `ae_eq_zero_of_subGaussianNorm_eq_zero` over the finitely many
points. Named-sorry fallback of this work item: `discrete_dudley_abs`
(the mean-zero headline `discrete_dudley` lands first).

**Bibliographic comments.** Dudley's bound is from R. M. Dudley, "The sizes
of compact subsets of Hilbert space and continuity of Gaussian processes,"
*J. Funct. Anal.* 1 (1967), 290–330 (for Gaussian processes; the
sub-gaussian extension is folklore). The dyadic discrete form as the primary
statement follows HDP §8.1. See the HDP Chapter 8 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **Discrete Dudley inequality, mean-zero form** (HDP §8.1, Theorem 8.1.4,
Eq. (8.2)): `E sup_{t ∈ T} X_t ≤ 6√3 · K · dudleySum T`. Book's unnamed
absolute constant `C` frozen to `6√3` (see file notes for the derivation). -/
theorem discrete_dudley {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG, HDP p.224 / p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ) :
    ∫ ω, ⨆ t ∈ T, X t ω ∂μ ≤ 6 * Real.sqrt 3 * K * dudleySum T := by sorry

/-- **Discrete Dudley inequality, absolute form** (HDP §8.1, Remark 8.1.5,
discrete): `E sup_{t ∈ T} |X_t − X_{t₀}| ≤ 20 · K · dudleySum T`, with NO
mean-zero hypothesis (as the book stresses for Eq. (8.13)). Book constant
frozen to `20` (`6√3` chaining + `4√π/√log 2` re-anchoring, slack). -/
theorem discrete_dudley_abs {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG, HDP p.224 / p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Remark 8.1.5
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ ≤ 20 * K * dudleySum T := by sorry

/-- Integrability of the anchored supremum, exported for `Chaining/Dudley.lean`
and the countable lift (derived from the increment tails, never
hypothesized). -/
lemma integrable_biSup_sub {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (finite sup domination)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    MeasureTheory.Integrable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ := by sorry

end StatLean.ConcentrationInequalities
