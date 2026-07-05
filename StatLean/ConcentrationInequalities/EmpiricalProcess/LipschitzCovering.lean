import StatLean.ConcentrationInequalities.EmpiricalProcess.LipschitzNet
import StatLean.ConcentrationInequalities.EmpiricalProcess.LipschitzApprox
import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Covering numbers of the Lipschitz class — Exercise 8.9, assembly

The covering-number bound for the class $\mathcal{F}$ of HDP Eq. (8.24):
$$ N(\mathcal{F}, L^\infty, \varepsilon) \;\le\; e^{12/\varepsilon}
   \qquad (0 < \varepsilon < 1), \qquad
   N(\mathcal{F}, L^\infty, \varepsilon) = 1 \quad (\varepsilon \ge 1), $$
together with the Dudley-facing *uniform* entropy majorants for arbitrary
subsets $T \subseteq \mathcal{F}$ (radius-halving forced by the internal
covering convention):
$$ \log N(T, L^\infty, \varepsilon) \;\le\; \frac{24}{\varepsilon}
   \qquad (0 < \varepsilon < 1). $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2, Exercise 8.9 (the book's bound is
$e^{C/\varepsilon}$ with $C$ unnamed) and p. 231 (entropy input to Eq. (8.25)).

**Proof formalization notes.** Frozen constant $C = 12$, from
$m := \lceil 3/\varepsilon \rceil_{\mathbb{N}}$ and
$\log((m+1)\,3^m) = \log(m+1) + m \log 3 \le m + 2m = 3m \le 12/\varepsilon$,
using `Real.add_one_le_exp` ($m + 1 \le e^m$), $\log 3 \le 2$ (from $3 < e^2$,
`Real.exp_one_gt_d9`), and $m \le 3/\varepsilon + 1 \le 4/\varepsilon$ for
$\varepsilon < 1$. Documented sharpening (NOT committed): $C = 9$ via
$3^8 = 6561 \le e^9$, i.e. $\log 3 \le 9/8$. The subset majorant doubles the
exponent to $24/\varepsilon$ because internal covering numbers are not
`⊆`-monotone: `Metric.coveringNumber_subset_le` costs a factor `2` in the
radius. Class-level exports are in `toNat` shape
(`((coveringNumber …).toNat : ℝ) ≤ exp(12/ε)`), matching the chaining
cluster's `sqrtLogCov` integrand carrier; `ne_top` lemmas make `toNat`
lossless and settle, for our sets, the chaining cluster's
totally-bounded-⇒-finite side condition. Edge behavior: for $\varepsilon \ge 1$
the covering number is exactly `1` (diameter cap, nonempty class). Named-sorry
fallback of the work item `hdp-emp-cover`: `card_lipschitzNet_le_exp` (the
arithmetic step; the `ℕ∞` covering chain closes modulo it).

**Bibliographic comments.** The $e^{\Theta(1/\varepsilon)}$ entropy of
Lipschitz balls on $[0,1]$ is due to Kolmogorov–Tikhomirov (1959); the
uniform-entropy input to Dudley's bound follows R. M. Dudley, "The sizes of
compact subsets of Hilbert space and continuity of Gaussian processes,"
*J. Funct. Anal.* 1 (1967), 290–330; see HDP §8 Notes.
-/

open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

/-- Subsets cost a factor `2` in radius (LEAN-ONLY `ℝ`-radius wrapper of
`Metric.coveringNumber_subset_le`; internal covering numbers are not
`⊆`-monotone, so this is the correct monotonicity surrogate). -/
theorem coveringNumber_le_of_subset_half {Y : Type*} [PseudoMetricSpace Y]
    {T s : Set Y}
    -- LEAN-ONLY: inclusion into the covered superset; no book content
    (hTs : T ⊆ s) {ε : ℝ}
    -- LEAN-ONLY: nonnegative radius (aligns `Real.toNNReal` clamping); no book content
    (hε : 0 ≤ ε) :
    coveringNumber T ε ≤ coveringNumber s (ε / 2) := by
  sorry

/-- `log 3 ≤ 2` (LEAN-ONLY numeric brick: `3 < e²` from `Real.exp_one_gt_d9`). -/
theorem log_three_le_two : Real.log 3 ≤ 2 := by
  sorry

/-- Net-cardinality arithmetic (HDP Exercise 8.9): for any mesh `m` with
`3/ε ≤ m ≤ 4/ε` (in particular `m = ⌈3/ε⌉₊` when `0 < ε < 1`),
`(m+1)·3^m ≤ e^{12/ε}`. Named-sorry fallback of `hdp-emp-cover`.
Frozen constant `12 = 3·4`; docstring records the uncommitted `C = 9`
sharpening via `3^8 ≤ e^9`. -/
theorem card_lipschitzNet_le_exp {ε : ℝ}
    -- USER-INPUT: radius window of Exercise 8.9; HDP Exercise 8.9
    (hε₀ : 0 < ε) (hε₁ : ε < 1) {m : ℕ} [NeZero m]
    -- LEAN-ONLY: mesh window making the count ≤ e^{12/ε}; instantiated at m = ⌈3/ε⌉₊
    (hm₁ : 3 / ε ≤ (m : ℝ)) (hm₂ : (m : ℝ) ≤ 4 / ε) :
    ((lipschitzNet m).card : ℝ) ≤ Real.exp (12 / ε) := by
  sorry

/-- **Exercise 8.9, headline export (toNat shape)**:
`N(𝓕, L∞, ε) ≤ e^{12/ε}` for `0 < ε < 1` (book: `e^{C/ε}`, `C` unnamed; ours
`C = 12`). Stated on `(coveringNumber …).toNat` cast to `ℝ`, the carrier of
the chaining cluster's `sqrtLogCov` integrand; lossless by
`coveringNumber_lipschitzUnitClass_ne_top`. -/
theorem coveringNumber_lipschitzUnitClass_toNat_le {ε : ℝ}
    -- USER-INPUT: radius window of Exercise 8.9; HDP Exercise 8.9
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    (((coveringNumber lipschitzUnitClass ε).toNat : ℕ) : ℝ) ≤ Real.exp (12 / ε) := by
  sorry

/-- The Lipschitz class is totally bounded at every positive radius: its
covering number is finite (LEAN-ONLY finiteness; makes the `toNat` exports
lossless and discharges, for this class, the chaining cluster's
`TotallyBounded ⇒ finite-covering` side condition). -/
theorem coveringNumber_lipschitzUnitClass_ne_top {ε : ℝ}
    -- USER-INPUT: positive radius; HDP Exercise 8.9
    (hε₀ : 0 < ε) :
    coveringNumber lipschitzUnitClass ε ≠ ⊤ := by
  sorry

/-- Above the diameter the covering number collapses: `N(𝓕, L∞, ε) = 1` for
`ε ≥ 1` (HDP §8.1 Remark 8.1.7; the entropy integral is capped at
`diam 𝓕 ≤ 1`). -/
theorem coveringNumber_lipschitzUnitClass_eq_one {ε : ℝ}
    -- USER-INPUT: radius at or above the class diameter; HDP §8.1 Remark 8.1.7
    (hε : 1 ≤ ε) :
    coveringNumber lipschitzUnitClass ε = 1 := by
  sorry

/-- Finiteness for arbitrary subsets `T ⊆ 𝓕` (LEAN-ONLY; via
`coveringNumber_le_of_subset_half` and the class-level finiteness at `ε/2`). -/
theorem coveringNumber_subset_lipschitzUnitClass_ne_top
    {T : Set C(unitInterval, ℝ)}
    -- USER-INPUT: subset of the Lipschitz class; HDP §8.2 p. 231
    (hT : T ⊆ lipschitzUnitClass) {ε : ℝ}
    -- USER-INPUT: positive radius; HDP §8.2 p. 231
    (hε₀ : 0 < ε) :
    coveringNumber T ε ≠ ⊤ := by
  sorry

/-- **Uniform entropy majorant, exponential shape** (HDP §8.2 p. 231): for
any `T ⊆ 𝓕` and `0 < ε < 1`, `N(T, L∞, ε) ≤ e^{24/ε}` — the factor `2` in
the exponent is the radius-halving cost of `⊆`-monotonicity. `toNat` carrier
per the chaining interface. -/
theorem coveringNumber_subset_toNat_le_exp {T : Set C(unitInterval, ℝ)}
    -- USER-INPUT: subset of the Lipschitz class (the finite Dudley sets); HDP §8.2 p. 231
    (hT : T ⊆ lipschitzUnitClass) {ε : ℝ}
    -- USER-INPUT: radius window; HDP §8.2 p. 231
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    (((coveringNumber T ε).toNat : ℕ) : ℝ) ≤ Real.exp (24 / ε) := by
  sorry

/-- **Uniform entropy majorant, log shape** (Dudley-integrand form; HDP §8.2
p. 231): `log N(T, L∞, ε) ≤ 24/ε` for `T ⊆ 𝓕`, `0 < ε < 1`. Matches the
chaining cluster's `sqrtLogCov` integrand `Real.log ((coveringNumber T ε).toNat)`. -/
theorem log_toNat_coveringNumber_subset_le {T : Set C(unitInterval, ℝ)}
    -- USER-INPUT: subset of the Lipschitz class; HDP §8.2 p. 231
    (hT : T ⊆ lipschitzUnitClass) {ε : ℝ}
    -- USER-INPUT: radius window; HDP §8.2 p. 231
    (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    Real.log (((coveringNumber T ε).toNat : ℕ) : ℝ) ≤ 24 / ε := by
  sorry

/-- Entropy vanishes above the diameter for subsets: `N(T, L∞, ε) = 1` for
nonempty `T ⊆ 𝓕` and `ε ≥ 1` (via `Metric.coveringNumber_eq_one_of_ediam_le`;
caps the Dudley integral at `D = 1`). -/
theorem coveringNumber_subset_eq_one_of_one_le {T : Set C(unitInterval, ℝ)}
    -- USER-INPUT: subset of the Lipschitz class; HDP §8.2 p. 231
    (hT : T ⊆ lipschitzUnitClass)
    -- LEAN-ONLY: nonemptiness (the empty set has covering number 0); no scope change
    (hne : T.Nonempty) {ε : ℝ}
    -- USER-INPUT: radius at or above the class diameter; HDP §8.1 Remark 8.1.7
    (hε : 1 ≤ ε) :
    coveringNumber T ε = 1 := by
  sorry

end StatLean.ConcentrationInequalities
