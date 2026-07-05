import StatLean.ConcentrationInequalities.Orlicz.Defs
import StatLean.ConcentrationInequalities.Orlicz.SubGaussianTail
import StatLean.ConcentrationInequalities.Chaining.TailToExpectation

/-!
# ψ₂-norm maximal inequality (no centering)

For $N$ (not necessarily centered, not necessarily independent) random
variables with $\|Y_i\|_{\psi_2} \le L$,
$$ \mathbb{P}\Bigl(\max_{i \le N} |Y_i| > \tau\Bigr) \le 2 N e^{-\tau^2/L^2},
   \qquad
   \mathbb{E}\Bigl[\max_{i \le N} |Y_i|\Bigr] \le 2 L \sqrt{\log(2N)}, $$
together with the first-moment bound $\mathbb{E}|Y| \le \sqrt{\pi}\, L$.
This is the per-level engine for the *no-mean-zero* two-sided chaining forms
(8.13)/(8.14)/(8.15), which the book stresses require no centering.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §2.5, Eq. (2.22) / Exercise 2.5.10 (maximal
inequality in ψ₂-norm), §2.5.2 (moment equivalences).

**Proof formalization notes.** Bridge-B1 consumption
(`measure_abs_ge_le_of_subGaussianNorm_le`, normalization `c = 1`, tail
`2exp(−τ²/L²)`) is confined to this file and to
`Chaining/SubGaussianIncrements.lean`. The route is B1 per-variable tail +
union bound + layer-cake (`Chaining/TailToExpectation.lean`) — deliberately
avoiding centering / ψ₂-norm-of-a-constant lemmas that are outside the frozen
Orlicz interface. Committed constants (book's unnamed absolute constants):
expectation bound `2·L·√(log(2N))` — split the layer cake at
`a = L√(log(2N))`; the Gaussian-tail remainder is
`≤ L/(2√log 2) ≤ 0.74·L√(log(2N))`, slack to the frozen numeral `2`. First
moment: `E|Y| ≤ ∫₀^∞ 2exp(−t²/L²) dt = √π·L`, exact. All tail lemmas carry
`[IsProbabilityMeasure μ]` (bridge B1 requires it). Named-sorry fallback of
this work item: `expectation_abs_max_le` (with `tail_abs_max_le` and the
first moment proved; `DudleyTail` needs only the tail form).

**Bibliographic comments.** Maximal inequalities under ψ₂-norm bounds are
folklore consequences of the Cramér–Chernoff method and Orlicz-norm calculus;
systematic treatments are Buldygin–Kozachenko, *Metric Characterization of
Random Variables and Random Processes*, AMS 2000, and van der Vaart–Wellner,
*Weak Convergence and Empirical Processes*, Springer 1996, §2.2 (Orlicz-norm
maximal inequalities). See the HDP Chapter 2 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **ψ₂ maximal inequality — tail bound** (HDP §2.5, Eq. (2.22)): union
bound over the B1 per-variable tails, no centering. -/
theorem tail_abs_max_le {ι : Type*}
    -- USER-INPUT: probability-space context (bridge B1 requires it); HDP §2.5
    [IsProbabilityMeasure μ] {s : Finset ι}
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hs : s.Nonempty) {Y : ι → Ω → ℝ} {L : ℝ≥0}
    -- LEAN-ONLY: nondegenerate scale so the tail RHS is meaningful
    (hL : 0 < L)
    -- LEAN-ONLY: a.e.-measurability, required by the Orlicz bridge B1
    (hm : ∀ i ∈ s, AEMeasurable (Y i) μ)
    -- USER-INPUT: uniform ψ₂-norm bound ‖Y_i‖_{ψ₂} ≤ L; HDP §2.5, Eq (2.22)
    (hY : ∀ i ∈ s, subGaussianNorm (Y i) μ ≤ (L : ℝ≥0∞))
    -- USER-INPUT: τ ≥ 0; HDP §2.5
    {τ : ℝ} (hτ : 0 ≤ τ) :
    μ {ω | τ < ⨆ i ∈ s, |Y i ω|}
      ≤ ENNReal.ofReal (2 * (s.card : ℝ) * Real.exp (-τ ^ 2 / (L : ℝ) ^ 2)) := by sorry

/-- **First moment from the ψ₂-norm** (HDP §2.5.2): layer-cake over the B1
tail, `E|Y| ≤ ∫₀^∞ 2exp(−t²/L²) dt = √π·L` (exact constant). -/
theorem integral_abs_le_of_subGaussianNorm_le
    -- USER-INPUT: probability-space context (bridge B1 requires it); HDP §2.5
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} {L : ℝ≥0}
    -- LEAN-ONLY: a.e.-measurability, required by the Orlicz bridge B1
    (hm : AEMeasurable Y μ)
    -- USER-INPUT: ψ₂-norm bound ‖Y‖_{ψ₂} ≤ L; HDP §2.5.2
    (hY : subGaussianNorm Y μ ≤ (L : ℝ≥0∞)) :
    ∫ ω, |Y ω| ∂μ ≤ Real.sqrt Real.pi * L := by sorry

/-- **ψ₂ maximal inequality — expectation bound** (HDP §2.5, Eq. (2.22)):
`E max|Y_i| ≤ 2·L·√(log(2N))`, no centering. Frozen numeral `2` (split at
`L√(log 2N)`; Gaussian-tail remainder ≤ 0.74·L√(log 2N), see file notes). -/
theorem expectation_abs_max_le {ι : Type*}
    -- USER-INPUT: probability-space context; HDP §2.5
    [IsProbabilityMeasure μ] {s : Finset ι}
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hs : s.Nonempty) {Y : ι → Ω → ℝ} {L : ℝ≥0}
    -- LEAN-ONLY: nondegenerate scale for the split-point optimization
    (hL : 0 < L)
    -- LEAN-ONLY: a.e.-measurability, required by the Orlicz bridge B1
    (hm : ∀ i ∈ s, AEMeasurable (Y i) μ)
    -- USER-INPUT: uniform ψ₂-norm bound ‖Y_i‖_{ψ₂} ≤ L; HDP §2.5, Eq (2.22)
    (hY : ∀ i ∈ s, subGaussianNorm (Y i) μ ≤ (L : ℝ≥0∞)) :
    ∫ ω, ⨆ i ∈ s, |Y i ω| ∂μ
      ≤ 2 * (L : ℝ) * Real.sqrt (Real.log (2 * s.card)) := by sorry

/-- Integrability of the finite maximum of ψ₂-bounded variables, derived from
the tail bound (never hypothesized downstream). -/
lemma integrable_biSup_abs {ι : Type*}
    -- USER-INPUT: probability-space context; HDP §2.5
    [IsProbabilityMeasure μ] {s : Finset ι}
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hs : s.Nonempty) {Y : ι → Ω → ℝ} {L : ℝ≥0}
    -- LEAN-ONLY: a.e.-measurability, required by the Orlicz bridge B1
    (hm : ∀ i ∈ s, AEMeasurable (Y i) μ)
    -- USER-INPUT: uniform ψ₂-norm bound ‖Y_i‖_{ψ₂} ≤ L; HDP §2.5
    (hY : ∀ i ∈ s, subGaussianNorm (Y i) μ ≤ (L : ℝ≥0∞)) :
    MeasureTheory.Integrable (fun ω => ⨆ i ∈ s, |Y i ω|) μ := by sorry

end StatLean.ConcentrationInequalities
