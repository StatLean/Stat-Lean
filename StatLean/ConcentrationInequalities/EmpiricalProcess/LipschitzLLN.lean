import StatLean.ConcentrationInequalities.EmpiricalProcess.Defs
import StatLean.ConcentrationInequalities.EmpiricalProcess.LipschitzCovering
import StatLean.ConcentrationInequalities.EmpiricalProcess.SubGaussianIncrements
import StatLean.ConcentrationInequalities.EmpiricalProcess.LipschitzDense
import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
import StatLean.ConcentrationInequalities.Chaining.DudleyConsumers

/-!
# The Lipschitz law of large numbers — Theorem 8.2.3, assembly

For i.i.d. $X_1, \dots, X_n$ with values in $[0,1]$ and common law $P$, the
empirical process is uniformly small over the **genuine full** $L$-Lipschitz
class:
$$ \mathbb{E} \sup_{\|f\|_{\mathrm{Lip}} \le L}
   \Bigl| \frac{1}{n} \sum_{i=1}^{n} f(X_i) - \mathbb{E}_P f \Bigr|
   \;\le\; \frac{C L}{\sqrt{n}}, \qquad C = 960. $$
No countability hypothesis appears: the supremum inside the expectation is
over the uncountable subtype $\{f : [0,1] \to \mathbb{R} \,\|\,
\|f\|_{\mathrm{Lip}} \le L\}$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2, Theorem 8.2.3 (book constant $C$ unnamed)
and Eq. (8.25).

**Proof formalization notes.** **Frozen constant `lipschitzLLNConst = 960`**,
coherent along both derivations: (i) the design formula
$\bigl(\int_0^1 \sqrt{24/\varepsilon}\, d\varepsilon\bigr) \cdot
C_{\mathrm{Dudley}} \cdot C_{\mathrm{B3}} = 4\sqrt{6} \cdot 40 \cdot \sqrt{6}
= 960$ (entropy integral $2\sqrt{24} = 4\sqrt 6$; `dudley_inequality_abs`
constant $40$; Orlicz-B3 carrier $\sqrt 6$), and (ii) the committed proof
route, the chaining cluster's packaged plug `dudley_abs_of_cov_le_exp_div`
at $80\,K\sqrt{C D}$ with increment constant $K = \sqrt{6}/\sqrt{n}$
(× $L$ after R1), entropy exponent $C = 24$, diameter cap $D = 1$:
$80 \cdot \sqrt 6 \cdot \sqrt{24} = 80 \cdot 12 = 960$. Assembly: per-`m`
finite Dudley bound on `T = lipschitzNetUnion m` with base point
`0 ∈ T` (`zero_mem_lipschitzNet`) and the `24/ε` majorant
(`log_toNat_coveringNumber_subset_le`); monotone-convergence E-sup lift
(`integral_tendsto_of_tendsto_of_monotone` + `tendsto_atTop_ciSup` +
`aestronglyMeasurable_of_tendsto_ae`, uniform-in-`m` bound `2` for the
integrand); then the pointwise R3/R2/R1 rewrites of `LipschitzDense.lean`
under the integral. The chaining theorems' integrability hypothesis
(`hint`, LEAN-ONLY Bochner-junk guard) and the increment mean-zero
hypotheses are **derived in the proof** (bounded process + probability
measures + `integral_empiricalProcess`), never exported — no hypothesis
laundering; the headline hypotheses are exactly the book's: independence,
common law on `[0,1]` (codomain type), `n ≥ 1` (`[NeZero n]`), plus
LEAN-ONLY per-index measurability. Edge behavior: `L = 0` holds via the
degenerate lemma `iSup_abs_empiricalProcess_lipZero_eq` (both sides `0` and
`0 ≤ 0`). Named-sorry fallback of the work item `hdp-emp-lln`:
`expectation_sup'_netUnion_le` (the single point of contact with the
chaining Dudley interface).

**Bibliographic comments.** Theorem 8.2.3 is a quantitative mean
Glivenko–Cantelli / Wasserstein-1 law of large numbers; the $n^{-1/2}$ rate
for the Lipschitz class on $[0,1]$ traces to R. M. Dudley, "The speed of
mean Glivenko–Cantelli convergence," *Ann. Math. Statist.* 40 (1969), 40–50;
the uniform-LLN framework is Vapnik–Chervonenkis (1971) and the chaining
route is Dudley (1967); see HDP §8 Notes and Remark 8.2.6 (Wasserstein
reading).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {P : Measure unitInterval} {n : ℕ} {X : Fin n → Ω → unitInterval}

/-- **The Theorem 8.2.3 constant** (HDP §8.2; the book's `C` is unnamed).
Frozen numeral `960`; formula `4√6 · 40 · √6` (entropy integral
`∫₀¹ √(24/ε) dε = 4√6` × `dudley_inequality_abs` constant `40` × Orlicz-B3
carrier `√6`), equivalently `80 · √6 · √24` via the packaged plug
`dudley_abs_of_cov_le_exp_div` (`80·K·√(C·D)` at `K = √6/√n`, `C = 24`,
`D = 1`). -/
noncomputable def lipschitzLLNConst : ℝ := 960

/-- **Per-`m` finite Dudley bound** (HDP §8.2, Eq. (8.25)): the expected
maximum of `|X_g|` over the exhaustion stage `lipschitzNetUnion m` is at most
`960/√n`, uniformly in `m` — the chaining plug `dudley_abs_of_cov_le_exp_div`
at base point `0 ∈ T`, entropy majorant `24/ε`, diameter cap `1`, increment
constant `√6/√n`. Single point of contact with the chaining Dudley interface;
named-sorry fallback of `hdp-emp-lln`. -/
theorem expectation_sup'_netUnion_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n]
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data on [0,1]; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) (m : ℕ) :
    ∫ ω, (lipschitzNetUnion m).sup' (lipschitzNetUnion_nonempty m)
        (fun g => |empiricalProcess P n X ⇑g ω|) ∂μ
      ≤ lipschitzLLNConst / Real.sqrt n := by
  sorry

/-- **E-sup over the class (8.24)** (HDP §8.2): monotone-convergence lift of
the per-`m` bound along the R3 identity — the genuine uncountable supremum
enters the Bochner integral (integrand measurable as a monotone limit,
bounded by `2`). -/
theorem expectation_sup_lipschitzUnitClass_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n]
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data on [0,1]; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    ∫ ω, (⨆ f : lipschitzUnitClass,
        |empiricalProcess P n X (⇑(f : C(unitInterval, ℝ))) ω|) ∂μ
      ≤ lipschitzLLNConst / Real.sqrt n := by
  sorry

/-- **Theorem 8.2.3 (Lipschitz law of large numbers), HEADLINE** (HDP §8.2):
for i.i.d. `X₁, …, Xₙ` with values in `[0,1]` and common law `P`,
`E sup_{‖f‖_Lip ≤ L} |n⁻¹ ∑ f(Xᵢ) − E_P f| ≤ 960·L/√n` — over the genuine
full `L`-Lipschitz class, no countability hypothesis. Book constant unnamed;
ours frozen at `lipschitzLLNConst = 960`. `L = 0` is included (degenerate
case). -/
theorem lipschitz_lln {L : ℝ≥0} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n]
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data on [0,1] (codomain type); HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    ∫ ω, (⨆ f : {f : unitInterval → ℝ // LipschitzWith L f},
        |empiricalProcess P n X (↑f) ω|) ∂μ
      ≤ lipschitzLLNConst * (L : ℝ) / Real.sqrt n := by
  sorry

end StatLean.ConcentrationInequalities
