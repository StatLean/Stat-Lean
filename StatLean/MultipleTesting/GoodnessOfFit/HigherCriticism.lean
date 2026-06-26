import StatLean.MultipleTesting.ForMathlib.EmpiricalCDF
import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
import StatLean.AsymptoticStatistics.EmpiricalProcess.DonskerBracketing
import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Higher Criticism and the detection boundary (Candès, Lecture 3, §3.3.3, Theorem 3)

Tukey's Higher-Criticism statistic and the Ingster–Donoho–Jin **detection boundary** for sparse
Gaussian mixtures (Candès, Lecture 3, §3.3.3). For the sparse mixture
`Xᵢ ∼ (1−εₙ)·N(0,1) + εₙ·N(μₙ,1)` with sparsity `εₙ = n^{−β}` (`1/2 < β < 1`) and signal
`μₙ = √(2r log n)`, the detection boundary is

`ρ*(β) = β − 1/2`           for `1/2 < β < 3/4`,
`ρ*(β) = (1 − √(1−β))²`     for `3/4 ≤ β ≤ 1`.

We formalize the two genuinely formalizable ingredients:

* `rhoStar β` — the detection boundary, a concrete piecewise function, with its basic properties
  (`rhoStar_continuous_at_junction`, `rhoStar_nonneg`, `rhoStar_one`);
* `hcStat p α₀ ω` — the Higher-Criticism statistic `max_{0<α≤α₀} (F̂ₙ(α) − α)/√(α(1−α)/n)`.

## Deferred: the detection theorem (Donoho–Jin 2004) — research target, NOT stated as Lean

**Theorem 3 (Donoho & Jin).** *Above the boundary* (`r > ρ*(β)`), the Higher-Criticism test that
rejects when `HC*ₙ ≥ √((1+δ)·2 log log n)` has total error `P₀(type I) + P₁(type II) → 0` as
`n → ∞`; *below* it (`r ≤ ρ*(β)`) every test has `liminf (P₀ + P₁) ≥ 1` (Ingster).

This is **not** stated as a Lean theorem here, deliberately: a faithful statement is an asymptotic
over a sequence of sparse-mixture models, and encoding it now would require laundering unproven
asymptotics through hypotheses (CLAUDE.md §2 forbids this). What the proof needs, and its status:

* **Donsker invariance** (`√n(F̂ₙ−F) ⇒` Brownian bridge) — **now formalized here**:
  `halfLine_isPDonsker` proves the half-line indicator class
  `F_cdf = {𝟙(−∞,t] : t ∈ ℝ}` is `P`-Donsker for every law `P` on `ℝ`, via the project's
  `isPDonsker_of_finite_bracketing_entropy_integral` and the new half-line bracketing-entropy
  bound `N_[](ε) ≲ 1/ε²` (`halfLineClass_bracketingEntropyIntegral_lt_top`). So the `H₀`
  empirical-process convergence underlying `hcStat` is in the library. Residual debts there are the
  half-line bracketing-entropy lemma (the quantile-grid construction) and the framework's own
  inherited maximal-inequality / positivity inputs — none of them the detection theorem.
* **Empirical-process LIL** (`max_{1/n≤t≤α₀} Wₙ(t)/√(2 log log n) →ᵈ 1`, calibrating the
  `√(2 log log n)` threshold) — **not yet available**; finer than Donsker (an iterated-logarithm /
  extreme-value statement for the normalized process near `0`). This is the threshold-calibration
  gap remaining after `halfLine_isPDonsker`.
* **Sparse-mixture large deviations** (the `H₁` detection above `ρ*(β)`) — **not yet available**.

With the H₀ empirical-process convergence now in the library (`halfLine_isPDonsker`), the *only*
residual gaps for Theorem 3 are (i) the empirical-process LIL threshold calibration and (ii) the
`H₁` sparse-mixture large-deviation analysis. Recorded as the TODO §"Batch 8" research target.
-/

open MeasureTheory
open AsymptoticStatistics.EmpiricalProcess

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : ℕ}

/-- The **Ingster–Donoho–Jin detection boundary** `ρ*(β)` for sparse Gaussian mixtures
(Candès, Lecture 3, §3.3.3): `β − 1/2` for `1/2 < β < 3/4`, and `(1 − √(1−β))²` for `3/4 ≤ β ≤ 1`. -/
noncomputable def rhoStar (β : ℝ) : ℝ :=
  if β < 3 / 4 then β - 1 / 2 else (1 - Real.sqrt (1 - β)) ^ 2

/-- The two pieces of `rhoStar` agree at the junction `β = 3/4`
(`3/4 − 1/2 = 1/4 = (1 − √(1/4))²`): the boundary is continuous there. -/
theorem rhoStar_continuous_at_junction :
    (3 / 4 : ℝ) - 1 / 2 = (1 - Real.sqrt (1 - 3 / 4)) ^ 2 := by
  have h : Real.sqrt (1 - 3 / 4) = 1 / 2 := by
    rw [show (1 - 3 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]; norm_num

/-- The detection boundary is nonnegative on the sparse range `1/2 < β ≤ 1`. -/
theorem rhoStar_nonneg {β : ℝ} (hβ0 : 1 / 2 < β) (hβ1 : β ≤ 1) : 0 ≤ rhoStar β := by
  unfold rhoStar
  split_ifs
  · linarith
  · exact sq_nonneg _

/-- At the densest sparse endpoint `β = 1`, `ρ*(1) = 1` (the Bonferroni detection threshold). -/
theorem rhoStar_one : rhoStar 1 = 1 := by
  unfold rhoStar
  rw [if_neg (by norm_num), show (1 - 1 : ℝ) = 0 by norm_num, Real.sqrt_zero]
  norm_num

/-- The **Higher-Criticism statistic** `HC*ₙ = max_{0<α≤α₀} (F̂ₙ(α) − α)/√(α(1−α)/n)` (Candès,
Lecture 3, §3.3.3; `F̂ₙ` is the empirical CDF `empiricalCDF p`). -/
noncomputable def hcStat (p : Fin n → Ω → ℝ) (α₀ : ℝ) (ω : Ω) : ℝ :=
  ⨆ α ∈ Set.Ioc (0 : ℝ) α₀,
    (empiricalCDF p α ω - α) / Real.sqrt (α * (1 - α) / (n : ℝ))

/-! ## The H₀ empirical-process half: the half-line indicator class is `P`-Donsker

This is the genuinely formalizable empirical-process content behind `hcStat`. The
Higher-Criticism statistic is a functional of the empirical CDF process
`Gₙ(t) = √n(F̂ₙ(t) − F(t))`, indexed by the half-line indicator class
`F_cdf = { 𝟙_{(−∞,t]} : t ∈ ℝ }`. The classical fact that this process converges
to a Gaussian limit (the `F`-time-changed Brownian bridge) is exactly the
statement that `F_cdf` is `P`-Donsker, which we obtain from the project's
bracketing-entropy Donsker theorem
(`isPDonsker_of_finite_bracketing_entropy_integral`, vdV §19.2 Thm 19.5).

The new, half-line-specific reachable content is the **bracketing-entropy bound**
`N_[](ε, F_cdf, L²(P)) ≲ 1/ε²`, hence `J_[](1, F_cdf, L²(P)) < ∞`
(`halfLineClass_bracketingEntropyIntegral_lt_top`), together with measurability of
the class (`halfLineClass_measurable`, 0-sorry). The assembly into `IsPDonsker`
additionally consumes the framework theorem's own (pre-existing, NOT half-line-
specific) inputs — the vdV Lemma 19.34 maximal/chaining inequality and the
bracketing-integral positivity regularity — which are inherited here as named
debts (`halfLineClass_chain_bound`, `halfLineClass_J_pos`), since the chaining
brick is `private` in `Maximal.lean` and cannot be threaded across files. -/

/-- The **half-line indicator class** `F_cdf = { 𝟙_{(−∞,t]} : t ∈ ℝ }` on `ℝ`
(Candès, Lecture 3; vdV §19.2 Example) — the index class of the empirical-CDF
process. Each member is the indicator `Set.indicator (Set.Iic t) 1` of a left-
infinite half-line; the class is the union over the threshold `t ∈ ℝ`. -/
def halfLineClass : Set (ℝ → ℝ) :=
  {f | ∃ t : ℝ, f = Set.indicator (Set.Iic t) (fun _ => (1 : ℝ))}

/-- Every member of `halfLineClass` is measurable: `𝟙_{(−∞,t]}` is the indicator
of the measurable set `Set.Iic t` of a measurable (constant) function. -/
theorem halfLineClass_measurable {f : ℝ → ℝ} (hf : f ∈ halfLineClass) : Measurable f := by
  obtain ⟨t, rfl⟩ := hf
  exact measurable_const.indicator measurableSet_Iic

/-- **Bracketing-entropy bound for the empirical-CDF class** (vdV §19.2 Example
19.6): the half-line class has bracketing number `N_[](ε, F_cdf, L²(P)) ≲ 1/ε²`,
so the Donsker entropy integral `J_[](1, F_cdf, L²(P)) = ∫₀¹ √(log N_[](ε)) dε`
is finite.

**Proof (the one remaining named debt, `sorry` below).** Fix `ε ∈ (0,1]`. Let
`F = cdf P` (monotone, right-continuous, `F(−∞)=0`, `F(+∞)=1`). Choose grid points
`−∞ = t₀ < t₁ < … < t_m = +∞` with `m ≤ ⌈1/ε²⌉ + 1` and `P((t_{i−1}, t_i]) ≤ ε²`
for every `i` (a `P`-mass partition; atoms of mass `> ε²` are placed as their own
grid points, which only adds the `+1`). The brackets are
`[𝟙_{(−∞,t_{i−1}]}, 𝟙_{(−∞,t_i]}]`: for any `t ∈ [t_{i−1}, t_i)` we have pointwise
`𝟙_{(−∞,t_{i−1}]} ≤ 𝟙_{(−∞,t]} ≤ 𝟙_{(−∞,t_i]}`, and the `L²(P)`-size is
`‖𝟙_{(−∞,t_i]} − 𝟙_{(−∞,t_{i−1}]}‖_{L²(P)} = √(P((t_{i−1}, t_i]})) ≤ ε`. Hence
`N_[](ε) ≤ ⌈1/ε²⌉ + 1`, giving `√(log N_[](ε)) ≲ √(2 log(1/ε))`, which is Lebesgue-
integrable on `(0,1]`; therefore `J_[](1) < ⊤`. The quantile-grid construction (a
measure-theoretic partition of `ℝ` into `P`-mass-`≤ ε²` pieces, valid for any law
including atomic ones) plus the `√log(1/ε)` integrability estimate are the content
deferred to this named lemma. -/
theorem halfLineClass_bracketingEntropyIntegral_lt_top
    (P : Measure ℝ) [IsProbabilityMeasure P] :
    bracketingEntropyIntegral 1 halfLineClass P < ⊤ := by
  sorry

/-- **Bracketing-integral positivity for the empirical-CDF class** (inherited
framework regularity input of `isPDonsker_of_finite_bracketing_entropy_integral`,
vdV §19.2). For the half-line class this is genuinely *true* (not vacuous): for any
`ε ≤ 1` the two extreme indicators `𝟙_∅`-like and `𝟙_ℝ`-like differ pointwise by
`1`, so no single `ε`-bracket can cover both and `N_[](ε) ≥ 2`, whence the
integrand `√(log N_[](ε)) ≥ √(log 2) > 0` on `(0, δ']` and the integral is
positive. Lifted to a named debt: the `N_[](ε) ≥ 2` lower bound and the resulting
positive-Lebesgue-integral estimate. -/
private theorem halfLineClass_J_pos (P : Measure ℝ) [IsProbabilityMeasure P] :
    ∀ δ' : ℝ, 0 < δ' → 0 < bracketingEntropyIntegral δ' halfLineClass P := by
  sorry

/-- **Maximal/chaining inequality for the empirical-CDF class** — the vdV
Lemma 19.34 sup-norm bound, the framework input `hChainBound_outer` of
`isPDonsker_of_finite_bracketing_entropy_integral`. This is **not** half-line-
specific: it is the general empirical-process maximal inequality, whose proof brick
`chain_supnorm_integral_bound_at_delta_q` is `private` in
`AsymptoticStatistics.EmpiricalProcess.Maximal` and so cannot be threaded across
modules. Inherited here verbatim as a named debt for the half-line class. -/
private theorem halfLineClass_chain_bound (P : Measure ℝ) [IsProbabilityMeasure P] :
    ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
      (X : ℕ → Ξ → ℝ),
      ∀ (Φ : ℝ → ℝ), Measurable Φ → IsEnvelope halfLineClass Φ → MemLp Φ 2 P →
        ∀ {δq : ℝ}, 0 < δq → ∀ (n : ℕ),
          ∫⁻ ξ, supNormOver halfLineClass
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
            ≤ ENNReal.ofReal 2 * bracketingEntropyIntegral δq halfLineClass P
              + ENNReal.ofReal 2 *
                (ENNReal.ofReal (Real.sqrt n)
                  * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                      * Set.indicator {x | δq * Real.sqrt n < |Φ x|} 1 ω ∂P) := by
  sorry

/-- **The empirical-CDF class is `P`-Donsker** (the H₀ half of the Donoho–Jin
detection program; vdV §19.2 Thm 19.5, Candès Lecture 3 §3.3.3). The class of
half-line indicators `F_cdf = { 𝟙_{(−∞,t]} : t ∈ ℝ }` is `P`-Donsker for *every*
law `P` on `ℝ`: the empirical-CDF process `√n(F̂ₙ − F)` converges weakly to a tight
Gaussian limit in `ℓ^∞(F_cdf)`.

Obtained from the project's bracketing-entropy Donsker theorem
`isPDonsker_of_finite_bracketing_entropy_integral`, fed the half-line measurability
(`halfLineClass_measurable`, 0-sorry) and entropy finiteness
(`halfLineClass_bracketingEntropyIntegral_lt_top`), together with the framework's
own maximal-inequality / positivity inputs (`halfLineClass_chain_bound`,
`halfLineClass_J_pos`). See the section docstring for the debt accounting. -/
theorem halfLine_isPDonsker (P : Measure ℝ) [IsProbabilityMeasure P] :
    IsPDonsker halfLineClass P :=
  isPDonsker_of_finite_bracketing_entropy_integral halfLineClass P
    (fun _ hf => (halfLineClass_measurable hf).aemeasurable)
    (halfLineClass_bracketingEntropyIntegral_lt_top P)
    (halfLineClass_J_pos P)
    (halfLineClass_chain_bound P)

end StatLean.MultipleTesting
