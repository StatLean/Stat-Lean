import StatLean.MultipleTesting.ForMathlib.EmpiricalCDF
import StatLean.MultipleTesting.ForMathlib.OptionalStopping
import StatLean.MultipleTesting.FDP.Defs
import StatLean.MultipleTesting.PValues.Defs

/-!
# Storey's q-value procedure — FDR control (Candès, Lecture 7, §7.4, Theorem 3)

Storey's adaptive procedure estimates the null proportion and thresholds the p-values on `[0,1/2]`.
With the rejection count `R(t) = countLE p t` and false-rejection count `V(t) = nullCountLE H₀ p t`:

* `storeyPiZero` — the null-proportion estimate `π̂₀ = (1 + n − R(1/2)) / (n/2)` (the `+1` keeps the
  martingale denominator strictly positive — see the proof);
* `storeyFDRhat q t` — the estimated FDR `π̂₀ · n t / (R(t) ∨ 1)`;
* `storeyThreshold q` — `τ = sup{ t ≤ 1/2 : storeyFDRhat q t ≤ q }`;
* `storeyRejects q` — reject `{ i : pᵢ ≤ τ }`.

**Main result** (`storey_fdr_le`, Candès L7 §7.4, Theorem 3): for independent uniform null p-values,
`FDR ≤ q`.

*Proof.* By the definition of `τ`, `FDP(τ) = q · V(τ)/τ · (1/2)/(1+n₀−V(1/2))`; Doob's optional
stopping on the backwards martingale `{V(t)/t}` over `[0,1/2]` gives
`E[V(τ)/τ] = E[V(1/2)/(1/2)]`, whence `E[FDP(τ)] ≤ q · E[V(1/2)/(1+n₀−V(1/2))] = q·(1−2^{−n₀}) ≤ q`
(the binomial identity, `V(1/2) ∼ Bin(n₀,1/2)`). The optional-stopping step
(`storey_reverseMG_ost`) is the genuinely martingale-theoretic ingredient — the uniform-null
backwards-martingale property, for which Mathlib has no continuous-time backwards-martingale support
— and is recorded here as a documented named `sorry`; the binomial identity reuses
`ForMathlib/BinomialRatio`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {n : ℕ}

/-- Storey's null-proportion estimate `π̂₀ = (1 + n − R(1/2)) / (n/2)` (Candès L7 §7.4). -/
noncomputable def storeyPiZero (p : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  (1 + (n : ℝ) - (countLE p (1 / 2) ω : ℝ)) / ((n : ℝ) / 2)

/-- Storey's estimated FDR at threshold `t`: `π̂₀ · n t / (R(t) ∨ 1)` (Candès L7 §7.4). -/
noncomputable def storeyFDRhat (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  storeyPiZero p ω * (n : ℝ) * t / (max (countLE p t ω : ℝ) 1)

/-- Storey's data-dependent threshold `τ = sup{ t ≤ 1/2 : storeyFDRhat q t ≤ q }` (Candès L7 §7.4). -/
noncomputable def storeyThreshold (p : Fin n → Ω → ℝ) (q : ℝ) (ω : Ω) : ℝ :=
  sSup {t : ℝ | t ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ storeyFDRhat p t ω ≤ q}

/-- Storey's rejection set: reject `{ i : pᵢ ≤ τ }` (Candès L7 §7.4). -/
noncomputable def storeyRejects (p : Fin n → Ω → ℝ) (q : ℝ) (ω : Ω) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i ω ≤ storeyThreshold p q ω)

/-- **Backwards-martingale optional stopping for the Storey threshold** (the martingale-theoretic
core of Theorem 3): for independent uniform null p-values, `E[V(τ)/τ] = E[V(1/2)/(1/2)] = 2·E[V(1/2)]`,
where `V(t) = nullCountLE H₀ p t` and `τ = storeyThreshold p q`. This is Doob's optional stopping on
the backwards martingale `{V(t)/t}_{t∈[0,1/2]}`; **documented named `sorry`** — Mathlib lacks
continuous-time backwards-martingale / optional-stopping support, and a faithful discrete
reformulation over the null order statistics (the uniform analogue of the knock-off
`condExp_coord_eq_count_div`) is a self-contained development of its own. -/
theorem storey_reverseMG_ost (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin n))
    (p : Fin n → Ω → ℝ) (q : ℝ)
    -- USER-INPUT: p-values measurable; Candès L7 §7.4
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: independent; Candès L7 §7.4
    (hindep : iIndepFun p μ)
    -- USER-INPUT: each null exactly uniform on [0,1]; Candès L7 §7.4
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    ∫ ω, (nullCountLE H₀ p (storeyThreshold p q ω) ω : ℝ) / storeyThreshold p q ω ∂μ
      = ∫ ω, (nullCountLE H₀ p (1 / 2) ω : ℝ) / (1 / 2) ∂μ := by
  sorry

/-- **Storey's procedure controls FDR** (Candès, Lecture 7, §7.4, Theorem 3, STAT 300C). For
independent uniform null p-values, `FDR ≤ q`. -/
theorem storey_fdr_le (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin n))
    (p : Fin n → Ω → ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    -- USER-INPUT: p-values measurable; Candès L7 §7.4
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: independent; Candès L7 §7.4
    (hindep : iIndepFun p μ)
    -- USER-INPUT: each null exactly uniform on [0,1]; Candès L7 §7.4
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    FDR H₀ (storeyRejects p q) μ ≤ q := by
  sorry

end StatLean.MultipleTesting
