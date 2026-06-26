import StatLean.MultipleTesting.ForMathlib.EmpiricalCDF
import StatLean.MultipleTesting.ForMathlib.OptionalStopping
import StatLean.MultipleTesting.FDP.Defs
import StatLean.MultipleTesting.PValues.Defs
import Mathlib.Probability.Independence.Basic

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

/-! ## Rewriting the Storey FDP into the counting-process form

The rejection set `storeyRejects p q ω = {i : pᵢ(ω) ≤ τ}` (with `τ = storeyThreshold p q ω`) makes
the rejection / false-rejection counts coincide with the threshold counting processes at `t = τ`:
`numRejections = R(τ) = countLE p τ` and `numFalseRejections = V(τ) = nullCountLE H₀ p τ`. Hence
`FDP = V(τ)/(R(τ)∨1)`. These are pure `Finset` rewrites (no probability) and are the bridge between
the `FDP/Defs` layer and the `EmpiricalCDF` counting processes that the martingale argument runs on.
-/

/-- The Storey rejection set intersected with the nulls is exactly the null counting filter at
`t = τ`: `{i : pᵢ ≤ τ} ∩ H₀ = {j ∈ H₀ : pⱼ ≤ τ}`. -/
private lemma storeyRejects_inter_eq (p : Fin n → Ω → ℝ) (q : ℝ) (H₀ : Finset (Fin n)) (ω : Ω) :
    storeyRejects p q ω ∩ H₀
      = H₀.filter (fun j => p j ω ≤ storeyThreshold p q ω) := by
  ext j
  simp only [storeyRejects, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- `numRejections (storeyRejects p q) = R(τ) = countLE p τ` (`τ = storeyThreshold p q ω`). -/
private lemma storey_numRejections_eq (p : Fin n → Ω → ℝ) (q : ℝ) (ω : Ω) :
    numRejections (storeyRejects p q) ω = countLE p (storeyThreshold p q ω) ω := rfl

/-- `numFalseRejections H₀ (storeyRejects p q) = V(τ) = nullCountLE H₀ p τ`. -/
private lemma storey_numFalseRejections_eq (p : Fin n → Ω → ℝ) (q : ℝ) (H₀ : Finset (Fin n))
    (ω : Ω) :
    numFalseRejections H₀ (storeyRejects p q) ω
      = nullCountLE H₀ p (storeyThreshold p q ω) ω := by
  unfold numFalseRejections nullCountLE
  rw [storeyRejects_inter_eq]

/-- The Storey FDP in counting-process form: `FDP = V(τ)/(R(τ)∨1)`. -/
private lemma storey_FDP_eq (p : Fin n → Ω → ℝ) (q : ℝ) (H₀ : Finset (Fin n)) (ω : Ω) :
    FDP H₀ (storeyRejects p q) ω
      = (nullCountLE H₀ p (storeyThreshold p q ω) ω : ℝ)
          / max (countLE p (storeyThreshold p q ω) ω : ℝ) 1 := by
  unfold FDP
  rw [storey_numFalseRejections_eq, storey_numRejections_eq]

/-- **Storey's procedure controls FDR** (Candès, Lecture 7, §7.4, Theorem 3, STAT 300C). For
independent uniform null p-values, `FDR ≤ q`.

The verified content here reduces `FDR = E[FDP]` to the counting-process form
`E[ V(τ)/(R(τ)∨1) ]` (via `storey_FDP_eq`). The remaining `sorry` is the analytic + probabilistic
core, blocked on machinery not packaged as merged bricks:

* **Threshold attainment** `storeyFDRhat q τ ≤ q` at the `sSup` (with `τ > 0`), giving the pointwise
  bound `FDP(τ) ≤ q·(V(τ)/τ)·1/(2(1+n−R(1/2)))`. `storeyFDRhat` is a step function (jumps at the
  order statistics), so the constraint set is not closed under the naive topology — this needs the
  right-continuity of `R(·)` rather than a continuity-of-the-objective argument.
* **Joint-factor optional stopping.** `storey_reverseMG_ost` (the documented martingale debt) gives
  `E[V(τ)/τ] = 2·E[V(1/2)]`, but the FDP bound carries the *random* weight
  `1/(2(1+n−R(1/2)))` correlated with the path; bridging needs a joint form of the backwards-MG
  optional-stopping statement.
* **Null-count law** `V(1/2) ∼ Bin(n₀,1/2)` (independent uniform nulls, `n₀ = H₀.card`), which turns
  `E[V(1/2)/(1+n₀−V(1/2))]` into `∑ₖ C(n₀,k)·2^{−n₀}·k/(1+(n₀−k))`. That finite sum is then bounded
  by `1 − 2^{−n₀} ≤ 1` via `binom_ratio_sum_le_one`; the missing piece is the distribution of the
  null count, not the algebra. -/
theorem storey_fdr_le (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin n))
    (p : Fin n → Ω → ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    -- USER-INPUT: p-values measurable; Candès L7 §7.4
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: independent; Candès L7 §7.4
    (hindep : iIndepFun p μ)
    -- USER-INPUT: each null exactly uniform on [0,1]; Candès L7 §7.4
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    FDR H₀ (storeyRejects p q) μ ≤ q := by
  -- Reduce `FDR = E[FDP]` to the counting-process form `E[ V(τ)/(R(τ)∨1) ]`.
  rw [FDR]
  simp_rw [storey_FDP_eq]
  -- Remaining: threshold-attainment + joint-factor `storey_reverseMG_ost` + null-count law
  -- `V(1/2) ∼ Bin(n₀,1/2)`, then `binom_ratio_sum_le_one`. See docstring for blocking steps.
  sorry

end StatLean.MultipleTesting
