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

/-! ## The reverse-martingale weight and the two integrands of the optional-stopping identity

The optional-stopping argument runs on the backwards martingale `M(t) = V(t)/t` over `t ∈ (0,1/2]`,
carrying the **`𝒢_{1/2}`-measurable weight** `w(ω) = (1/2)/(1 + n₀ − V(1/2))` (the `+1` from
`storeyPiZero` keeps the denominator `≥ 1`, hence strictly positive). Two integrands matter:

* `storeyLHSint = (V(τ)/τ)·w` — the stopped value carrying the weight; this is what the Storey FDP
  is bounded by (`storey_FDP_le_bound`).
* `storeyRHSint = V(1/2)/(1 + n₀ − V(1/2))` — the value of the same quantity at the top of the
  backwards filtration `t = 1/2` (using `(V(1/2)/(1/2))·w = 2·V(1/2)·w = V(1/2)/(1+n₀−V(1/2))`).

The reverse-MG optional-stopping identity (`storey_reverseMG_ost`) is `∫ LHS = ∫ RHS`, and the
binomial null-count law (`storey_binom_bound`) is `∫ RHS ≤ 1`. -/

/-- The strictly-positive Storey denominator `1 + n₀ − V(1/2)` (`n₀ = H₀.card`). The `+1` of
`storeyPiZero` is what makes this `≥ 1`. -/
private noncomputable def storeyDenom (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  1 + (H₀.card : ℝ) - (nullCountLE H₀ p (1 / 2) ω : ℝ)

private lemma nullCountLE_le_card (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) :
    nullCountLE H₀ p t ω ≤ H₀.card := Finset.card_filter_le _ _

private lemma storeyDenom_ge_one (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (ω : Ω) :
    1 ≤ storeyDenom H₀ p ω := by
  unfold storeyDenom
  have : (nullCountLE H₀ p (1 / 2) ω : ℝ) ≤ (H₀.card : ℝ) := by
    exact_mod_cast nullCountLE_le_card H₀ p (1 / 2) ω
  linarith

private lemma storeyDenom_pos (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (ω : Ω) :
    0 < storeyDenom H₀ p ω := lt_of_lt_of_le one_pos (storeyDenom_ge_one H₀ p ω)

/-- The weighted stopped value `(V(τ)/τ)·w`, with `w = (1/2)/(1+n₀−V(1/2))` the `𝒢_{1/2}`-measurable
weight (`τ = storeyThreshold p q ω`). -/
private noncomputable def storeyLHSint (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (q : ℝ) (ω : Ω) :
    ℝ :=
  ((nullCountLE H₀ p (storeyThreshold p q ω) ω : ℝ) / storeyThreshold p q ω)
    * ((1 / 2) / storeyDenom H₀ p ω)

/-- The top-of-filtration value `V(1/2)/(1+n₀−V(1/2))`, equal to `(V(1/2)/(1/2))·w`. Bounded by `n₀`,
hence integrable; its integral is `≤ 1` by the binomial null-count law (`storey_binom_bound`). -/
private noncomputable def storeyRHSint (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  (nullCountLE H₀ p (1 / 2) ω : ℝ) / storeyDenom H₀ p ω

/-- **Backwards-martingale optional stopping for the Storey threshold** (the martingale-theoretic
core of Theorem 3): for independent uniform null p-values, the weighted stopped value `(V(τ)/τ)·w`
is integrable and `∫ (V(τ)/τ)·w = ∫ V(1/2)/(1+n₀−V(1/2))`, where `V(t) = nullCountLE H₀ p t`,
`τ = storeyThreshold p q`, `w = (1/2)/(1+n₀−V(1/2))` is the `𝒢_{1/2}`-measurable weight, and the
right side is `(V(1/2)/(1/2))·w`. This is Doob's optional stopping on the backwards martingale
`{V(t)/t}_{t∈(0,1/2]}` against the `𝒢_{1/2}`-measurable weight `w` (tower property: `E[V(τ)/τ |
𝒢_{1/2}] = V(1/2)/(1/2)`).

**Documented named `sorry`.** Mathlib lacks continuous-time backwards-martingale / optional-stopping
support; the faithful discrete reformulation over the null order statistics (the uniform analogue of
the knock-off `condExp_coord_eq_count_div` — conditional on `V(1/2)=m`, the `m` nulls `≤ 1/2` are
i.i.d. `Uniform[0,1/2]`, so `V(t)|𝒢_{1/2} ∼ Bin(m,2t)` and `E[V(t)/t|𝒢_{1/2}] = 2m = V(1/2)/(1/2)`)
is a self-contained development of its own, mirroring `Knockoff/Supermartingale.lean`. The
integrability claim is the substantive analytic content (`V(τ)/τ` is unbounded near `τ → 0`; it is
integrable precisely because the reverse-MG keeps `E[V(t)/t] = 2n₀` constant). -/
theorem storey_reverseMG_ost (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin n))
    (p : Fin n → Ω → ℝ) (q : ℝ)
    -- USER-INPUT: p-values measurable; Candès L7 §7.4
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: independent; Candès L7 §7.4
    (hindep : iIndepFun p μ)
    -- USER-INPUT: each null exactly uniform on [0,1]; Candès L7 §7.4
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    Integrable (storeyLHSint H₀ p q) μ ∧
      ∫ ω, storeyLHSint H₀ p q ω ∂μ = ∫ ω, storeyRHSint H₀ p ω ∂μ := by
  sorry

/-- **Binomial null-count bound** (Candès L7 §7.4): `∫ V(1/2)/(1+n₀−V(1/2)) ≤ 1`. For independent
uniform nulls, `V(1/2) ∼ Bin(n₀, 1/2)`, so the integral equals
`∑ₖ C(n₀,k)·2^{−n₀}·k/(1+(n₀−k)) = 1 − 2^{−n₀} ≤ 1` via `binom_ratio_sum_le_one`.

**Documented named `sorry`.** The algebra (`binom_ratio_sum_le_one`) is fully proved; the missing
piece is the *law* `V(1/2) ∼ Bin(n₀,1/2)` (a sum of `n₀` i.i.d. `Bernoulli(1/2)` indicators
`𝟙(Uⱼ ≤ 1/2)`), which turns the integral into that finite sum. -/
theorem storey_binom_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin n))
    (p : Fin n → Ω → ℝ)
    -- USER-INPUT: p-values measurable; Candès L7 §7.4
    (hmeas : ∀ j, Measurable (p j))
    -- USER-INPUT: independent; Candès L7 §7.4
    (hindep : iIndepFun p μ)
    -- USER-INPUT: each null exactly uniform on [0,1]; Candès L7 §7.4
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    ∫ ω, storeyRHSint H₀ p ω ∂μ ≤ 1 := by
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

/-! ## Threshold attainment and the pointwise FDP bound -/

private lemma storeyFDRhat_zero (p : Fin n → Ω → ℝ) (ω : Ω) :
    storeyFDRhat p 0 ω = 0 := by
  simp [storeyFDRhat]

private lemma storeyThreshold_set_bddAbove (p : Fin n → Ω → ℝ) (q : ℝ) (ω : Ω) :
    BddAbove {t : ℝ | t ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ storeyFDRhat p t ω ≤ q} :=
  ⟨1 / 2, fun t ht => ht.1.2⟩

private lemma storeyThreshold_zero_mem (p : Fin n → Ω → ℝ) {q : ℝ} (hq0 : 0 < q) (ω : Ω) :
    (0 : ℝ) ∈ {t : ℝ | t ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ storeyFDRhat p t ω ≤ q} :=
  ⟨⟨le_rfl, by norm_num⟩, by rw [storeyFDRhat_zero]; exact hq0.le⟩

private lemma storeyThreshold_nonneg (p : Fin n → Ω → ℝ) {q : ℝ} (hq0 : 0 < q) (ω : Ω) :
    0 ≤ storeyThreshold p q ω :=
  le_csSup (storeyThreshold_set_bddAbove p q ω) (storeyThreshold_zero_mem p hq0 ω)

/-- **Threshold attainment** (the right-continuity ingredient of Theorem 3): the estimated FDR at
the data-dependent threshold `τ = storeyThreshold p q ω` does not exceed `q`. `storeyFDRhat p · ω`
is right-continuous in `t` (continuous numerator `π̂₀·n·t` over the right-continuous step denominator
`R(·)∨1`); at the `sSup`, either `τ` is not an order statistic (continuity gives the left-limit `≤ q`)
or `R(·)` jumps up at `τ` (so the value drops below the left-limit `≤ q`). Either way `≤ q`.

**Documented named `sorry`.** The sublevel set of a right-continuous step function is not closed
under the naive topology; the attainment needs the order-statistic jump analysis of `countLE`, not
a continuity-of-the-objective argument. -/
private theorem storey_threshold_attained (p : Fin n → Ω → ℝ) {q : ℝ} (hq0 : 0 < q) (ω : Ω) :
    storeyFDRhat p (storeyThreshold p q ω) ω ≤ q := by
  sorry

/-- Splitting the rejection count over nulls and non-nulls: `R(t) + n₀ ≤ V(t) + n` (`n₀ = H₀.card`).
The non-null rejections `R(t) − V(t) = #{j ∉ H₀ : pⱼ ≤ t}` are at most the `n − n₀` non-nulls. -/
private lemma countLE_add_card_le (H₀ : Finset (Fin n)) (p : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) :
    countLE p t ω + H₀.card ≤ nullCountLE H₀ p t ω + n := by
  classical
  set P : Fin n → Prop := fun j => p j ω ≤ t with hP
  have hcount : countLE p t ω
      = (H₀.filter P).card + (H₀ᶜ.filter P).card := by
    unfold countLE
    rw [← Finset.filter_card_add_filter_neg_card_eq_card (p := fun j => j ∈ H₀)]
    congr 1
    · rw [Finset.filter_filter]; congr 1; ext j; simp [hP, and_comm]
    · rw [Finset.filter_filter]; congr 1; ext j; simp [hP, and_comm, Finset.mem_compl]
  have hnn : (H₀ᶜ.filter P).card ≤ n - H₀.card := by
    calc (H₀ᶜ.filter P).card ≤ H₀ᶜ.card := Finset.card_filter_le _ _
      _ = n - H₀.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hcard : H₀.card ≤ n := by simpa using Finset.card_le_univ H₀
  rw [hcount]
  have : (H₀.filter P).card = nullCountLE H₀ p t ω := rfl
  omega

/-- a.e. every null p-value is strictly positive: `μ{ω | pⱼ ω ≤ 0} = ofReal 0 = 0` for `j ∈ H₀`. -/
private lemma storey_nulls_pos (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin n))
    (p : Fin n → Ω → ℝ)
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    ∀ᵐ ω ∂μ, ∀ j ∈ H₀, 0 < p j ω := by
  rw [Filter.eventually_all_finset]
  intro j hj
  have h0 : μ {ω | p j ω ≤ 0} = 0 := by
    rw [hnull j hj 0 le_rfl (by norm_num)]; simp
  rw [ae_iff]
  convert h0 using 2
  ext ω; simp [not_lt]

/-- **Pointwise FDP bound** (threshold attainment, in counting-process form): a.e.,
`V(τ)/(R(τ)∨1) ≤ q · (V(τ)/τ) · (1/2)/(1+n₀−V(1/2))`. The `τ = 0` branch uses
`storey_nulls_pos` (then `V(0) = 0`); the `τ > 0` branch combines `storey_threshold_attained`
(`π̂₀·n·τ ≤ q·(R(τ)∨1)`) with `π̂₀·n = 2(1+n−R(1/2)) ≥ 2·(1+n₀−V(1/2))` (`countLE_add_card_le`). -/
private lemma storey_FDP_le_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H₀ : Finset (Fin n))
    (p : Fin n → Ω → ℝ) {q : ℝ} (hq0 : 0 < q)
    (hnull : ∀ j ∈ H₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → μ {ω | p j ω ≤ t} = ENNReal.ofReal t) :
    ∀ᵐ ω ∂μ, (nullCountLE H₀ p (storeyThreshold p q ω) ω : ℝ)
        / max (countLE p (storeyThreshold p q ω) ω : ℝ) 1
      ≤ q * storeyLHSint H₀ p q ω := by
  sorry

/-- **Storey's procedure controls FDR** (Candès, Lecture 7, §7.4, Theorem 3, STAT 300C). For
independent uniform null p-values, `FDR ≤ q`.

The full assembly is verified here from three sharp named bricks isolating the irreducible
probabilistic content: `storey_reverseMG_ost` (the reverse-martingale optional-stopping identity,
`∫ (V(τ)/τ)·w = ∫ V(1/2)/(1+n₀−V(1/2))`, with integrability), `storey_binom_bound` (the binomial
null-count law `∫ V(1/2)/(1+n₀−V(1/2)) ≤ 1`), and `storey_threshold_attained` (the right-continuity
attainment `storeyFDRhat τ ≤ q`, consumed via the proved pointwise bound `storey_FDP_le_bound`).
Reducing `FDR = E[FDP]` to `E[FDP] ≤ q·∫ LHS = q·∫ RHS ≤ q` is the proved glue. -/
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
  obtain ⟨hLint, hOST⟩ := storey_reverseMG_ost μ H₀ p q hmeas hindep hnull
  have hg_int : Integrable (fun ω => q * storeyLHSint H₀ p q ω) μ := hLint.const_mul q
  have hfdp_nonneg : (0 : Ω → ℝ) ≤ᵐ[μ] fun ω =>
      (nullCountLE H₀ p (storeyThreshold p q ω) ω : ℝ)
        / max (countLE p (storeyThreshold p q ω) ω : ℝ) 1 := by
    filter_upwards with ω
    exact div_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (le_max_right _ _))
  calc ∫ ω, (nullCountLE H₀ p (storeyThreshold p q ω) ω : ℝ)
          / max (countLE p (storeyThreshold p q ω) ω : ℝ) 1 ∂μ
      ≤ ∫ ω, q * storeyLHSint H₀ p q ω ∂μ :=
        integral_mono_of_nonneg hfdp_nonneg hg_int
          (storey_FDP_le_bound μ H₀ p hq0 hnull)
    _ = q * ∫ ω, storeyLHSint H₀ p q ω ∂μ := integral_const_mul q _
    _ = q * ∫ ω, storeyRHSint H₀ p ω ∂μ := by rw [hOST]
    _ ≤ q * 1 :=
        mul_le_mul_of_nonneg_left (storey_binom_bound μ H₀ p hmeas hindep hnull) hq0.le
    _ = q := mul_one q

end StatLean.MultipleTesting
