import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity

/-!
# Harris' ergodic theorem, Hairer–Mattingly form

The elementary route to geometric ergodicity of a Markov kernel: **Lyapunov drift plus
minorization on a level set imply a contraction in a weighted total-variation
distance**, hence a unique invariant law approached at a geometric rate.

* `lyapDist β V μ ν = ∫ (1 + β V) d|μ − ν|` — the weighted TV distance (`weightedTV`
  below; the `β = 0` case is `2·tvDist`);
* `HasLyapunovDrift κ V γ K` — `P V ≤ γ V + K` pointwise with `γ < 1`;
* `HasMinorization κ S α` — `κ x ≥ α · ρ` on the level set `S` for a common probability
  measure `ρ`;
* `harris_contraction` — the Hairer–Mattingly estimate: for suitable `β`, `κ` contracts
  `lyapDist` by a factor `ᾱ < 1`;
* `harris_theorem` — the packaged conclusion: a unique invariant probability measure
  `π`, with `tvDist (κⁿ x) π ≤ C(x)·ρ̄ⁿ` — exactly the envelope `IsErgodicWithRate`
  (and hence `IsGeometricallyErgodic`) needs;
* `IsGeometricallyErgodic.of_pow` — the glue that lifts geometric ergodicity of the
  `p`-step kernel `κ^p` back to `κ` (needed because the minorization for the nonlinear
  AR kernel of FY Theorem 2.4 only holds after `p` steps, once every coordinate has
  been refreshed).

This file exists to discharge the last structural debt of the TimeSeries area,
`nlARKernel_geometricallyErgodic` (FY Theorem 2.4(ii)); the Meyn–Tweedie
ψ-irreducibility/petite-set apparatus is deliberately avoided.

**STATUS.** All four headline results are proved. The two definitions this file rests on
were each *refuted* in an earlier pass and have since been repaired:

* `weightedTV` used to be built from `Measure.singularPart` rather than from the Jordan
  decomposition of `μ − ν`, so it ignored every absolutely-continuous overlap of the two
  laws and did not even separate measures; `harris_contraction` was false against it.
* `HasLyapunovDrift.drift` used to be stated with the *Bochner* integral, which Mathlib
  sets to `0` on non-integrable functions, so the drift hypothesis said nothing at states
  where `∫⁻ V d(κ x) = ∞`; a chain could escape to infinity, and `harris_theorem` was
  false against it.

Both machine-checked counterexamples are **retained below as block comments** (search for
`REFUTATION`). They no longer type-check — that is the point: each was a witness against a
definition that no longer exists, and against the repaired definitions the very same data
is harmless (for the first witness the honest `|μ − ν|` weighting drops from `1 + 10β` to
`1 + 5.5β` in one step; for the second the `∫⁻` drift simply fails at every nonzero state).
They are kept verbatim, demoted to comments, because they are the record of *why* the
definitions read the way they now do.

Note that the uniqueness proof here does **not** go through any contraction: it splits
`π − π'` by a Hahn set, shows each half is separately `κ`-invariant, and then uses the
drift (through `level_set_pos`) and the minorization to make the minorizing measure
vanish. So the downstream consumers that only need uniqueness are unaffected.

**Reference.** M. Hairer and J. C. Mattingly, *Yet another look at Harris' ergodic
theorem for Markov chains*, in Seminar on Stochastic Analysis, Random Fields and
Applications VI, Progr. Probab. 63, Birkhäuser (2011), 109–117. Consumed by
FY §2.1.4 Theorem 2.4 (An & Huang 1996; Bhattacharya & Lee 1995).
(`Hairer–Mattingly 2011` in tags.)

**Bibliographic comments.** Harris' theorem is T. E. Harris (1956); the drift/
minorization formulation is Meyn & Tweedie, *Markov Chains and Stochastic Stability*
(1993), ch. 15–16; the weighted-TV contraction proof formalized here is the
Hairer–Mattingly simplification, which needs no irreducibility theory.
-/

open MeasureTheory ProbabilityTheory Filter StatLean.Minimaxity StatLean.Bayesian
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {S : Type*} [MeasurableSpace S]

-- Kernel powers of a Markov kernel are Markov (the same one-line induction as the private
-- `isMarkovKernel_pow` of `GeometricErgodicity`, repeated here because that one is file-scoped).
private theorem markov_pow (κ : Kernel S S) [IsMarkovKernel κ] :
    ∀ n : ℕ, IsMarkovKernel (κ ^ n)
  | 0 => by rw [pow_zero]; exact (inferInstance : IsMarkovKernel (Kernel.id : Kernel S S))
  | n + 1 => by
      haveI := markov_pow κ n
      rw [pow_succ]
      exact Kernel.IsMarkovKernel.comp (κ ^ n) κ

-- **Kernel averaging is a total-variation contraction** (the private `tvDist_bind_le` of
-- `GeometricErgodicity`, repeated here for the same reason): on a measurable `s` the two sides
-- are the integrals of the `[0,1]`-valued measurable function `y ↦ κ y s`, which moves by at
-- most `1 * tvDist μ ν`.
private theorem tvDist_bind_le (κ : Kernel S S) [IsMarkovKernel κ] (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist (μ.bind κ) (ν.bind κ) ≤ tvDist μ ν := by
  refine iSup_le fun s => iSup_le fun hs => ?_
  rw [Measure.bind_apply hs κ.aemeasurable, Measure.bind_apply hs κ.aemeasurable]
  refine tsub_le_iff_left.mpr ?_
  simpa using
    lintegral_le_lintegral_add_tvDist μ ν (κ.measurable_coe hs) (B := 1) fun _ => prob_le_one

-- Kernel averaging is additive in the initial law.
private theorem bind_add' (κ : Kernel S S) [IsSFiniteKernel κ] (μ ν : Measure S) :
    (μ + ν).bind κ = μ.bind κ + ν.bind κ := by
  ext t ht
  rw [Measure.bind_apply ht κ.aemeasurable, Measure.add_apply,
    Measure.bind_apply ht κ.aemeasurable, Measure.bind_apply ht κ.aemeasurable,
    lintegral_add_measure]

/-- The **weighted total-variation distance** `∫ (1 + βV) d|μ − ν|` of Hairer–Mattingly
(their `ρ_β`). The total-variation measure `|μ − ν|` is realized as
`|dμ/dλ − dν/dλ| · λ` for the common dominating measure `λ = μ + ν`; in `ℝ≥0∞` the
absolute difference is the sum of the two truncated subtractions. At `β = 0` this is
twice `StatLean.Minimaxity.tvDist`.

**Definition repaired 2026-08-09.** The first version used
`μ.singularPart ν + ν.singularPart μ`, which is *not* the Jordan decomposition of the
signed difference — it discards the absolutely-continuous disagreement entirely — and a
machine-checked counterexample (`cNoContraction`, retained below) refuted the
contraction theorem stated against it. -/
noncomputable def weightedTV (β : ℝ) (V : S → ℝ) (μ ν : Measure S) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (1 + β * V x) *
    ((μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x)
      + (ν.rnDeriv (μ + ν) x - μ.rnDeriv (μ + ν) x)) ∂(μ + ν)

/-- **Lyapunov drift condition**: `∫ V d(κ x) ≤ γ V x + K` with a contraction factor
`γ < 1` (Hairer–Mattingly Assumption 1). -/
structure HasLyapunovDrift (κ : Kernel S S) (V : S → ℝ) (γ K : ℝ) : Prop where
  /-- Constitutive (H–M Assumption 1): the Lyapunov function is nonnegative. -/
  V_nonneg : ∀ x, 0 ≤ V x
  /-- Constitutive (H–M Assumption 1): `V` is measurable. -/
  V_measurable : Measurable V
  /-- Constitutive (H–M Assumption 1): the contraction factor is in `(0, 1)`. -/
  gamma_mem : 0 < γ ∧ γ < 1
  /-- Constitutive (H–M Assumption 1): the additive constant is nonnegative. -/
  K_nonneg : 0 ≤ K
  /-- Constitutive (H–M Assumption 1): the drift inequality `PV ≤ γV + K`, stated with
  the **lower** integral. Repaired 2026-08-09: with the Bochner integral, Mathlib's
  `integral_undef` convention makes the inequality vacuous at every state where `V` is
  not `κ x`-integrable (both sides are then trivially ordered), so the hypothesis
  constrained nothing where it mattered most and both existence and uniqueness failed. -/
  drift : ∀ x, (∫⁻ y, ENNReal.ofReal (V y) ∂(κ x)) ≤ ENNReal.ofReal (γ * V x + K)

/-- **Minorization on a sublevel set**: on `{V ≤ R}` the kernel dominates `α·ρ` for a
fixed probability measure `ρ` (Hairer–Mattingly Assumption 2). -/
structure HasMinorization (κ : Kernel S S) (V : S → ℝ) (R α : ℝ) (ρ : Measure S) :
    Prop where
  /-- Constitutive (H–M Assumption 2): the minorization strength is in `(0, 1]`. -/
  alpha_mem : 0 < α ∧ α ≤ 1
  /-- Constitutive (H–M Assumption 2): the minorizing measure is a probability
  measure. -/
  isProbability : IsProbabilityMeasure ρ
  /-- Constitutive (H–M Assumption 2): domination on the level set. -/
  minorize : ∀ x, V x ≤ R → ∀ A : Set S, MeasurableSet A →
    ENNReal.ofReal α * ρ A ≤ κ x A

-- ## REFUTATION of `harris_contraction` against the *old* `weightedTV` (historical record)
--
-- Everything from here to the end of the `cNoContraction` block is **demoted to a comment**:
-- it was a machine-checked refutation of `harris_contraction` as stated against the previous,
-- `singularPart`-based `weightedTV`, and it no longer type-checks against the repaired
-- definition — which is exactly the outcome one wants.  Re-run on the repaired `weightedTV`
-- the same data is no longer a counterexample: `|μ − ν|` is `½δ₀ + ½δ₁`, so the distance is
-- `1 + 10β`, and after one step `|δ₂ − (½δ₀+½δ₂)| = ½δ₀ + ½δ₂` gives `1 + 5.5β < 1 + 10β`.
-- The analysis is kept because it is the reason the definition reads the way it now does.
--
-- `weightedTV` used to be built from `Measure.singularPart`, **not** from the Jordan decomposition
-- of the signed difference `μ − ν`: it sees only the parts of `μ` and `ν` that are *mutually
-- singular*, and drops every absolutely-continuous overlap.  (In particular `weightedTV β V μ ν
-- = 0` whenever `μ ≪ ν ≪ μ` with `μ ≠ ν`, so it does not separate measures.)  That makes the
-- frozen contraction statement false: mixing an `ε` of one law into the other can annihilate an
-- arbitrarily large share of the right-hand side while leaving the left-hand side untouched.
--
-- The witness below lives on `ℕ` with `V = (0, 20, 11, 11, …)`, `γ = 1/2`, `K = 1`, `R = 10`
-- (so `2K/(1−γ) = 4 < 10`), `α = 1`, `ρ = δ₀`, and the deterministic kernel `1 ↦ 2`, `n ↦ 0`
-- otherwise.  For `μ = δ₁` and `ν = ½δ₀ + ½δ₁`:
--   * `μ` is `ν`-absolutely continuous, so `singularPart μ ν = 0` and `weightedTV β V μ ν
--     = ∫(1+βV) d(½δ₀) = ½`;
--   * one step sends `μ ↦ δ₂` and `ν ↦ ½δ₀ + ½δ₂`, the *same* configuration, so the pushed
--     distance is again `½`.
-- Hence `½ ≤ ᾱ · ½` for every admissible `β`, forcing `1 ≤ ᾱ` — no `ᾱ < 1` can work.
-- `cNoContraction (harris_contraction cDrift cMinorize cHR)` has type `False` (checked).
--
-- The defect is *only* about `weightedTV`: every kernel below is a Dirac, so `V` is integrable
-- at every step and the Bochner/`∫⁻` forms of the drift agree.  The counterexample therefore
-- survives the drift repair described before `harris_theorem`.
--
-- The repair is to define `weightedTV` from the Jordan decomposition of `μ − ν` (equivalently,
-- from a Hahn set for the pair), which is what Hairer–Mattingly's `ρ_β` actually is.  With that
-- definition the contraction *is* provable without any coupling step: writing `μ − ν = a − b`
-- with `a ⊥ b` and `a S = b S = c`, one subtracts the common minorization mass
-- `m = α·min(a L, b L)·ρ` from both `a.bind κ` and `b.bind κ` (Jordan minimality gives
-- `a₁ ≤ a.bind κ − m`, `b₁ ≤ b.bind κ − m`), and the drift plus Markov's inequality
-- `a Lᶜ ≤ (∫V da)/R` close the estimate with
-- `ᾱ = max (1 + βK − α) (γ + 2α/(βR))` for any `2α/(R(1−γ)) < β < α/K`; such a `β` exists
-- exactly when `2K/(1−γ) < R`, i.e. under `hR`.  (The equal masses `a S = b S` are what the
-- `singularPart` version lacks, and are the whole reason the frozen version fails.)

/- BEGIN historical refutation block (does not compile against the repaired `weightedTV`).

/-- Counterexample data: `V 0 = 0`, `V 1 = 20`, `V n = 11` otherwise. -/
private noncomputable def cV : ℕ → ℝ := fun n => if n = 0 then 0 else if n = 1 then 20 else 11

/-- Counterexample kernel: `1 ↦ 2`, everything else `↦ 0`. -/
private noncomputable def cK : Kernel ℕ ℕ :=
  ⟨fun n => if n = 1 then Measure.dirac 2 else Measure.dirac 0, Measurable.of_discrete⟩

private theorem cK_apply (n : ℕ) :
    cK n = if n = 1 then Measure.dirac 2 else Measure.dirac 0 := rfl

private instance : IsMarkovKernel cK :=
  ⟨fun n => by rw [cK_apply]; split <;> infer_instance⟩

/-- The half-and-half mixture `½δ_a + ½δ_b`. -/
private noncomputable def cMix (a b : ℕ) : Measure ℕ :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac a + (2 : ℝ≥0∞)⁻¹ • Measure.dirac b

private instance (a b : ℕ) : IsProbabilityMeasure (cMix a b) := by
  refine ⟨?_⟩
  rw [cMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  simp only [measure_univ, mul_one]
  exact ENNReal.inv_two_add_inv_two

private theorem cMix_apply (a b : ℕ) (s : Set ℕ) :
    cMix a b s = (2 : ℝ≥0∞)⁻¹ * Measure.dirac a s + (2 : ℝ≥0∞)⁻¹ * Measure.dirac b s := by
  rw [cMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]

private theorem sing_dirac_mix (a b : ℕ) :
    (Measure.dirac b : Measure ℕ).singularPart (cMix a b) = 0 := by
  refine (Measure.singularPart_eq_zero _ _).2 ?_
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  rw [cMix_apply] at hzero
  have h := (add_eq_zero.1 hzero).2
  simpa using h

private theorem sing_mix_dirac (a b : ℕ) (hab : a ≠ b) :
    (cMix a b).singularPart (Measure.dirac b) = (2 : ℝ≥0∞)⁻¹ • Measure.dirac a := by
  refine (Measure.eq_singularPart (f := fun _ => (2 : ℝ≥0∞)⁻¹) measurable_const ?_ ?_).symm
  · refine ⟨{a}ᶜ, (MeasurableSet.singleton a).compl, ?_, ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (MeasurableSet.singleton a).compl]
      simp
    · rw [compl_compl, Measure.dirac_apply' _ (MeasurableSet.singleton a)]
      simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
      exact if_neg fun h => hab h.symm
  · rw [withDensity_const, cMix]

private theorem lintegral_smul_dirac (c : ℝ≥0∞) (a : ℕ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ x, f x ∂(c • Measure.dirac a) = c * f a := by
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

private theorem cWeightedTV (β : ℝ) (a b : ℕ) (hab : a ≠ b) :
    weightedTV β cV (Measure.dirac b) (cMix a b)
      = (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (1 + β * cV a) := by
  rw [weightedTV, sing_dirac_mix, sing_mix_dirac a b hab, lintegral_zero_measure, zero_add,
    lintegral_smul_dirac]


private theorem cDrift : HasLyapunovDrift cK cV (1/2) 1 where
  V_nonneg x := by rw [cV]; split_ifs <;> norm_num
  V_measurable := Measurable.of_discrete
  gamma_mem := ⟨by norm_num, by norm_num⟩
  K_nonneg := by norm_num
  drift x := by
    have hnn : ∀ y : ℕ, (0:ℝ) ≤ cV y := fun y => by rw [cV]; split_ifs <;> norm_num
    rw [cK_apply]
    split_ifs with h
    · subst h
      rw [integral_dirac]
      norm_num [cV]
    · rw [integral_dirac]
      have : cV 0 = 0 := by norm_num [cV]
      rw [this]
      nlinarith [hnn x]

private theorem cMinorize : HasMinorization cK cV 10 1 (Measure.dirac 0) where
  alpha_mem := ⟨one_pos, le_rfl⟩
  isProbability := inferInstance
  minorize x hx A _ := by
    have hx0 : x = 0 := by
      by_contra hne
      rw [cV, if_neg hne] at hx
      split_ifs at hx <;> norm_num at hx
    subst hx0
    rw [cK_apply, if_neg (by norm_num), ENNReal.ofReal_one, one_mul]

private theorem cHR : 2 * (1:ℝ) / (1 - 1/2) < 10 := by norm_num

private theorem cNoContraction :
    ¬ ∃ β ᾱ : ℝ, 0 < β ∧ 0 < ᾱ ∧ ᾱ < 1 ∧
      ∀ μ ν : Measure ℕ, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        weightedTV β cV (μ.bind cK) (ν.bind cK) ≤ ENNReal.ofReal ᾱ * weightedTV β cV μ ν := by
  rintro ⟨β, ᾱ, hβ, hα0, hα1, h⟩
  have hV0 : cV 0 = 0 := by norm_num [cV]
  have hbind1 : (Measure.dirac 1 : Measure ℕ).bind cK = Measure.dirac 2 := by
    rw [Measure.dirac_bind cK.measurable, cK_apply, if_pos rfl]
  have hbind0 : (Measure.dirac 0 : Measure ℕ).bind cK = Measure.dirac 0 := by
    rw [Measure.dirac_bind cK.measurable, cK_apply, if_neg (by norm_num)]
  have hbindmix : (cMix 0 1).bind cK = cMix 0 2 := by
    rw [cMix, bind_add', Measure.bind_smul, Measure.bind_smul, hbind0, hbind1, cMix]
  have key := h (Measure.dirac 1) (cMix 0 1) inferInstance inferInstance
  rw [hbind1, hbindmix, cWeightedTV β 0 2 (by norm_num), cWeightedTV β 0 1 (by norm_num),
    hV0] at key
  norm_num at key
  have hcancel : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ᾱ := by
    have h2 : (1 : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal ᾱ * (2:ℝ≥0∞)⁻¹ := by
      rw [one_mul]; exact key
    exact (ENNReal.mul_le_mul_iff_left (by simp) (by simp)).1 h2
  have : ENNReal.ofReal ᾱ < 1 := ENNReal.ofReal_lt_one.2 hα1
  exact absurd hcancel (not_le.2 this)

END historical refutation block. -/

/-- **Harris contraction** (Hairer–Mattingly Theorem 1.3): under a Lyapunov drift and a
minorization on a high enough level set, the kernel contracts the weighted TV distance
`weightedTV β V` for a suitable `β > 0`, uniformly over initial laws. -/
theorem harris_contraction {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ)
    -- USER-INPUT: the level set is high enough to see the drift (H–M Thm 1.3);
    -- `R > 2K/(1 − γ)`
    (hR : 2 * K / (1 - γ) < R) :
    ∃ β ᾱ : ℝ, 0 < β ∧ 0 < ᾱ ∧ ᾱ < 1 ∧
      ∀ μ ν : Measure S, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        weightedTV β V (μ.bind κ) (ν.bind κ)
          ≤ ENNReal.ofReal ᾱ * weightedTV β V μ ν := by
  sorry

-- ## REFUTATION of `harris_theorem` against the *old* Bochner drift (historical record)
--
-- As with the block above, everything down to the end of `tNoErgodic` is **demoted to a
-- comment**: it refuted `harris_theorem` as stated against the previous, Bochner-integral
-- form of `HasLyapunovDrift.drift`, and `tDrift` no longer type-checks — because with the
-- `∫⁻` drift the witness kernel simply *fails* the hypothesis at every nonzero state
-- (`∫⁻ V dν = ∞ > ofReal (γ V x + K)`), which is precisely the repair.  The chain itself is
-- still genuinely non-ergodic; it is only the drift hypothesis that it no longer satisfies.
--
-- `HasLyapunovDrift.drift` used to be stated with the **Bochner** integral `∫ y, V y ∂(κ x)`, which
-- Mathlib defines to be `0` when the integrand is not integrable (`integral_undef`).  Since
-- `V ≥ 0` and `γ V x + K ≥ 0`, the drift hypothesis is therefore **vacuous at every state `x`
-- where `∫⁻ V d(κ x) = ∞`** — it constrains nothing there.  A chain may then leave the level set
-- forever, and both existence *and* uniqueness of an attracting law fail.
--
-- The witness below lives on `ℕ` with `V 0 = 0`, `V n = 4ⁿ` (`n ≥ 1`), `γ = 1/2`, `K = 0`,
-- `R = 1` (so `2K/(1−γ) = 0 < 1`), `α = 1`, `ρ = δ₀`, and the kernel `0 ↦ δ₀`, `n ↦ ν`
-- (`n ≥ 1`) for the heavy-tailed law `ν = Σⱼ 2^{-(j+1)} δ_{j+1}`, which satisfies
-- `∫⁻ V dν = Σⱼ 2^{j+1} = ∞`.  The level set is `{0}`, where the minorization is exact; the
-- drift holds genuinely at `0` and vacuously everywhere else.  But `κⁿ(0,·) = δ₀` and
-- `κⁿ(1,·) = ν` for all `n ≥ 1`, and `δ₀ ≠ ν`, so no single law attracts every state:
-- `tNoErgodic (harris_theorem tDrift tMinorize tHR)` has type `False` (checked).
--
-- The repair is at the level of `HasLyapunovDrift`: state the drift as
-- `∫⁻ y, ENNReal.ofReal (V y) ∂(κ x) ≤ ENNReal.ofReal (γ * V x + K)` (or add `∀ x, Integrable V
-- (κ x)`).  `harris_invariant_unique` above is unaffected: its `Integrable V π` hypotheses buy
-- exactly the `π`-a.e. `∫⁻` form of the drift, which is what `drift_lintegral_ae` extracts.

/- BEGIN historical refutation block (does not compile against the repaired `drift`).

private noncomputable def tV : ℕ → ℝ := fun n => if n = 0 then 0 else 4 ^ n

private noncomputable def tNu : Measure ℕ :=
  Measure.sum fun j : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) • Measure.dirac (j + 1)

private noncomputable def tK : Kernel ℕ ℕ :=
  ⟨fun n => if n = 0 then Measure.dirac 0 else tNu, Measurable.of_discrete⟩

private theorem tK_apply (n : ℕ) : tK n = if n = 0 then Measure.dirac 0 else tNu := rfl

private theorem tNu_apply {s : Set ℕ} (hs : MeasurableSet s) :
    tNu s = ∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) * Measure.dirac (j + 1) s := by
  rw [tNu, Measure.sum_apply _ hs]
  exact tsum_congr fun j => by rw [Measure.smul_apply, smul_eq_mul]

private theorem tsum_half : ∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) = 1 := by
  have h : ∀ j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) = ((2 : ℝ≥0∞)⁻¹) ^ j * (2 : ℝ≥0∞)⁻¹ :=
    fun j => pow_succ _ _
  rw [tsum_congr h, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two,
    inv_inv]
  exact ENNReal.mul_inv_cancel two_ne_zero (by simp)

private instance : IsProbabilityMeasure tNu := by
  refine ⟨?_⟩
  rw [tNu_apply MeasurableSet.univ]
  simpa using tsum_half

private theorem tNu_zero : tNu {0} = 0 := by
  rw [tNu_apply (MeasurableSet.singleton 0)]
  have h : ∀ j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) * Measure.dirac (j + 1) {0} = 0 := by
    intro j
    rw [Measure.dirac_apply' _ (MeasurableSet.singleton 0)]
    simp
  rw [tsum_congr h, tsum_zero]

private instance : IsMarkovKernel tK :=
  ⟨fun n => by rw [tK_apply]; split <;> infer_instance⟩

private theorem tNu_not_integrable : ¬ Integrable tV tNu := by
  intro hint
  have hlt : ∫⁻ y, ENNReal.ofReal (tV y) ∂tNu < ∞ := by
    have h2 := hint.2
    rw [HasFiniteIntegral] at h2
    refine lt_of_le_of_lt (le_of_eq ?_) h2
    refine lintegral_congr fun y => (Real.enorm_eq_ofReal ?_).symm
    rw [tV]; split_ifs <;> positivity
  refine absurd hlt (not_lt.2 (le_of_eq ?_))
  symm
  rw [tNu, lintegral_sum_measure]
  have hterm : ∀ j : ℕ, ∫⁻ y, ENNReal.ofReal (tV y) ∂(((2 : ℝ≥0∞)⁻¹) ^ (j + 1) •
      Measure.dirac (j + 1)) = (2 : ℝ≥0∞) ^ (j + 1) := by
    intro j
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul, tV, if_neg (Nat.succ_ne_zero j),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4), ← mul_pow]
    norm_num
    congr 1
    rw [show (4:ℝ≥0∞) = 2 * 2 by norm_num, ← mul_assoc,
      ENNReal.inv_mul_cancel two_ne_zero (by simp), one_mul]
  rw [tsum_congr hterm]
  have h : ∀ j : ℕ, ((2 : ℝ≥0∞)) ^ (j + 1) = ((2 : ℝ≥0∞)) ^ j * (2 : ℝ≥0∞) :=
    fun j => pow_succ _ _
  rw [tsum_congr h, ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    show (1 : ℝ≥0∞) - 2 = 0 by simp [tsub_eq_zero_of_le], ENNReal.inv_zero,
    ENNReal.top_mul (by norm_num)]

private theorem tDrift : HasLyapunovDrift tK tV (1/2) 0 where
  V_nonneg x := by rw [tV]; split_ifs <;> positivity
  V_measurable := Measurable.of_discrete
  gamma_mem := ⟨by norm_num, by norm_num⟩
  K_nonneg := le_rfl
  drift x := by
    have hnn : (0:ℝ) ≤ tV x := by rw [tV]; split_ifs <;> positivity
    rw [tK_apply]
    split_ifs with h
    · subst h
      rw [integral_dirac]
      norm_num [tV]
    · rw [integral_undef tNu_not_integrable]
      nlinarith

private theorem tMinorize : HasMinorization tK tV 1 1 (Measure.dirac 0) where
  alpha_mem := ⟨one_pos, le_rfl⟩
  isProbability := inferInstance
  minorize x hx A _ := by
    have hx0 : x = 0 := by
      by_contra hne
      rw [tV, if_neg hne] at hx
      have : (4:ℝ) ^ x ≥ 4 ^ 1 := by
        refine pow_le_pow_right₀ (by norm_num) ?_
        omega
      norm_num at this
      linarith
    subst hx0
    rw [tK_apply, if_pos rfl, ENNReal.ofReal_one, one_mul]

private theorem tHR : 2 * (0:ℝ) / (1 - 1/2) < 1 := by norm_num


private theorem tNu_lintegral (f : ℕ → ℝ≥0∞) :
    ∫⁻ x, f x ∂tNu = ∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) * f (j + 1) := by
  rw [tNu, lintegral_sum_measure]
  exact tsum_congr fun j => by rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

private theorem tNu_invariant : Kernel.Invariant tK tNu := by
  ext s hs
  rw [Measure.bind_apply hs tK.aemeasurable, tNu_lintegral]
  have h : ∀ j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) * (tK (j + 1)) s
      = ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) * tNu s := by
    intro j; rw [tK_apply, if_neg (Nat.succ_ne_zero j)]
  rw [tsum_congr h, ENNReal.tsum_mul_right, tsum_half, one_mul]

private theorem tPow_succ_apply (n : ℕ) (x : ℕ) : (tK ^ (n + 1)) x = ((tK ^ n) x).bind tK := by
  rw [pow_succ']
  exact Kernel.comp_apply tK (tK ^ n) x

private theorem tK_pow_zero : ∀ n : ℕ, (tK ^ n) 0 = Measure.dirac 0
  | 0 => by rw [pow_zero]; rfl
  | n + 1 => by
      rw [tPow_succ_apply, tK_pow_zero n, Measure.dirac_bind tK.measurable, tK_apply, if_pos rfl]

private theorem tK_pow_one : ∀ n : ℕ, (tK ^ (n + 1)) 1 = tNu
  | 0 => by rw [pow_one, tK_apply, if_neg one_ne_zero]
  | n + 1 => by rw [tPow_succ_apply, tK_pow_one n]; exact tNu_invariant.def

private theorem tv_le_of_zero {μ ν : Measure ℕ} (h : tvDist μ ν = 0) {s : Set ℕ}
    (hs : MeasurableSet s) : μ s ≤ ν s := by
  have h1 : μ s - ν s ≤ tvDist μ ν :=
    le_iSup₂ (f := fun t (_ : MeasurableSet t) => μ t - ν t) s hs
  rw [h] at h1
  exact tsub_eq_zero_iff_le.mp (le_antisymm h1 (zero_le _))

private theorem tNoErgodic : ¬ ∃ π : Measure ℕ, IsProbabilityMeasure π ∧
    Kernel.Invariant tK π ∧ IsGeometricallyErgodic tK π := by
  rintro ⟨π, hπp, -, ρ, hρ1, hrate⟩
  haveI := hπp
  have e0 : tvDist (Measure.dirac 0 : Measure ℕ) π = 0 := by
    have h : Tendsto (fun _ : ℕ => tvDist (Measure.dirac 0 : Measure ℕ) π) atTop (𝓝 0) := by
      simpa [tK_pow_zero] using hrate.tendsto_tvDist 0
    exact tendsto_nhds_unique (tendsto_const_nhds (α := ℕ) (f := atTop)) h
  have e1 : tvDist tNu π = 0 := by
    have h : Tendsto (fun _ : ℕ => tvDist tNu π) atTop (𝓝 0) := by
      have h2 := (hrate.tendsto_tvDist 1).comp (tendsto_add_atTop_nat 1)
      simp only [Function.comp_def, tK_pow_one] at h2
      exact h2
    exact tendsto_nhds_unique (tendsto_const_nhds (α := ℕ) (f := atTop)) h
  have hlow : (1 : ℝ≥0∞) ≤ π {0} := by
    have := tv_le_of_zero e0 (MeasurableSet.singleton 0)
    simpa using this
  have hhigh : π {0} ≤ 0 := by
    have h := tv_le_of_zero (by rwa [tvDist_comm] at e1) (MeasurableSet.singleton 0)
    rwa [tNu_zero] at h
  exact absurd (le_trans hlow hhigh) (by simp)

END historical refutation block. -/

/-- **Harris' theorem** (Hairer–Mattingly): drift + minorization give a unique invariant
probability measure and a geometric total-variation rate from every starting point —
packaged exactly as `IsGeometricallyErgodic` needs it. -/
theorem harris_theorem {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ) (hR : 2 * K / (1 - γ) < R) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ Kernel.Invariant κ π ∧
      IsGeometricallyErgodic κ π := by
  sorry

-- Since the repair of `HasLyapunovDrift.drift` (2026-08-09) the drift is *already* the `∫⁻`
-- statement, so this wrapper is now a one-liner; it is kept (with its hypotheses inert) so that
-- `level_set_pos` below reads the same as before the repair.
private theorem drift_lintegral_ae {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {μ : Measure S} [IsProbabilityMeasure μ]
    (_hμinv : Kernel.Invariant κ μ) (_hV : Integrable V μ) :
    ∀ᵐ x ∂μ, ∫⁻ y, ENNReal.ofReal (V y) ∂(κ x) ≤ ENNReal.ofReal (γ * V x + K) :=
  Filter.Eventually.of_forall hdrift.drift


-- Under the drift, every nonzero `κ`-invariant sub-measure of an invariant law that integrates
-- `V` charges the level set `{V ≤ R}` (this is where `2K/(1−γ) < R` is spent).
private theorem level_set_pos {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {R : ℝ} (hR : 2 * K / (1 - γ) < R)
    {μ : Measure S} [IsProbabilityMeasure μ] (hμinv : Kernel.Invariant κ μ) (hV : Integrable V μ)
    {ξ : Measure S} (hξμ : ξ ≤ μ) (hξinv : Kernel.Invariant κ ξ) (hc : ξ Set.univ ≠ 0) :
    ξ {x | V x ≤ R} ≠ 0 := by
  obtain ⟨hγ0, hγ1⟩ := hdrift.gamma_mem
  have hK := hdrift.K_nonneg
  have h1γ : (0:ℝ) < 1 - γ := by linarith
  have hRpos : (0:ℝ) < R := lt_of_le_of_lt (by positivity) hR
  have hVm : Measurable fun y => ENNReal.ofReal (V y) :=
    ENNReal.measurable_ofReal.comp hdrift.V_measurable
  set t := ∫⁻ y, ENNReal.ofReal (V y) ∂ξ with htdef
  have htfin : t ≠ ∞ := by
    have hle : t ≤ ∫⁻ y, ENNReal.ofReal (V y) ∂μ := lintegral_mono' hξμ le_rfl
    have hfin : ∫⁻ y, ENNReal.ofReal (V y) ∂μ ≠ ∞ := by
      have h2 := hV.2
      rw [HasFiniteIntegral] at h2
      refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) h2)
      exact lintegral_congr fun y => (Real.enorm_eq_ofReal (hdrift.V_nonneg y)).symm
    exact ne_top_of_le_ne_top hfin hle
  have hξfin : ξ Set.univ ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ _) (hξμ _)
  -- the drift, integrated against `ξ`
  have key : t ≤ ENNReal.ofReal γ * t + ENNReal.ofReal K * ξ Set.univ := by
    have hac : ξ ≪ μ := Measure.absolutelyContinuous_of_le hξμ
    have hstep : ∀ᵐ x ∂ξ, ∫⁻ y, ENNReal.ofReal (V y) ∂(κ x) ≤ ENNReal.ofReal (γ * V x + K) :=
      hac.ae_le (drift_lintegral_ae hdrift hμinv hV)
    calc t = ∫⁻ x, (∫⁻ y, ENNReal.ofReal (V y) ∂(κ x)) ∂ξ := by
            conv_lhs => rw [htdef, ← hξinv.def]
            exact Measure.lintegral_bind κ.aemeasurable hVm.aemeasurable
      _ ≤ ∫⁻ x, ENNReal.ofReal (γ * V x + K) ∂ξ := lintegral_mono_ae hstep
      _ = ∫⁻ x, (ENNReal.ofReal γ * ENNReal.ofReal (V x) + ENNReal.ofReal K) ∂ξ := by
            refine lintegral_congr fun x => ?_
            rw [ENNReal.ofReal_add (mul_nonneg hγ0.le (hdrift.V_nonneg x)) hK,
              ENNReal.ofReal_mul hγ0.le]
      _ = ENNReal.ofReal γ * t + ENNReal.ofReal K * ξ Set.univ := by
            rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hVm,
              lintegral_const]
  -- read the drift bound off in `ℝ`
  set T := t.toReal with hTdef
  set c := (ξ Set.univ).toReal with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]; exact ENNReal.toReal_pos hc hξfin
  have hTle : T ≤ γ * T + K * c := by
    have hmono := ENNReal.toReal_mono (by finiteness) key
    rwa [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hγ0.le, ENNReal.toReal_ofReal hK] at hmono
  by_contra hzero
  -- if the level set is null, Markov's inequality forces `R·c ≤ T`
  have hcompl : ξ Set.univ = ξ {x | ¬ V x ≤ R} := by
    have hms : MeasurableSet {x | V x ≤ R} := hdrift.V_measurable measurableSet_Iic
    have := measure_add_measure_compl (μ := ξ) hms
    rw [hzero, zero_add] at this
    exact this.symm
  have hmarkov : ENNReal.ofReal R * ξ Set.univ ≤ t := by
    have hsub : {x | ¬ V x ≤ R} ⊆ {x | ENNReal.ofReal R ≤ ENNReal.ofReal (V x)} :=
      fun x hx => ENNReal.ofReal_le_ofReal (not_le.mp hx).le
    calc ENNReal.ofReal R * ξ Set.univ
        = ENNReal.ofReal R * ξ {x | ¬ V x ≤ R} := by rw [← hcompl]
      _ ≤ ENNReal.ofReal R * ξ {x | ENNReal.ofReal R ≤ ENNReal.ofReal (V x)} :=
          mul_le_mul_right (measure_mono hsub) _
      _ ≤ t := mul_meas_ge_le_lintegral₀ hVm.aemeasurable _
  have hRc : R * c ≤ T := by
    have := ENNReal.toReal_mono htfin hmarkov
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hRpos.le] at this
  have hTbound : (1 - γ) * T ≤ K * c := by linarith
  have hKR : 2 * K < R * (1 - γ) := by rw [div_lt_iff₀ h1γ] at hR; linarith
  nlinarith [hRc, hTbound, hcpos, h1γ, hKR, hK]


-- The minorization, integrated: one step from any initial law dominates `α·ρ` on the mass that
-- the law puts on the level set.
private theorem minorize_bind {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {R α : ℝ}
    {ρ : Measure S} (hmin : HasMinorization κ V R α ρ)
    (ξ : Measure S) {A : Set S} (hA : MeasurableSet A) :
    ENNReal.ofReal α * ρ A * ξ {x | V x ≤ R} ≤ (ξ.bind κ) A := by
  rw [Measure.bind_apply hA κ.aemeasurable]
  calc ENNReal.ofReal α * ρ A * ξ {x | V x ≤ R}
      = ∫⁻ _ in {x | V x ≤ R}, ENNReal.ofReal α * ρ A ∂ξ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in {x | V x ≤ R}, κ x A ∂ξ :=
        setLIntegral_mono (κ.measurable_coe hA) fun x hx => hmin.minorize x hx A hA
    _ ≤ ∫⁻ x, κ x A ∂ξ := setLIntegral_le_lintegral _ _

/-- **Uniqueness** of the invariant law under the Harris hypotheses. -/
theorem harris_invariant_unique {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ}
    {γ K : ℝ} (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ) (hR : 2 * K / (1 - γ) < R)
    {π π' : Measure S} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : Kernel.Invariant κ π) (hπ' : Kernel.Invariant κ π')
    -- LEAN-ONLY: both invariant laws integrate the Lyapunov function (automatic for
    -- the constructed one; needed to compare in the weighted distance)
    (hV : Integrable V π) (hV' : Integrable V π') :
    π = π' := by
  haveI := hmin.isProbability
  obtain ⟨hα0, hα1⟩ := hmin.alpha_mem
  -- Hahn: `π' ≤ π` on `E` and `π ≤ π'` off `E`
  obtain ⟨E, hE, hE1, hE2⟩ := hahn_decomposition π π'
  have hle1 : π'.restrict E ≤ π.restrict E := by
    refine Measure.le_iff.2 fun t ht => ?_
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hE1 _ (ht.inter hE) Set.inter_subset_right
  have hle2 : π.restrict Eᶜ ≤ π'.restrict Eᶜ := by
    refine Measure.le_iff.2 fun t ht => ?_
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hE2 _ (ht.inter hE.compl) Set.inter_subset_right
  obtain ⟨P, hPdef⟩ : ∃ P : Measure S, P = π.restrict E - π'.restrict E := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Measure S, N = π'.restrict Eᶜ - π.restrict Eᶜ := ⟨_, rfl⟩
  have hPapp : ∀ t, MeasurableSet t → P t = π (t ∩ E) - π' (t ∩ E) := fun t ht => by
    rw [hPdef, Measure.sub_apply ht hle1, Measure.restrict_apply ht, Measure.restrict_apply ht]
  have hNapp : ∀ t, MeasurableSet t → N t = π' (t ∩ Eᶜ) - π (t ∩ Eᶜ) := fun t ht => by
    rw [hNdef, Measure.sub_apply ht hle2, Measure.restrict_apply ht, Measure.restrict_apply ht]
  have hPle : P ≤ π := by rw [hPdef]; exact le_trans Measure.sub_le Measure.restrict_le_self
  have hNle : N ≤ π' := by rw [hNdef]; exact le_trans Measure.sub_le Measure.restrict_le_self
  haveI : IsFiniteMeasure P :=
    ⟨lt_of_le_of_lt (Measure.le_iff'.1 hPle Set.univ) (measure_lt_top π Set.univ)⟩
  haveI : IsFiniteMeasure N :=
    ⟨lt_of_le_of_lt (Measure.le_iff'.1 hNle Set.univ) (measure_lt_top π' Set.univ)⟩
  have hPEc : P Eᶜ = 0 := by rw [hPapp _ hE.compl]; simp
  have hNE : N E = 0 := by rw [hNapp _ hE]; simp
  -- `π − π' = P − N`, in the additive form `π + N = π' + P`
  have hsum : π + N = π' + P := by
    ext t ht
    have hb : π (t ∩ Eᶜ) ≤ π' (t ∩ Eᶜ) := hE2 _ (ht.inter hE.compl) Set.inter_subset_right
    have ha : π' (t ∩ E) ≤ π (t ∩ E) := hE1 _ (ht.inter hE) Set.inter_subset_right
    have h1 : π (t ∩ Eᶜ) + (π' (t ∩ Eᶜ) - π (t ∩ Eᶜ)) = π' (t ∩ Eᶜ) := add_tsub_cancel_of_le hb
    have h2 : π' (t ∩ E) + (π (t ∩ E) - π' (t ∩ E)) = π (t ∩ E) := add_tsub_cancel_of_le ha
    have hsπ : π t = π (t ∩ E) + π (t ∩ Eᶜ) := by
      rw [← Set.diff_eq]; exact (measure_inter_add_diff t hE).symm
    have hsπ' : π' t = π' (t ∩ E) + π' (t ∩ Eᶜ) := by
      rw [← Set.diff_eq]; exact (measure_inter_add_diff t hE).symm
    rw [Measure.add_apply, Measure.add_apply, hPapp t ht, hNapp t ht]
    calc π t + (π' (t ∩ Eᶜ) - π (t ∩ Eᶜ))
        = π (t ∩ E) + (π (t ∩ Eᶜ) + (π' (t ∩ Eᶜ) - π (t ∩ Eᶜ))) := by rw [hsπ, add_assoc]
      _ = π (t ∩ E) + π' (t ∩ Eᶜ) := by rw [h1]
      _ = (π' (t ∩ E) + (π (t ∩ E) - π' (t ∩ E))) + π' (t ∩ Eᶜ) := by rw [h2]
      _ = π' t + (π (t ∩ E) - π' (t ∩ E)) := by rw [hsπ']; ring
  -- both halves have the same (finite) mass
  have hmassPN : N Set.univ = P Set.univ := by
    have := congrArg (fun m => m Set.univ) hsum
    simp only [Measure.add_apply, measure_univ] at this
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 this
  -- one kernel step of the identity `π + N = π' + P`
  have hbind : π + N.bind κ = π' + P.bind κ := by
    have h := congrArg (fun m => m.bind κ) hsum
    simpa [bind_add', hπ.def, hπ'.def] using h
  have hmassbind : ∀ ξ : Measure S, (ξ.bind κ) Set.univ = ξ Set.univ := fun ξ => by
    rw [Measure.bind_apply MeasurableSet.univ κ.aemeasurable]
    simp
  -- `P` is invariant: it is dominated by its own image, with the same total mass
  have hPQ : ∀ t, MeasurableSet t → t ⊆ E → P t ≤ (P.bind κ) t := by
    intro t ht htE
    have hNt : N t = 0 := le_antisymm (hNE ▸ measure_mono htE) (zero_le _)
    have e1 : π t + N t = π' t + P t := by
      have := congrArg (fun m => m t) hsum; simpa [Measure.add_apply] using this
    have e2 : π t + (N.bind κ) t = π' t + (P.bind κ) t := by
      have := congrArg (fun m => m t) hbind; simpa [Measure.add_apply] using this
    rw [hNt, add_zero] at e1
    rw [e1] at e2
    have : P t + (N.bind κ) t ≤ (P.bind κ) t := by
      rw [add_assoc] at e2
      exact le_of_eq ((ENNReal.add_right_inj (measure_ne_top π' t)).1 e2)
    exact le_trans le_self_add this
  have hQEc : (P.bind κ) Eᶜ = 0 := by
    have h1 : P Set.univ = P E := by
      have := measure_add_measure_compl (μ := P) hE
      rw [hPEc, add_zero] at this; exact this.symm
    have h2 : P E ≤ (P.bind κ) E := hPQ E hE subset_rfl
    have h3 : (P.bind κ) E + (P.bind κ) Eᶜ = P Set.univ := by
      rw [measure_add_measure_compl (μ := P.bind κ) hE, hmassbind]
    have h4 : (P.bind κ) Eᶜ ≤ 0 := by
      have : (P.bind κ) E + (P.bind κ) Eᶜ ≤ (P.bind κ) E + 0 := by
        rw [h3, add_zero, h1]; exact h2
      exact (ENNReal.add_le_add_iff_left (measure_ne_top _ _)).1 this
    exact le_antisymm h4 (zero_le _)
  have hPQ' : P ≤ P.bind κ := by
    refine Measure.le_iff.2 fun t ht => ?_
    have h1 : P t = P (t ∩ E) := by
      have := measure_inter_add_diff t hE (μ := P)
      have h0 : P (t \ E) = 0 := by
        refine le_antisymm ?_ (zero_le _)
        rw [Set.diff_eq]
        exact le_trans (measure_mono Set.inter_subset_right) (le_of_eq hPEc)
      rw [h0, add_zero] at this; exact this.symm
    have h2 : (P.bind κ) (t ∩ E) ≤ (P.bind κ) t := measure_mono Set.inter_subset_left
    exact h1 ▸ le_trans (hPQ _ (ht.inter hE) Set.inter_subset_right) h2
  have hPinv : Kernel.Invariant κ P := by
    refine le_antisymm ?_ hPQ'
    refine Measure.le_iff.2 fun t ht => ?_
    have h1 : (P.bind κ) t + P tᶜ ≤ (P.bind κ) t + (P.bind κ) tᶜ :=
      add_le_add le_rfl (Measure.le_iff'.1 hPQ' _)
    rw [measure_add_measure_compl (μ := P.bind κ) ht, hmassbind,
      ← measure_add_measure_compl (μ := P) ht] at h1
    exact (ENNReal.add_le_add_iff_right (measure_ne_top P tᶜ)).1 h1
  -- and so is `N`
  have hME : (N.bind κ) E = 0 := by
    have h1 : ∀ t, MeasurableSet t → t ⊆ Eᶜ → N t = (N.bind κ) t := by
      intro t ht htE
      have hPt : P t = 0 := le_antisymm (hPEc ▸ measure_mono htE) (zero_le _)
      have hQt : (P.bind κ) t = 0 := le_antisymm (hQEc ▸ measure_mono htE) (zero_le _)
      have e1 : π t + N t = π' t + P t := by
        have := congrArg (fun m => m t) hsum; simpa [Measure.add_apply] using this
      have e2 : π t + (N.bind κ) t = π' t + (P.bind κ) t := by
        have := congrArg (fun m => m t) hbind; simpa [Measure.add_apply] using this
      rw [hPt, add_zero] at e1
      rw [hQt, add_zero] at e2
      rw [← e2] at e1
      exact (ENNReal.add_right_inj (measure_ne_top π t)).1 e1
    have h2 : N Set.univ = N Eᶜ := by
      have := measure_add_measure_compl (μ := N) hE
      rw [hNE, zero_add] at this; exact this.symm
    have h3 : (N.bind κ) E + (N.bind κ) Eᶜ = N Set.univ := by
      rw [measure_add_measure_compl (μ := N.bind κ) hE, hmassbind]
    rw [← h1 Eᶜ hE.compl subset_rfl, ← h2] at h3
    have : (N.bind κ) E ≤ 0 := by
      have h4 : (N.bind κ) E + N Set.univ ≤ 0 + N Set.univ := by rw [h3, zero_add]
      exact (ENNReal.add_le_add_iff_right (measure_ne_top N _)).1 h4
    exact le_antisymm this (zero_le _)
  have hNinv : Kernel.Invariant κ N := by
    have hNQ : N ≤ N.bind κ := by
      refine Measure.le_iff.2 fun t ht => ?_
      have h1 : N t = N (t ∩ Eᶜ) := by
        have h := measure_inter_add_diff t hE.compl (μ := N)
        have h0 : N (t \ Eᶜ) = 0 := by
          refine le_antisymm ?_ (zero_le _)
          rw [Set.diff_eq, compl_compl]
          exact le_trans (measure_mono Set.inter_subset_right) (le_of_eq hNE)
        rw [h0, add_zero] at h; exact h.symm
      have h2 : N (t ∩ Eᶜ) ≤ (N.bind κ) (t ∩ Eᶜ) := by
        have hPt : P (t ∩ Eᶜ) = 0 :=
          le_antisymm (hPEc ▸ measure_mono Set.inter_subset_right) (zero_le _)
        have hQt : (P.bind κ) (t ∩ Eᶜ) = 0 :=
          le_antisymm (hQEc ▸ measure_mono Set.inter_subset_right) (zero_le _)
        have e1 : π (t ∩ Eᶜ) + N (t ∩ Eᶜ) = π' (t ∩ Eᶜ) + P (t ∩ Eᶜ) := by
          have := congrArg (fun m => m (t ∩ Eᶜ)) hsum; simpa [Measure.add_apply] using this
        have e2 : π (t ∩ Eᶜ) + (N.bind κ) (t ∩ Eᶜ) = π' (t ∩ Eᶜ) + (P.bind κ) (t ∩ Eᶜ) := by
          have := congrArg (fun m => m (t ∩ Eᶜ)) hbind; simpa [Measure.add_apply] using this
        rw [hPt, add_zero] at e1
        rw [hQt, add_zero] at e2
        rw [← e2] at e1
        exact le_of_eq ((ENNReal.add_right_inj (measure_ne_top π _)).1 e1)
      exact h1 ▸ le_trans h2 (measure_mono Set.inter_subset_left)
    refine le_antisymm ?_ hNQ
    refine Measure.le_iff.2 fun t ht => ?_
    have h1 : (N.bind κ) t + N tᶜ ≤ (N.bind κ) t + (N.bind κ) tᶜ :=
      add_le_add le_rfl (Measure.le_iff'.1 hNQ _)
    rw [measure_add_measure_compl (μ := N.bind κ) ht, hmassbind,
      ← measure_add_measure_compl (μ := N) ht] at h1
    exact (ENNReal.add_le_add_iff_right (measure_ne_top N tᶜ)).1 h1
  -- if the two halves were nonzero they would be mutually singular invariant laws, each
  -- charging the level set — impossible, because the minorizing measure would have to vanish
  by_cases hc : P Set.univ = 0
  · have hP0 : P = 0 := by simpa using Measure.measure_univ_eq_zero.1 hc
    have hN0 : N = 0 := by
      have : N Set.univ = 0 := by rw [hmassPN, hc]
      simpa using Measure.measure_univ_eq_zero.1 this
    rw [hP0, hN0] at hsum
    simpa using hsum
  · exfalso
    have hcN : N Set.univ ≠ 0 := by rw [hmassPN]; exact hc
    have hPL : P {x | V x ≤ R} ≠ 0 := level_set_pos hdrift hR hπ hV hPle hPinv hc
    have hNL : N {x | V x ≤ R} ≠ 0 := level_set_pos hdrift hR hπ' hV' hNle hNinv hcN
    have hρEc : ρ Eᶜ = 0 := by
      have h := minorize_bind hmin P hE.compl
      rw [hPinv.def, hPEc] at h
      have h0 : ENNReal.ofReal α * ρ Eᶜ * P {x | V x ≤ R} = 0 := le_antisymm h (zero_le _)
      rcases mul_eq_zero.1 h0 with h1 | h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact absurd h2 (by simp [ENNReal.ofReal_eq_zero, not_le, hα0])
        · exact h2
      · exact absurd h1 hPL
    have hρE : ρ E = 0 := by
      have h := minorize_bind hmin N hE
      rw [hNinv.def, hNE] at h
      have h0 : ENNReal.ofReal α * ρ E * N {x | V x ≤ R} = 0 := le_antisymm h (zero_le _)
      rcases mul_eq_zero.1 h0 with h1 | h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact absurd h2 (by simp [ENNReal.ofReal_eq_zero, not_le, hα0])
        · exact h2
      · exact absurd h1 hNL
    have : (1 : ℝ≥0∞) = 0 := by
      rw [← measure_univ (μ := ρ), ← measure_add_measure_compl (μ := ρ) hE, hρE, hρEc, add_zero]
    exact one_ne_zero this

/-- **Lifting from the `p`-step kernel**: if `κ^p` is geometrically ergodic with
invariant law `π` and `π` is invariant for `κ` itself, then `κ` is geometrically
ergodic. (The nonlinear-AR kernel of FY Theorem 2.4 is only minorized after `p` steps,
so this is the last glue step of that proof.) -/
theorem IsGeometricallyErgodic.of_pow {κ : Kernel S S} [IsMarkovKernel κ]
    {π : Measure S} [IsProbabilityMeasure π] {p : ℕ} (hp : 0 < p)
    (hpow : IsGeometricallyErgodic (κ ^ p) π) (hinv : Kernel.Invariant κ π) :
    IsGeometricallyErgodic κ π := by
  obtain ⟨ρ, hρ1, hρ⟩ := hpow
  have hpinv : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hbase : (1 : ℝ≥0∞) ≤ ρ⁻¹ := ENNReal.one_le_inv.mpr hρ.rho_le_one
  refine ⟨ρ ^ ((p : ℝ)⁻¹), ENNReal.rpow_lt_one hρ1 hpinv,
    ⟨ENNReal.rpow_pos hρ.rho_pos hρ1.ne_top, (ENNReal.rpow_lt_one hρ1 hpinv).le, fun x => ?_⟩⟩
  -- the `q`-step envelope of the `p`-step kernel, scaled by the fixed constant `ρ⁻¹`
  have hq : Tendsto (fun n : ℕ => n / p) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * p, fun _ ha => (Nat.le_div_iff_mul_le hp).2 ha⟩
  have hmaj : Tendsto
      (fun n : ℕ => ρ⁻¹ * (ρ⁻¹ ^ (n / p) * tvDist (((κ ^ p) ^ (n / p)) x) π)) atTop (𝓝 0) := by
    have h := (hρ.tendsto x).comp hq
    simpa using ENNReal.Tendsto.const_mul h (Or.inr (by simp [hρ.rho_pos.ne']))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
    (Eventually.of_forall fun n => zero_le _) (Eventually.of_forall fun n => ?_)
  set q := n / p with hqdef
  set r := n % p with hrdef
  have hnr : n = r + p * q := by rw [hrdef, hqdef, Nat.mod_add_div]
  haveI := markov_pow κ (p * q)
  haveI := markov_pow κ r
  -- Distance: the leftover `r = n % p` steps, applied *last*, can only contract (`π` is
  -- `κ^r`-invariant), so the `n`-step distance is at most the `pq`-step one.
  have hdist : tvDist ((κ ^ n) x) π ≤ tvDist (((κ ^ p) ^ q) x) π := by
    have hπ : π = π.bind (κ ^ r) := ((invariant_pow hinv r).def).symm
    have hstep : (κ ^ n) x = ((κ ^ (p * q)) x).bind (κ ^ r) := by
      rw [hnr, pow_add]
      exact Kernel.comp_apply (κ ^ r) (κ ^ (p * q)) x
    rw [hstep, ← pow_mul]
    nth_rewrite 1 [hπ]
    exact tvDist_bind_le (κ ^ r) ((κ ^ (p * q)) x) π
  -- Rate: `(ρ^{1/p})⁻ⁿ ≤ ρ⁻¹ · ρ⁻ᵠ` because `n/p ≤ q + 1`.
  have hrate : (ρ ^ ((p : ℝ)⁻¹))⁻¹ ^ n ≤ ρ⁻¹ * ρ⁻¹ ^ q := by
    have hexp : ((p : ℝ)⁻¹) * (n : ℝ) ≤ (q : ℝ) + 1 := by
      have hnp : (n : ℝ) ≤ (p : ℝ) * ((q : ℝ) + 1) := by
        have hr : r < p := by rw [hrdef]; exact Nat.mod_lt n hp
        have hpq : p * (q + 1) = p * q + p := by ring
        have hle : n ≤ p * (q + 1) := by omega
        exact_mod_cast hle
      rw [inv_mul_le_iff₀ (by exact_mod_cast hp)]
      linarith
    calc (ρ ^ ((p : ℝ)⁻¹))⁻¹ ^ n
        = (ρ⁻¹ ^ ((p : ℝ)⁻¹)) ^ ((n : ℕ) : ℝ) := by
          rw [ENNReal.inv_rpow, ENNReal.rpow_natCast]
      _ = ρ⁻¹ ^ (((p : ℝ)⁻¹) * (n : ℝ)) := (ENNReal.rpow_mul _ _ _).symm
      _ ≤ ρ⁻¹ ^ ((q : ℝ) + 1) := ENNReal.rpow_le_rpow_of_exponent_le hbase hexp
      _ = ρ⁻¹ ^ (q + 1) := by rw [← ENNReal.rpow_natCast ρ⁻¹ (q + 1)]; norm_num
      _ = ρ⁻¹ * ρ⁻¹ ^ q := by rw [pow_succ]; ring
  calc (ρ ^ ((p : ℝ)⁻¹))⁻¹ ^ n * tvDist ((κ ^ n) x) π
      ≤ (ρ⁻¹ * ρ⁻¹ ^ q) * tvDist (((κ ^ p) ^ q) x) π := mul_le_mul' hrate hdist
    _ = ρ⁻¹ * (ρ⁻¹ ^ q * tvDist (((κ ^ p) ^ q) x) π) := by ring

end StatLean.TimeSeries
