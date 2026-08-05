import StatLean.TimeSeries.Mixing.Defs
import StatLean.TimeSeries.Process.Stationary
import StatLean.TimeSeries.Models.WhiteNoise
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Relations between the mixing coefficients (FY §2.6.1, pp. 68–71)

Basic properties of the five dependence coefficients of `Mixing/Defs.lean` and the
classical implication chain `ψ-mixing ⇒ φ-mixing ⇒ {β-, ρ-mixing} ⇒ α-mixing`
(FY §2.6.1 "basic facts", cited to Bradley 1986):

* set-level basics: the description sets are nonempty and bounded, the coefficients
  nonnegative; `α ≤ 1`, monotone in both σ-algebra arguments; process coefficients
  antitone in the lag;
* provable coefficient inequalities: `2α ≤ β`, `α ≤ φ`, `β ≤ φ`, `φ ≤ 2ψ`-form,
  `α ≤ ¼ρ` (FY's display `α(k) ≤ ¼ρ(k)`);
* the Bradley square-root relation `ρ ≤ 2√φ` (giving FY's `¼ρ(k) ≤ ½φ^{1/2}(k)`) —
  literature DEBT;
* heredity under instantaneous measurable transforms;
* the shift lemma: under strict stationarity the anchored coefficients equal the
  coefficients between any `k`-shifted past/future pair (the property FY uses silently
  in every block argument);
* the in-text non-example (ix): a deterministic recursion `X_{t+1} = m(X_t)` with a
  non-degenerate event is not α-mixing;
* literature statement DEBTS: Pham–Tran (causal ARMA with absolutely continuous iid
  innovations is exponentially β-mixing), Basrak–Davis–Mikosch (GARCH is exponentially
  α-mixing), Kolmogorov–Rozanov (Gaussian: ρ-mixing ⇔ α-mixing).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.1
(pp. 68–71). (`FY §2.6.1`.)

**Proof formalization notes.**
* `2α ≤ β`: the four-set partition `{A, Aᶜ} × {B, Bᶜ}` has partition sum
  `4|P(A∩B) − P(A)P(B)|`.
* `α ≤ φ`: `|P(A∩B) − P(A)P(B)| = P(A)·|P(B|A) − P(B)| ≤ φ` (the `P(A) = 0` term
  vanishes).
* `β ≤ φ`: for a partition pair, `Σ_j |P(B_j|A_i) − P(B_j)| ≤ 2 sup_B |P(B|A_i) − P(B)|`
  (split the sum by sign; each signed half is a single event).
* `α ≤ ¼ρ`: centered indicators, `Cov(1_A, 1_B) = P(A∩B) − P(A)P(B)` and
  `Var(1_A) = P(A)(1−P(A)) ≤ ¼`.
* The shift lemma transports the description sets through the path map; strict
  stationarity is exactly invariance of the path law under the shift.

**Bibliographic comments.** The implication chain and the sharp constants are collected
in R. C. Bradley, *Basic properties of strong mixing conditions* (in Eberlein–Taqqu,
1986) and his 2005 survey; `ρ ≤ 2√φ` is due to Peligrad (after Cogburn and Ibragimov).
Pham & Tran, *Some mixing properties of time series models*, SPA 1985; Basrak, Davis &
Mikosch, *Regular variation of GARCH processes*, SPA 2002; Kolmogorov & Rozanov 1960
for the Gaussian ρ ⇔ α equivalence.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

/-! ### Set-level basics

Two-σ-algebra statements follow the Mathlib `condExp` binder convention: the ambient
σ-algebra `mΩ` is a plain implicit bound *after* the sub-σ-algebras and immediately
before `μ`, so that local-instance resolution and unification agree (an
instance-implicit ambient would be shadowed by the sub-σ-algebra binders). -/

section TwoAlgebras

variable {Ω : Type*}

/-- On a probability space every measure is at most `1` after `toReal`. -/
private lemma toReal_le_one {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Set Ω) : (μ s).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ s))

/-- Every value in the α description set is bounded by `1`. -/
private lemma abs_alpha_term_le_one {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (A B : Set Ω) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ 1 := by
  have h1 := toReal_le_one (μ := μ) (A ∩ B)
  have h2 := toReal_le_one (μ := μ) A
  have h3 := toReal_le_one (μ := μ) B
  have h0 : (0 : ℝ) ≤ (μ (A ∩ B)).toReal := ENNReal.toReal_nonneg
  have h0a : (0 : ℝ) ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have h0b : (0 : ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> nlinarith

/-- The α description set contains `0` (take `A = ∅`). -/
theorem alphaMixCoeff_set_nonempty {m₁ m₂ mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    (0 : ℝ) ∈ {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
      r = |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|} :=
  ⟨∅, ∅, @MeasurableSet.empty Ω m₁, @MeasurableSet.empty Ω m₂, by simp⟩

/-- On a probability space the α description set is bounded above by `1`. -/
theorem alphaMixCoeff_set_bddAbove {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    BddAbove {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
      r = |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨A, B, -, -, rfl⟩
  exact abs_alpha_term_le_one A B

/-- `0 ≤ α`. -/
theorem alphaMixCoeff_nonneg {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    0 ≤ alphaMixCoeff μ m₁ m₂ :=
  le_csSup (alphaMixCoeff_set_bddAbove (mΩ := mΩ)) (alphaMixCoeff_set_nonempty (mΩ := mΩ) μ)

/-- `α ≤ 1` (indeed `α ≤ ¼`, but FY only uses boundedness). -/
theorem alphaMixCoeff_le_one {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    alphaMixCoeff μ m₁ m₂ ≤ 1 :=
  Real.sSup_le (by rintro r ⟨A, B, -, -, rfl⟩; exact abs_alpha_term_le_one A B) zero_le_one

/-- α is monotone in both σ-algebra arguments. -/
theorem alphaMixCoeff_mono {m₁ m₂ m₁' m₂' mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁' ≤ m₁) (h₂ : m₂' ≤ m₂) :
    alphaMixCoeff μ m₁' m₂' ≤ alphaMixCoeff μ m₁ m₂ := by
  refine csSup_le_csSup (alphaMixCoeff_set_bddAbove (mΩ := mΩ))
    ⟨0, alphaMixCoeff_set_nonempty (mΩ := mΩ) μ⟩ ?_
  rintro r ⟨A, B, hA, hB, rfl⟩
  exact ⟨A, B, h₁ _ hA, h₂ _ hB, rfl⟩

end TwoAlgebras

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The process α-coefficient is antitone in the lag (FY: "monotone nonincreasing",
used silently; from `sigmaGE X (n+1) ≤ sigmaGE X n`). -/
theorem alphaCoeff_antitone [IsProbabilityMeasure μ] (X : ℤ → Ω → ℝ) :
    Antitone fun n : ℕ => alphaCoeff X μ n := by
  intro a b hab
  refine alphaMixCoeff_mono le_rfl ?_
  refine iSup₂_le fun s hs => ?_
  have hs' : (b : ℤ) ≤ s := hs
  refine le_iSup₂_of_le s (Set.mem_Ici.mpr ?_) le_rfl
  exact le_trans (by exact_mod_cast hab) hs'

end Process

/-! ### Provable coefficient inequalities (FY §2.6.1 basic facts) -/

section TwoAlgebras2

variable {Ω : Type*}

/-- `2α ≤ β` (four-set partitions witness the α events). -/
theorem two_mul_alphaMixCoeff_le_betaMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    2 * alphaMixCoeff μ m₁ m₂ ≤ betaMixCoeff μ m₁ m₂ := by
  sorry

/-- `α ≤ φ`. -/
theorem alphaMixCoeff_le_phiMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    alphaMixCoeff μ m₁ m₂ ≤ phiMixCoeff μ m₁ m₂ := by
  sorry

/-- `β ≤ φ` (partition sums against a fixed past cell are conditional-probability
discrepancies). -/
theorem betaMixCoeff_le_phiMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    betaMixCoeff μ m₁ m₂ ≤ phiMixCoeff μ m₁ m₂ := by
  sorry

/-- `φ ≤ ψ` in the calibrated form `|P(B) − P(B|A)| = P(B)|1 − P(B|A)/P(B)|`
(the `P(B) = 0` cell contributes `0` on both sides). -/
theorem phiMixCoeff_le_psiMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    phiMixCoeff μ m₁ m₂ ≤ psiMixCoeff μ m₁ m₂ := by
  sorry

/-- **FY's display** `α ≤ ¼ρ` (centered indicators; `Var 1_A ≤ ¼`). -/
theorem alphaMixCoeff_le_quarter_mul_rhoMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    alphaMixCoeff μ m₁ m₂ ≤ (1 / 4) * rhoMixCoeff μ m₁ m₂ := by
  sorry

/-- **DEBT (Bradley/Peligrad; FY §2.6.1 display `¼ρ ≤ ½√φ`)**: the square-root
relation `ρ ≤ 2√φ`. Literature-level; the proof needs the L²-duality description of
`ρ` and a two-sided conditional Cauchy–Schwarz argument. -/
theorem rhoMixCoeff_le_two_mul_sqrt_phiMixCoeff_debt {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    rhoMixCoeff μ m₁ m₂ ≤ 2 * Real.sqrt (phiMixCoeff μ m₁ m₂) := by
  sorry

end TwoAlgebras2

/-! ### Mixing-class implications (FY Definition 2.11 chain) -/

section Process2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- ψ-mixing ⇒ φ-mixing. -/
theorem IsPsiMixing.isPhiMixing [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (h : IsPsiMixing X μ) : IsPhiMixing X μ := by
  sorry

/-- φ-mixing ⇒ β-mixing. -/
theorem IsPhiMixing.isBetaMixing [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (h : IsPhiMixing X μ) : IsBetaMixing X μ := by
  sorry

/-- β-mixing ⇒ α-mixing. -/
theorem IsBetaMixing.isAlphaMixing [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (h : IsBetaMixing X μ) : IsAlphaMixing X μ := by
  sorry

/-- ρ-mixing ⇒ α-mixing. -/
theorem IsRhoMixing.isAlphaMixing [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (h : IsRhoMixing X μ) : IsAlphaMixing X μ := by
  sorry

/-! ### Heredity and the shift lemma -/

/-- **Heredity** (FY §2.6.1(iv)): an instantaneous measurable transform
`Y_t = g(X_t)` has smaller past/future σ-algebras, hence smaller α-coefficients; α-mixing
is inherited. (The same argument applies verbatim to β, ρ, φ, ψ via
`alphaMixCoeff_mono`-analogues; α is the one consumed downstream.) -/
theorem IsAlphaMixing.comp [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (h : IsAlphaMixing X μ) {g : ℝ → ℝ} (hg : Measurable g) :
    IsAlphaMixing (fun t ω => g (X t ω)) μ := by
  sorry

/-- **Shift lemma** (used silently by every FY block argument): under strict
stationarity, the α-coefficient between the past up to `k` and the future from `k + n`
does not depend on the anchor `k`. -/
theorem IsStrictlyStationary.alphaMixCoeff_shift [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hstat : IsStrictlyStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) (k : ℤ) (n : ℕ) :
    alphaMixCoeff μ (sigmaLE X k) (sigmaGE X (k + n)) = alphaCoeff X μ n := by
  sorry

/-! ### The deterministic non-example (FY §2.6.1(ix)) -/

/-- **FY §2.6.1(ix), quantitative core**: for a deterministic recursion
`X_{t+1} = m(X_t)` every event of the time-`n` state lies in the past σ-algebra as
well, so `α(n) ≥ P(X_n ∈ C)(1 − P(X_n ∈ C))`. -/
theorem alphaCoeff_ge_of_deterministic [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) {m : ℝ → ℝ} (hm : Measurable m)
    -- USER-INPUT: deterministic recursion; FY §2.6.1(ix)
    (hrec : ∀ t : ℤ, ∀ ω, X (t + 1) ω = m (X t ω))
    {C : Set ℝ} (hC : MeasurableSet C) (n : ℕ) :
    (μ (X n ⁻¹' C)).toReal * (1 - (μ (X n ⁻¹' C)).toReal)
      ≤ alphaCoeff X μ n := by
  sorry

/-- **FY §2.6.1(ix)**: a deterministic recursion with uniformly non-degenerate events is
not α-mixing. -/
theorem not_isAlphaMixing_of_deterministic [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) {m : ℝ → ℝ} (hm : Measurable m)
    (hrec : ∀ t : ℤ, ∀ ω, X (t + 1) ω = m (X t ω))
    -- USER-INPUT: uniform non-degeneracy of some tail events; FY §2.6.1(ix)
    {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1 / 2)
    (hC : ∀ n : ℕ, ∃ C : Set ℝ, MeasurableSet C ∧
      c ≤ (μ (X n ⁻¹' C)).toReal ∧ (μ (X n ⁻¹' C)).toReal ≤ 1 - c) :
    ¬ IsAlphaMixing X μ := by
  sorry

/-! ### Literature statement DEBTS (FY §2.6.1(v), (viii), (x)) -/

/-- **DEBT (Pham–Tran 1985; FY §2.6.1(v))**: a stationary causal ARMA process with
iid innovations admitting an (absolutely continuous) density is exponentially
β-mixing. -/
theorem arma_betaCoeff_exponential_debt [IsProbabilityMeasure μ]
    {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hstat : IsStrictlyStationary X μ)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: iid innovations with a Lebesgue density; Pham–Tran 1985
    (hiid : IsIIDNoise ε σ2 μ)
    (hdens : ∃ g : ℝ → ℝ, Measurable g ∧
      μ.map (ε 0) = MeasureTheory.volume.withDensity fun x => ENNReal.ofReal (g x))
    -- USER-INPUT: no roots of b on the closed unit disc (causality; stated inline —
    -- this concept-layer file must not import `Stationarity/ARMAExistence`); FY §2.1
    (hroot : ∀ z : ℂ, ‖z‖ ≤ 1 → Polynomial.aeval z (arPoly b) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ n : ℕ, betaCoeff X μ n ≤ C * r ^ n := by
  sorry

/-- **DEBT (Basrak–Davis–Mikosch 2002; FY §2.6.1(x))**: a strictly stationary
GARCH(p, q) process with `Σᵢ bᵢ + Σⱼ aⱼ < 1` whose iid innovations have a Lebesgue
density positive in a neighbourhood of `0` is exponentially α-mixing. -/
theorem garch_alphaCoeff_exponential_debt [IsProbabilityMeasure μ]
    {c0 : ℝ} {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: contraction of the GARCH coefficients; BDM 2002 / FY §2.6.1(x)
    (hsum : ∑ i, b i + ∑ j, a j < 1)
    -- USER-INPUT: innovation density positive near zero; BDM 2002
    (hdens : ∃ g : ℝ → ℝ, Measurable g ∧
      μ.map (ε 0) = MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x| < δ → 0 < g x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ n : ℕ, alphaCoeff X μ n ≤ C * r ^ n := by
  sorry

/-- **DEBT (Kolmogorov–Rozanov 1960; FY §2.6.1(viii))**: for a (strictly stationary)
Gaussian process, α-mixing already implies ρ-mixing (the coefficients are comparable:
`ρ(n) ≤ 2π α(n)`). -/
theorem gaussian_rho_le_alpha_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: Gaussian process; Kolmogorov–Rozanov
    (hgauss : ProbabilityTheory.IsGaussianProcess X μ) (n : ℕ) :
    rhoCoeff X μ n ≤ 2 * Real.pi * alphaCoeff X μ n := by
  sorry

end Process2

end StatLean.TimeSeries
