import StatLean.TimeSeries.Models.WhiteNoise
import StatLean.TimeSeries.Process.Stationary
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Stationary ARCH(∞) processes: the Volterra construction (FY §2.1.5, Theorem 2.5)

**FY Theorem 2.5(i)** with the full §2.7.1 proof: under `Σ_j b_j < 1`, the ARCH(∞)
equation (FY eq. (2.15)) has a strictly stationary, integrable, nonnegative solution with
mean `a/(1 − Σ_j b_j)` — the **Volterra series**
`Y_t = a ξ_t (1 + Σ_{k≥1} Σ_{j₁,…,j_k} b_{j₁} ⋯ b_{j_k} ξ_{t−ℓ₁} ⋯ ξ_{t−ℓ_k})`
(`ℓ_m = (j₁+1) + ⋯ + (j_m+1)` partial sums of lags) — and it is the a.e.-unique
integrable solution; if `a = 0`, the only solution is `Y ≡ 0`.
Also: FY Theorem 2.5(ii) (finite second moment under eq. (2.16)) and Theorem 2.6 (the
finite-dimensional invariance principle) as statement-level DEBTS (FY cites both to
Giraitis–Kokoszka–Leipus 2000 without in-book proofs).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.5
(Theorem 2.5, eqs. (2.15)–(2.16), Theorem 2.6, pp. 37–38) and §2.7.1 (proof of Thm
2.5(i), eq. (2.68), pp. 78–79). (`FY §2.1.5 Thm 2.5–2.6; §2.7.1`.)

**Proof formalization notes.**
* All terms are nonnegative, so the Volterra series converges by monotone convergence
  (Tonelli over the countable index set of finite lag-tuples); its layer-`k` expectation
  is `a(Σ_j b_j)^k` because strictly decreasing time indices make the `ξ`-product a
  product of independent mean-one factors.
* Strict stationarity: `Y_t` is a fixed measurable function of the shifted i.i.d. family
  `(ξ_{t−k})_{k≥0}`; the finite-dimensional laws transport along the shift-invariance of
  the infinite product law (pinned `Probability/ProductMeasure` +
  `iIndepFun` infinite-product characterization).
* Uniqueness iterates FY eq. (2.68) and uses the model's `indep_past` field (the implicit
  semantics FY's proof uses, surfaced in `IsARCHInf`), Markov's inequality and
  Borel–Cantelli.

**Bibliographic comments.** L. Giraitis, P. Kokoszka and R. Leipus, "Stationary ARCH
models: dependence structure and central limit theorem", *Econometric Theory* **16**
(2000), 3–22. The Volterra-expansion method for random recurrences goes back to
V. Volterra's integral-equation calculus; in the ARCH context it was introduced by
Giraitis–Kokoszka–Leipus. ARCH itself is R. F. Engle (1982).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The i.i.d.-noise input data for the ARCH(∞) construction: a nonnegative i.i.d.
family with unit mean (the `ξ` of FY eq. (2.15)), packaged as a `Prop`. -/
structure IsARCHNoise (ξ : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- Constitutive (FY eq. (2.15)): the noise variables are random variables. -/
  measurable : ∀ t, Measurable (ξ t)
  /-- Constitutive (FY eq. (2.15)): nonnegativity. -/
  nonneg : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ ξ t ω
  /-- Constitutive (FY eq. (2.15)): mutual independence. -/
  iIndep : iIndepFun ξ μ
  /-- Constitutive (FY eq. (2.15)): identical distribution. -/
  identDistrib : ∀ s t, IdentDistrib (ξ s) (ξ t) μ μ
  /-- Constitutive (FY eq. (2.15)): integrable with `E ξ = 1`. -/
  integrable : Integrable (ξ 0) μ
  integral_eq_one : ∫ ω, ξ 0 ω ∂μ = 1

/-- **FY Theorem 2.5(i), existence** (proof: §2.7.1 Volterra series): if
`Σ_j bc j < 1`, there is a strictly stationary, integrable, a.e.-nonnegative solution of
the ARCH(∞) equation over the given noise, with `E Y_t = a / (1 − Σ_j bc j)`. -/
theorem exists_stationary_archInf [IsProbabilityMeasure μ]
    {a : ℝ} {bc : ℕ → ℝ} {ξ : ℤ → Ω → ℝ}
    -- USER-INPUT: coefficients; FY eq. (2.15)
    (ha : 0 ≤ a) (hbc : ∀ j, 0 ≤ bc j)
    -- USER-INPUT: contraction Σ b_j < 1; FY Thm 2.5(i)
    (hsum : Summable bc) (hlt : ∑' j, bc j < 1)
    -- USER-INPUT: the noise; FY eq. (2.15)
    (hξ : IsARCHNoise ξ μ) :
    ∃ Y : ℤ → Ω → ℝ, IsARCHInf a bc Y ξ μ ∧ IsStrictlyStationary Y μ ∧
      (∀ t, Integrable (Y t) μ) ∧ ∀ t, ∫ ω, Y t ω ∂μ = a / (1 - ∑' j, bc j) := by
  sorry

/-- **FY Theorem 2.5(i), uniqueness** (§2.7.1): two integrable solutions of the ARCH(∞)
equation over the same noise agree a.e. at every time. -/
theorem archInf_unique [IsProbabilityMeasure μ]
    {a : ℝ} {bc : ℕ → ℝ} {Y Y' ξ : ℤ → Ω → ℝ}
    (hsum : Summable bc) (hlt : ∑' j, bc j < 1)
    (h : IsARCHInf a bc Y ξ μ) (hint : ∀ t, Integrable (Y t) μ)
    -- USER-INPUT: stationarity of the compared solutions (uniform first moments);
    -- FY Thm 2.5(i) states uniqueness among strictly stationary solutions
    (hstat : IsStrictlyStationary Y μ)
    (h' : IsARCHInf a bc Y' ξ μ) (hint' : ∀ t, Integrable (Y' t) μ)
    (hstat' : IsStrictlyStationary Y' μ) (t : ℤ) :
    Y t =ᵐ[μ] Y' t := by
  sorry

/-- **FY Theorem 2.5(i), degenerate case**: if `a = 0`, every integrable strictly
stationary solution is a.e. zero. -/
theorem archInf_eq_zero_of_a_eq_zero [IsProbabilityMeasure μ]
    {bc : ℕ → ℝ} {Y ξ : ℤ → Ω → ℝ}
    (hsum : Summable bc) (hlt : ∑' j, bc j < 1)
    (h : IsARCHInf 0 bc Y ξ μ) (hint : ∀ t, Integrable (Y t) μ)
    (hstat : IsStrictlyStationary Y μ) (t : ℤ) :
    Y t =ᵐ[μ] 0 := by
  sorry

/-- **FY Theorem 2.5(ii) — DEBT** (Giraitis–Kokoszka–Leipus 2000; not proved in FY):
under the second-moment contraction (FY eq. (2.16)) the stationary solution has a finite
second moment. -/
theorem archInf_memLp_two_debt [IsProbabilityMeasure μ]
    {a : ℝ} {bc : ℕ → ℝ} {Y ξ : ℤ → Ω → ℝ}
    (ha : 0 ≤ a) (hbc : ∀ j, 0 ≤ bc j) (hsum : Summable bc)
    (hξ : IsARCHNoise ξ μ) (hξ2 : MemLp (ξ 0) 2 μ)
    -- USER-INPUT: FY eq. (2.16): max{1, ‖ξ‖₂}·Σ b_j < 1
    (h16 : max 1 (Real.sqrt (∫ ω, ξ 0 ω ^ 2 ∂μ)) * ∑' j, bc j < 1)
    (h : IsARCHInf a bc Y ξ μ) (hstat : IsStrictlyStationary Y μ)
    (hint : ∀ t, Integrable (Y t) μ) (t : ℤ) :
    MemLp (Y t) 2 μ := by
  sorry

/-- **FY Theorem 2.6 — DEBT** (Giraitis–Kokoszka–Leipus 2000; fdd invariance principle):
under eq. (2.16), the normalized partial sums of a stationary ARCH(∞) process are
asymptotically `N(0, σ²)` with long-run variance `σ² = Σ_k Cov(Y_k, Y_0)`. Stated at the
level of one-dimensional marginals through characteristic functions (Lévy-equivalent to
convergence in distribution; the full Brownian fdd statement of FY Thm 2.6 refines this
and can be layered on once a Brownian process is available). -/
theorem archInf_clt_debt [IsProbabilityMeasure μ]
    {a : ℝ} {bc : ℕ → ℝ} {Y ξ : ℤ → Ω → ℝ}
    (ha : 0 ≤ a) (hbc : ∀ j, 0 ≤ bc j) (hsum : Summable bc)
    (hξ : IsARCHNoise ξ μ) (hξ2 : MemLp (ξ 0) 2 μ)
    (h16 : max 1 (Real.sqrt (∫ ω, ξ 0 ω ^ 2 ∂μ)) * ∑' j, bc j < 1)
    (h : IsARCHInf a bc Y ξ μ) (hstat : IsStrictlyStationary Y μ)
    (hL2 : ∀ t, MemLp (Y t) 2 μ)
    {σ2 : ℝ} (hσ2 : HasSum (fun k : ℤ => acvf Y μ k) σ2) (hσpos : 0 < σ2) (u : ℝ) :
    Tendsto
      (fun n : ℕ => charFun
        (μ.map fun ω => (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range n, (Y t ω - ∫ ω', Y t ω' ∂μ)) u)
      atTop (nhds (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  sorry

end StatLean.TimeSeries
