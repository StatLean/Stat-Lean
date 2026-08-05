import StatLean.TimeSeries.Mixing.Defs
import StatLean.TimeSeries.Process.Stationary
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Covariance and moment inequalities under mixing (FY §2.6.2, pp. 71–73)

The quantitative toolbox for α-mixing processes:

* **Proposition 2.5(ii) (Billingsley)**: bounded case, `|Cov(f, g)| ≤ 4 α C₁ C₂`, plus
  the complex version with constant `16` — the workhorse of Proposition 2.6;
* **Proposition 2.5(i) (Davydov)**: `1/p + 1/q < 1` ⇒
  `|Cov(f, g)| ≤ 8 α^{1 − 1/p − 1/q} ‖f‖_p ‖g‖_q` — **built here in full** (FY cites
  Doukhan §1.2.2; truncation of both factors against the bounded case);
* **Proposition 2.6 (Volkonskii–Rozanov)**: complex unit-bounded blocks with α-gaps,
  `|E ∏ ξ_l − ∏ E ξ_l| ≤ 16 (k − 1) a` — the factorization engine of both CLT proofs
  (Theorems 2.21(ii) and 2.22);
* the **fourth-moment bound** (the `q = 4` instance of FY Proposition 2.7(ii) that the
  Bernstein-block CLT consumes): bounded, zero-mean, strictly stationary,
  `α(n) ≤ K n⁻²` ⇒ `E S_n⁴ ≤ C n²`;
* **Theorems 2.18/2.19 (Bosq exponential inequalities)** — literature DEBTS (used only
  by ch. 5 KDE uniform rates, outside the current scope).

**Scope note.** FY's Theorem 2.17 (Doukhan–Louhichi moment bounds via the
covariance-decay functional `M_{r,q}`) and the general-`q` Proposition 2.7 are *not*
stated: their only consumers in scope — Theorems 2.20(i)/2.21(i) — are themselves
cited-out literature debts carrying their own hypotheses, and the CLT proofs consume
only the `q = 4` instance stated here.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.2,
Propositions 2.5–2.7 and Theorems 2.17–2.19 (pp. 71–73). (`FY §2.6.2`.)

**Proof formalization notes.**
* Billingsley: with `η = sgn(E[f g | split])`-free classical argument: write the
  covariance against centered factors and pass to the four-event correlation via
  `f = ∫ (1_{f > t} − 1_{f < −t}) dt`-free discretization — the standard route is
  by the identity `Cov(f, g) = ∫∫ [P(f > s, g > t) − P(f > s)P(g > t)] ds dt`
  (Hoeffding), each integrand bounded by `α`; totals `4 α C₁ C₂` after splitting signs.
* Davydov: truncate at levels `C₁, C₂`, apply the bounded case to the truncations and
  Hölder/Markov to the tails; optimize the levels (`C_i = ‖·‖ · α^{-1/(...)}`) to get
  the exponent `1 − 1/p − 1/q` and constant `8`.
* Volkonskii–Rozanov: induction on `k`; each step peels the last factor with the
  complex bounded inequality (constant 16) against the cumulative-past σ-algebra.
* Fourth moment: expand `E S⁴` over index 4-tuples, split each expectation at the
  largest gap `g` (Billingsley pairs), count tuples with largest gap `g` as `O(n g²)`;
  `Σ_g n g² · g⁻² = O(n²)`, and the paired products contribute `(n Σ α)² = O(n²)`.

**Bibliographic comments.** Prop 2.5(i) is Yu. A. Davydov (1968); (ii) is
P. Billingsley, *Convergence of Probability Measures* (1968), Lemma 1 of §20;
Prop 2.6 is Volkonskii & Rozanov (1959, Lemma 4.3 in Bradley's numbering). The
exponential inequalities are D. Bosq, *Nonparametric Statistics for Stochastic
Processes* (1998), Thms 1.3–1.4. Hoeffding's covariance identity is from Hoeffding
(1940); its use here follows Doukhan (1994) §1.2.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

/-! ### Proposition 2.5(ii): the bounded (Billingsley) covariance inequality

Two-σ-algebra statements follow the Mathlib `condExp` binder convention (ambient `mΩ`
as a plain implicit bound after the sub-σ-algebras, before `μ`) — see
`Mixing/Relations.lean`. -/

section TwoAlgebras

variable {Ω : Type*}

/-- **FY Proposition 2.5(ii) (Billingsley)**: `m₁`/`m₂`-measurable bounded factors have
covariance at most `4 α C₁ C₂`. -/
theorem abs_covariance_le_of_bounded {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    {C₁ C₂ : ℝ}
    -- USER-INPUT: uniform bounds; FY Prop 2.5(ii)
    (hfC : ∀ᵐ ω ∂μ, |f ω| ≤ C₁) (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C₂) :
    |cov[f, g; μ]| ≤ 4 * alphaMixCoeff μ m₁ m₂ * C₁ * C₂ := by
  sorry

/-- **Complex Billingsley** (FY §2.6.2, constant 16): unit-modulus-bounded complex
factors. Stated with the real-bilinear covariance
`E[f·g] − E[f]·E[g]` in `ℂ`. -/
theorem norm_covariance_le_of_bounded_complex {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℂ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    {C₁ C₂ : ℝ}
    -- USER-INPUT: uniform bounds; FY §2.6.2 complex remark
    (hfC : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C₁) (hgC : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ C₂) :
    ‖(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ‖
      ≤ 16 * alphaMixCoeff μ m₁ m₂ * C₁ * C₂ := by
  sorry

/-! ### Proposition 2.5(i): the Davydov covariance inequality -/

/-- **FY Proposition 2.5(i) (Davydov)**: for `p, q > 1` with `1/p + 1/q < 1`,
`|Cov(f, g)| ≤ 8 α^{1 − 1/p − 1/q} ‖f‖_p ‖g‖_q`. Built in full (truncation against the
bounded case; FY cites Doukhan §1.2.2). -/
theorem abs_covariance_le_davydov {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    {p q : ℝ}
    -- USER-INPUT: integrability exponents; FY Prop 2.5(i)
    (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q < 1)
    (hfLp : MemLp f (ENNReal.ofReal p) μ) (hgLq : MemLp g (ENNReal.ofReal q) μ) :
    |cov[f, g; μ]|
      ≤ 8 * alphaMixCoeff μ m₁ m₂ ^ (1 - 1 / p - 1 / q)
        * (eLpNorm f (ENNReal.ofReal p) μ).toReal
        * (eLpNorm g (ENNReal.ofReal q) μ).toReal := by
  sorry

/-! ### Proposition 2.6: the Volkonskii–Rozanov factorization -/

/-- **FY Proposition 2.6 (Volkonskii–Rozanov)**: complex unit-bounded blocks measured
against an increasing family with α-gaps at most `a` factorize up to `16 (k − 1) a`.
The gap hypothesis is abstract: the α-coefficient between the cumulative past
`⨆_{j ≤ l} m j` and the next block `m (l+1)` is at most `a` — process-level
applications supply it via `IsStrictlyStationary.alphaMixCoeff_shift` and
monotonicity. -/
theorem norm_integral_prod_sub_prod_integral_le {k : ℕ}
    {m : Fin k → MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hle : ∀ l, m l ≤ mΩ)
    (ξ : Fin k → Ω → ℂ) (hmeas : ∀ l, Measurable[m l] (ξ l))
    -- USER-INPUT: unit modulus bound; FY Prop 2.6
    (hbdd : ∀ l, ∀ᵐ ω ∂μ, ‖ξ l ω‖ ≤ 1)
    {a : ℝ}
    -- USER-INPUT: α-gap bound between cumulative past and next block; FY Prop 2.6
    (hgap : ∀ l : Fin k, ∀ hl : (l : ℕ) + 1 < k,
      alphaMixCoeff μ (⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ l, m j) (m ⟨(l : ℕ) + 1, hl⟩) ≤ a) :
    ‖(∫ ω, ∏ l, ξ l ω ∂μ) - ∏ l, ∫ ω, ξ l ω ∂μ‖
      ≤ 16 * ((k : ℝ) - 1) * a := by
  sorry

end TwoAlgebras

/-! ### The fourth-moment bound (FY Proposition 2.7(ii) at `q = 4`) -/

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **FY Proposition 2.7(ii), `q = 4` instance** (the one the Bernstein-block CLT
consumes): a bounded zero-mean strictly stationary α-mixing process with
`α(n) ≤ K n⁻²` has `E S_n⁴ ≤ C n²`. -/
theorem moment4_partial_sum_le [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    {C : ℝ}
    -- USER-INPUT: uniform bound; FY Prop 2.7(ii)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    -- USER-INPUT: zero mean; FY Prop 2.7
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {K : ℝ}
    -- USER-INPUT: α-decay of order n⁻²; FY Prop 2.7(ii) with q = 4
    (hα : ∀ n : ℕ, 1 ≤ n → alphaCoeff X μ n ≤ K / (n : ℝ) ^ 2) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ n : ℕ,
      ∫ ω, (∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) ^ 4 ∂μ ≤ C' * (n : ℝ) ^ 2 := by
  sorry

/-! ### Theorems 2.18/2.19: Bosq exponential inequalities (literature DEBTS) -/

/-- **DEBT (Bosq 1998 Thm 1.3; FY Theorem 2.18)**: bounded zero-mean strictly
stationary process; for every `ε > 0` and integer `1 ≤ qb ≤ n/2`,
`P(|S_n/n| > ε) ≤ 4 exp(−ε² qb/(8 b²)) + 22 (1 + 4b/ε)^{1/2} qb α([n/(2 qb)])`.
Used only by ch. 5 KDE uniform rates (outside current scope). -/
theorem bosq_exponential_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    {b : ℝ} (hb : 0 < b)
    -- USER-INPUT: uniform bound; FY Thm 2.18
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ b)
    -- USER-INPUT: zero mean; FY Thm 2.18
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {ε : ℝ} (hε : 0 < ε) {n qb : ℕ} (hq1 : 1 ≤ qb) (hqn : 2 * qb ≤ n) :
    (μ {ω | ε < |(n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω|}).toReal
      ≤ 4 * Real.exp (-(ε ^ 2 * qb) / (8 * b ^ 2))
        + 22 * (1 + 4 * b / ε) ^ ((1 : ℝ) / 2) * qb * alphaCoeff X μ (n / (2 * qb)) := by
  sorry

/-- **DEBT (Bosq 1998 Thm 1.4; FY Theorem 2.19, eq. (2.62))**: under Cramér's condition
`E|X_t|^k ≤ C^{k−2} k! E X_t²` (all `k ≥ 3`), for any `n ≥ 2`, `k ≥ 3`,
`1 ≤ qb ≤ n/2` and `ε > 0`, with `μ(ε) = ε²/(25 E X_t² + 5Cε)`:
`P(|S_n| > nε) ≤ 2(1 + n/qb + μ(ε)) e^{−qb·μ(ε)}
  + 11 n (1 + 5 ε⁻¹ (E|X_t|^k)^{1/(2k+1)}) α([n/(qb+1)])^{2k/(2k+1)}`.
(The book prints `E X_t^k` in the second factor; we state the weaker bound with
`E|X_t|^k ≥ E X_t^k`, which the cited result implies.) -/
theorem bosq_cramer_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    {C : ℝ} (hC : 0 < C)
    -- USER-INPUT: zero mean; FY Thm 2.19
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hL2 : MemLp (X 0) 2 μ)
    -- USER-INPUT: Cramér's condition (2.62); FY Thm 2.19
    (hcram : ∀ k : ℕ, 3 ≤ k →
      ∫ ω, |X 0 ω| ^ k ∂μ ≤ C ^ (k - 2) * (Nat.factorial k : ℝ) * ∫ ω, X 0 ω ^ 2 ∂μ)
    {ε : ℝ} (hε : 0 < ε) {n k qb : ℕ} (hn : 2 ≤ n) (hk : 3 ≤ k)
    (hq1 : 1 ≤ qb) (hqn : 2 * qb ≤ n) :
    (μ {ω | ε < |(n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω|}).toReal
      ≤ 2 * (1 + (n : ℝ) / qb + ε ^ 2 / (25 * ∫ ω, X 0 ω ^ 2 ∂μ + 5 * C * ε))
          * Real.exp (-(qb : ℝ) * (ε ^ 2 / (25 * ∫ ω, X 0 ω ^ 2 ∂μ + 5 * C * ε)))
        + 11 * n * (1 + 5 * ε⁻¹ * (∫ ω, |X 0 ω| ^ k ∂μ) ^ ((1 : ℝ) / (2 * k + 1)))
          * alphaCoeff X μ (n / (qb + 1)) ^ ((2 * k : ℝ) / (2 * k + 1)) := by
  sorry

end Process

end StatLean.TimeSeries
