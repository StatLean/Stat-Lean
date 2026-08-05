import StatLean.TimeSeries.Mixing.Inequalities
import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT

/-!
# Limit theorems for α-mixing processes (FY §2.6.3, pp. 74–76)

* **Theorem 2.20(ii)** (in-text proof): bounded zero-mean strictly stationary with
  `Σ α(j) < ∞` ⇒ the ACVF is absolutely summable and
  `n⁻¹ Var(S_n) → γ(0) + 2 Σ_{j≥1} γ(j)` (eq. (2.63)). **Erratum**: the book's display
  bounds `|γ(j)| ≤ 4α(j){E|X_1|}²`; the correct Billingsley bound is `4α(j)C²` — we
  state and use the corrected form.
* **Theorem 2.21(ii)** (FULL in-text proof, pp. 75–76): additionally `σ² > 0` ⇒
  `S_n/√n →d N(0, σ²)`, `σ² = γ(0) + 2Σγ(j)` — the Bernstein-block scheme: big blocks
  of length `l_n`, small blocks `s_n` (`s_n → ∞`, `s_n/l_n → 0`, `l_n/n → 0`);
  small-block negligibility via the fourth-moment bound; characteristic-function
  factorization via Volkonskii–Rozanov (`16(k_n − 1)α(s_n) → 0`, using
  `α(n) = o(1/n)` from monotone + summable); big-block array CLT via the Lindeberg
  double-array theorem.
* **Theorem 2.20(i)/2.21(i)** — the `δ`-moment versions (cited Bosq / Peligrad):
  literature DEBTS.
* **Proposition 2.8 (SLLN)** — α-mixing + `E|X| < ∞` ⇒ `S_n/n → EX` a.s.: literature
  DEBT (the cited route is "α-mixing ⇒ ergodic" + Birkhoff; Mathlib has no pointwise
  ergodic theorem in the pin).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.3,
Prop 2.8, Thms 2.20–2.21, eq. (2.63) (pp. 74–76). (`FY §2.6.3`.)

**Proof formalization notes.**
* Summability statements are spelled inline (`Summable fun k : ℤ => |acvf X μ k|`)
  rather than through `Spectral/SpectralDensity.HasSummableACVF` — this concept-layer
  file must not import the spectral assembly.
* `σ²` is packaged as `acvf X μ 0 + 2 * Σ'_{j : ℕ} acvf X μ (j + 1)`.
* The α-coefficient of the blocks is controlled through
  `IsStrictlyStationary.alphaMixCoeff_shift` (Relations) + `alphaMixCoeff_mono`.

**Bibliographic comments.** The Bernstein small-block/large-block method is
S. N. Bernstein (1927); Theorem 2.21's proof follows Ibragimov–Linnik (1971) Thm 18.4.1
as streamlined by FY. The δ-moment CLT (i) is M. Peligrad (*Invariance principles for
mixing sequences*, Ann. Probab. 1982-adjacent); Thm 2.20(i) is Bosq (1998) §1.5. The
SLLN via ergodicity is Doob (1953) ch. X / Ibragimov–Linnik (1971) ch. 17.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **FY Theorem 2.20(ii)** (in-text; erratum `4α(j)C²` applied): bounded zero-mean
strictly stationary + summable α ⇒ summable ACVF and the variance-rate identity
(2.63). -/
theorem summable_acvf_and_var_rate_of_bounded [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {C : ℝ}
    -- USER-INPUT: uniform bound; FY Thm 2.20(ii)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    -- USER-INPUT: zero mean; FY §2.6.3 setup
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    -- USER-INPUT: summable mixing coefficients; FY Thm 2.20(ii)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n) :
    (Summable fun k : ℤ => |acvf X μ k|) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
          variance (fun ω => ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ) atTop
        (𝓝 (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))) := by
  sorry

/-- **FY Theorem 2.21(ii)** (full in-text proof, Bernstein blocks): bounded zero-mean
strictly stationary, summable α, positive long-run variance ⇒ `S_n/√n →d N(0, σ²)`
(charFun form). -/
theorem clt_of_bounded_alphaMixing [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {C : ℝ}
    -- USER-INPUT: uniform bound; FY Thm 2.21(ii)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    -- USER-INPUT: zero mean; FY §2.6.3 setup
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    -- USER-INPUT: summable mixing coefficients; FY Thm 2.21(ii)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n)
    -- USER-INPUT: positive long-run variance; FY Thm 2.21
    (hσ : 0 < acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))
    (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) u) atTop
      (𝓝 (charFun (gaussianReal 0
        (Real.toNNReal (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1)))) u)) := by
  sorry

/-- **DEBT (Bosq 1998 §1.5; FY Theorem 2.20(i))**: the `δ`-moment version of the
variance rate: `E|X|^δ < ∞` (δ > 2) and `Σ_j α(j)^{1−2/δ} < ∞` suffice. -/
theorem summable_acvf_and_var_rate_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {δ : ℝ}
    -- USER-INPUT: δ-moment; FY Thm 2.20(i)
    (hδ : 2 < δ) (hLδ : MemLp (X 0) (ENNReal.ofReal δ) μ)
    -- USER-INPUT: zero mean; FY §2.6.3 setup
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    -- USER-INPUT: Σ α^{1−2/δ} < ∞; FY Thm 2.20(i)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n ^ (1 - 2 / δ)) :
    (Summable fun k : ℤ => |acvf X μ k|) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
          variance (fun ω => ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ) atTop
        (𝓝 (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))) := by
  sorry

/-- **DEBT (Peligrad; FY Theorem 2.21(i))**: the `δ`-moment CLT under the Thm 2.20(i)
hypotheses and positive long-run variance. -/
theorem clt_of_alphaMixing_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {δ : ℝ} (hδ : 2 < δ) (hLδ : MemLp (X 0) (ENNReal.ofReal δ) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n ^ (1 - 2 / δ))
    (hσ : 0 < acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))
    (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) u) atTop
      (𝓝 (charFun (gaussianReal 0
        (Real.toNNReal (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1)))) u)) := by
  sorry

/-- **DEBT (Doob 1953 / Ibragimov–Linnik 1971; FY Proposition 2.8)**: the strong law
for α-mixing strictly stationary sequences with a first moment. The cited route is
"α-mixing ⇒ ergodicity" + the Birkhoff pointwise ergodic theorem, which the Mathlib
pin does not provide. -/
theorem slln_of_alphaMixing_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    (hL1 : Integrable (X 0) μ)
    -- USER-INPUT: α-mixing; FY Prop 2.8
    (hmix : IsAlphaMixing X μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
        (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) atTop
      (𝓝 (∫ ω', X 0 ω' ∂μ)) := by
  sorry

end StatLean.TimeSeries
