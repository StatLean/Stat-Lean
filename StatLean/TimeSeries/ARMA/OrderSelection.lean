import StatLean.TimeSeries.ARMA.Likelihood
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Order determination: KL information and the AIC family (FY §3.4)

* **Kullback–Leibler information** of a candidate density `g` against the truth `f`
  (FY eq. (3.15)) and its **nonnegativity** — the in-text Jensen proof (a clean
  self-contained target);
* the **AIC** (3.17)/(3.18), **AICC** (3.19), **FPE**, and **BIC** (3.23)/(3.24)
  criteria for ARMA order selection, defined on the profiled likelihood criterion of
  `ARMA/Likelihood.lean` with FY's penalties;
* the **Taylor equivalence** `AICC = AIC + O(1/T)`-form (in-text; the FPE display
  absorbs an additive constant, harmless for argmin);
* literature DEBTS: the Akaike bias approximation `≈ p_m/T` (Akaike 1973) and BIC
  consistency (Hannan 1980) — the book cites both without proof.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.4,
eqs. (3.15)–(3.24) (pp. 99–109). (`FY §3.4`.)

**Bibliographic comments.** KL information: Kullback & Leibler (1951). AIC: Akaike
(1973, 2nd Int. Symp. Information Theory); AICC: Hurvich & Tsai (1989); FPE: Akaike
(1969); BIC: Schwarz (1978) and Akaike (1977); BIC consistency for ARMA orders:
Hannan (1980, Ann. Statist.).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

/-- **Kullback–Leibler information** (FY eq. (3.15)) of a candidate density `g`
relative to the true density `f`, both w.r.t. Lebesgue on ℝ^d modeled as a σ-finite
measure `ν`: `KL(f, g) = ∫ f log(f/g) dν` (junk under non-integrability, by the
integral convention). -/
noncomputable def klInfo {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (f g : α → ℝ) : ℝ :=
  ∫ v, f v * Real.log (f v / g v) ∂ν

/-- **FY §3.4.1 (Jensen)**: the KL information is nonnegative for probability
densities: if `f, g ≥ 0` integrate to `1` against `ν` and `g > 0` on `{f > 0}`, then
`KL(f, g) ≥ 0`. In-text proof: `−log` is convex, Jensen against the probability
measure `f dν`. -/
theorem klInfo_nonneg {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [SigmaFinite ν] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ v, 0 ≤ f v) (hg0 : ∀ v, 0 ≤ g v)
    -- USER-INPUT: probability densities; FY §3.4.1
    (hf1 : ∫ v, f v ∂ν = 1) (hg1 : ∫ v, g v ∂ν = 1)
    -- USER-INPUT: absolute continuity on the support; FY §3.4.1 (implicit)
    (hsupp : ∀ v, 0 < f v → 0 < g v)
    -- LEAN-ONLY: integrability of the KL integrand (finite KL); junk otherwise
    (hint : Integrable (fun v => f v * Real.log (f v / g v)) ν) :
    0 ≤ klInfo ν f g := by
  sorry

/-- **AIC** (FY eq. (3.18), profiled form): `T·ℓ*(b, a) + 2(p + q)` — stated as a
definition on the profiled criterion; the `argmin` semantics live with the
estimator hypotheses of the consumers. -/
noncomputable def armaAIC {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) {T : ℕ}
    (x : Fin T → ℝ) : ℝ :=
  (T : ℝ) * armaProfileCriterion b a x + 2 * ((p : ℝ) + (q : ℝ))

/-- **AICC** (FY eq. (3.19), Hurvich–Tsai small-sample correction):
`T·ℓ* + 2(p+q)T/(T − p − q − 1)`. -/
noncomputable def armaAICC {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) {T : ℕ}
    (x : Fin T → ℝ) : ℝ :=
  (T : ℝ) * armaProfileCriterion b a x
    + 2 * ((p : ℝ) + (q : ℝ)) * (T : ℝ) / ((T : ℝ) - (p : ℝ) - (q : ℝ) - 1)

/-- **BIC** (FY eq. (3.23)): `T·ℓ* + (p + q)·log T`. -/
noncomputable def armaBIC {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) {T : ℕ}
    (x : Fin T → ℝ) : ℝ :=
  (T : ℝ) * armaProfileCriterion b a x + ((p : ℝ) + (q : ℝ)) * Real.log T

/-- **Taylor equivalence** (FY §3.4.3, in-text): the AICC and AIC penalties differ by
`O(1/T)` uniformly over bounded orders: for `p + q ≤ m` and `T ≥ 2(m + 1)`,
`|armaAICC − armaAIC| ≤ 2(m + 1)²·2/T`-shaped bound. Stated with the explicit
constant `4(m+1)²/T`. -/
theorem armaAICC_sub_armaAIC_le {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (x : Fin T → ℝ) {m : ℕ}
    (hm : p + q ≤ m) (hT : 2 * (m + 1) ≤ T) :
    |armaAICC b a x - armaAIC b a x| ≤ 4 * ((m : ℝ) + 1) ^ 2 / T := by
  sorry

/-- The order-level BIC **value function**: the infimum of `armaBIC` over parameters
in the constraint set at fixed orders `(p, q)` (junk by the `iInf` convention when
unbounded below). -/
noncomputable def armaBICmin (p q : ℕ) {T : ℕ} (x : Fin T → ℝ) : ℝ :=
  ⨅ ba : {ba : (Fin p → ℝ) × (Fin q → ℝ) // ARMAInvertibleParams ba.1 ba.2},
    armaBIC ba.val.1 ba.val.2 x

/-- **DEBT (Hannan 1980; FY §3.4.3)**: BIC order-selection consistency. If the data
are a stationary causal invertible ARMA(p₀, q₀) with iid noise, any measurable
selection minimizing the BIC value function over a fixed grid containing `(p₀, q₀)`
picks the true orders with probability tending to one. -/
theorem bic_consistency_debt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {p0 q0 : ℕ} {b0 : Fin p0 → ℝ} {a0 : Fin q0 → ℝ}
    {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB : ARMAInvertibleParams b0 a0)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {P Q : ℕ} (hp : p0 ≤ P) (hq : q0 ≤ Q)
    -- USER-INPUT: a measurable BIC-minimizing order selection over the grid; FY §3.4.3
    (psel qsel : ℕ → Ω → ℕ)
    (hmeassel : ∀ T, Measurable (psel T) ∧ Measurable (qsel T))
    (hminsel : ∀ (T : ℕ) (ω : Ω), psel T ω ≤ P ∧ qsel T ω ≤ Q ∧
      ∀ p ≤ P, ∀ q ≤ Q,
        armaBICmin (psel T ω) (qsel T ω) (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          ≤ armaBICmin p q (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)) :
    Tendsto (fun T : ℕ =>
        (μ {ω | psel T ω = p0 ∧ qsel T ω = q0}).toReal) atTop (𝓝 1) := by
  sorry

end StatLean.TimeSeries
