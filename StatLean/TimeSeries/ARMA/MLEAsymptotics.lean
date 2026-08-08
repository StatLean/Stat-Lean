import StatLean.TimeSeries.ARMA.Consistency
import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.BrownCLT
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Hannan's theorem: asymptotic normality of the ARMA Gaussian MLE (FY Theorem 3.2)

The head of the commissioned Hannan program (ledger (a), batches C–D): for a
stationary causal invertible ARMA(p, q) with **iid** noise and coprime minimal orders,
any measurable approximate-MLE sequence over a compact identifiable region satisfies

`√T (θ̂_T − θ₀) →d N(0, W)`, `W = (hannanVarZ b₀ a₀)⁻¹` (FY eq. (3.14)),

stated in Cramér–Wold/charFun form, together with `σ̂² →p σ²`. FY's remarks are
honored: **no fourth moment is required**, and the noise assumption is exactly iid
(the martingale-difference weakening is future work, not stated).

Also here:
* **FY Proposition 3.1** (PACF asymptotics; misprint corrected — the scaling is `√T`,
  not `T^{−1/2}`): for a causal AR(p) with iid noise and `k > p`, the sample PACF
  `π̂(k)` (Yule–Walker form on the sample ACVF) satisfies `√T π̂(k) →d N(0, 1)`;
* literature DEBTS: the asymptotic equivalence LS = YW = MLE (B&D Thm 10.8.2) and the
  reciprocal-variance identity `(Γ_k⁻¹)_{kk} = σ⁻²` for `k > p` (FY "can be proved" —
  attempted in the lane, demotable).

**Assembly plan** (lane prompt carries detail): consistency (`mle_consistent`) +
score MDS (`armaScore_condexp_zero` + Brown `mds_clt_sequence`) + Hessian/information
LLN + the standard Taylor/sandwich argument on the profiled criterion.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.3.2,
Theorem 3.2, eq. (3.14), Prop 3.1 (pp. 96–99); E. J. Hannan, J. Appl. Probab. 10
(1973) 130–145; Brockwell & Davis (1991) §8.7–§10.8. (`FY §3.3 Thm 3.2 / Hannan
1973`.)
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **FY Theorem 3.2 (Hannan), Cramér–Wold/charFun form**: under the `mle_consistent`
setting, every linear combination of `√T (θ̂_T − θ₀)` is asymptotically
`N(0, cᵀ W c)` with `W = (hannanVarZ b₀ a₀)⁻¹`. -/
theorem hannan_mle_clt [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ)
    -- USER-INPUT: iid innovations; FY Thm 3.2 (no 4th moment required)
    (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    -- USER-INPUT: (b₀, a₀) ∈ 𝓑; FY eq. (3.11)
    (hB0 : ARMAInvertibleParams b0 a0)
    -- USER-INPUT: coprime minimal orders; Hannan 1973 (FY implicit)
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))}
    -- USER-INPUT: compact identifiable search region with θ₀ interior; Hannan §2
    (hK : IsCompact K) (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2)
    (hK0 : (b0, a0) ∈ interior K)
    (θ : (T : ℕ) → Ω → (Fin p → ℝ) × (Fin q → ℝ))
    (hθmeas : ∀ T, Measurable (θ T))
    {δT : ℕ → ℝ} (hδT0 : ∀ T, 0 ≤ δT T)
    -- USER-INPUT: approximate minimization at rate o(1/T) (exact minimizers
    -- qualify); FY eq. (3.10) argmax corrected
    (hδTfast : Tendsto (fun T : ℕ => (T : ℝ) * δT T) atTop (𝓝 0))
    (hargmin : ∀ (T : ℕ) (ω : Ω), θ T ω ∈ K ∧ ∀ ba ∈ K,
      armaProfileCriterion (θ T ω).1 (θ T ω).2
          (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
        ≤ armaProfileCriterion ba.1 ba.2
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) + δT T)
    (c : Fin p ⊕ Fin q → ℝ) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T *
          ((∑ i : Fin p, c (.inl i) * ((θ T ω).1 i - b0 i)) +
            ∑ j : Fin q, c (.inr j) * ((θ T ω).2 j - a0 j))) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (c ⬝ᵥ ((hannanVarZ b0 a0)⁻¹ *ᵥ c)))) u)) := by
  sorry

/-- **FY Theorem 3.2, variance part**: the profiled variance estimator is consistent,
`σ̂²_T = S(θ̂_T)/T →p σ²`. -/
theorem hannan_sigma2_consistent [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))}
    (hK : IsCompact K) (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2)
    (hK0 : (b0, a0) ∈ interior K)
    (θ : (T : ℕ) → Ω → (Fin p → ℝ) × (Fin q → ℝ)) (hθmeas : ∀ T, Measurable (θ T))
    {δT : ℕ → ℝ} (hδT0 : ∀ T, 0 ≤ δT T)
    (hδTfast : Tendsto (fun T : ℕ => (T : ℝ) * δT T) atTop (𝓝 0))
    (hargmin : ∀ (T : ℕ) (ω : Ω), θ T ω ∈ K ∧ ∀ ba ∈ K,
      armaProfileCriterion (θ T ω).1 (θ T ω).2
          (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
        ≤ armaProfileCriterion ba.1 ba.2
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) + δT T)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ => (μ {ω | δ ≤
        |armaProfileS (θ T ω).1 (θ T ω).2
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2|}).toReal)
      atTop (𝓝 0) := by
  sorry

/-- The **sample PACF** at order `k` (Yule–Walker form on the sample ACVF): the last
coordinate of the solution of the sample Yule–Walker system (junk `0` at `k = 0` or
when the sample Toeplitz matrix is singular, by the matrix-inverse convention). -/
noncomputable def samplePACF {T : ℕ} (x : Fin T → ℝ) (k : ℕ) : ℝ :=
  if hk : 0 < k then
    (((Matrix.of fun i j : Fin k =>
          sampleACVF x ((i : ℤ) - (j : ℤ)).natAbs)⁻¹)
        *ᵥ fun i : Fin k => sampleACVF x ((i : ℕ) + 1)) ⟨k - 1, by omega⟩
  else 0

/-- **FY Proposition 3.1** (misprint corrected: `√T`, not `T^{−1/2}`): for a causal
AR(p) with iid noise and lag `k > p`, the sample PACF is asymptotically standard
normal: `√T π̂(k) →d N(0, 1)`. -/
theorem samplePACF_clt [IsProbabilityMeasure μ] {p : ℕ}
    {b0 : Fin p → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsAR b0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hroot : NoRootClosedDisc b0)
    (hcausal :
      IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {k : ℕ} (hk : p < k) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * samplePACF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) k) u)
      atTop (𝓝 (charFun (gaussianReal 0 1) u)) := by
  sorry

/-- **DEBT (B&D Thm 10.8.2; FY §3.3.2 remark)**: least-squares, Yule–Walker, and
Gaussian-MLE estimator sequences of a causal AR(p) are asymptotically equivalent
(`√T`-differences vanish in probability). Statement recorded at the coarse level FY
cites. -/
theorem ls_yw_mle_equivalent_debt [IsProbabilityMeasure μ] {p : ℕ}
    {b0 : Fin p → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsAR b0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hroot : NoRootClosedDisc b0)
    (hcausal : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: the Yule–Walker estimator (sample-YW solution) and any
    -- MLE sequence as in `hannan_mle_clt`; B&D Thm 10.8.2
    (bYW : (T : ℕ) → Ω → Fin p → ℝ)
    (hYW : ∀ (T : ℕ) (ω : Ω) (i : Fin p),
      bYW T ω i = (((Matrix.of fun i' j : Fin p =>
          sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
            ((i' : ℤ) - (j : ℤ)).natAbs)⁻¹) *ᵥ
        fun i' : Fin p => sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          ((i' : ℕ) + 1)) i)
    (bMLE : (T : ℕ) → Ω → Fin p → ℝ) (hMLEmeas : ∀ T, Measurable (bMLE T))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ => (μ {ω | δ ≤
        Real.sqrt T * dist (bYW T ω) (bMLE T ω)}).toReal) atTop (𝓝 0) := by
  sorry

end StatLean.TimeSeries
