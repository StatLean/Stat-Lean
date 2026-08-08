import StatLean.TimeSeries.ARMA.Likelihood
import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.Defs

/-!
# Score analysis for ARMA maximum likelihood (FY §3.3.2, eq. (3.14); Hannan program)

The analytic layer of the commissioned Hannan Theorem 3.2 proof (time-domain route,
`notes/time_series/roadmap.md`): residual inversion, the auxiliary AR processes, the
information matrix, and the martingale-difference property of the quasi-score.

* `armaPi` — the **AR(∞) inversion coefficients** `π(z) = b(z)/a(z)` (invertibility
  makes them geometrically decaying: `summable_abs_armaPi`);
* `maCrossACVF` — cross-covariances of two MA(∞) filters driven by a common unit
  white noise;
* `hannanVarZ` — **FY eq. (3.14)**: the covariance matrix of
  `Z_t = (U_{t−1}, …, U_{t−p}, V_{t−1}, …, V_{t−q})`, where `U` is the AR(p) process
  `b(B)U = ε` and `V` the AR(q) process `a(B)V = ε` driven by a **common** `WN(0,1)`;
  the asymptotic covariance of the MLE is `W = (hannanVarZ)⁻¹`;
* `hannanVarZ_posDef` — positive-definiteness **under coprimality** of the AR and MA
  polynomials (the ARMA(1,1) degeneracy at `a + b = 0` noted by FY shows coprimality
  is genuinely needed; FY's `(b₀, a₀) ∈ 𝓑` implicitly assumes minimal orders);
* `armaResidual` — the θ-residual process `ε_t(θ) = Σ_j π_j(θ) X_{t−j}` as an `L²`
  limit, recovering the innovations at the true parameter
  (`armaResidual_eq_noise`);
* the **score-as-MDS** structure: at the true parameter the derivative array of the
  residual sum of squares is a stationary martingale-difference sequence against the
  noise filtration (`armaScore_condexp_zero`) with conditional variance proportional
  to `hannanVarZ` in the limit — the inputs Brown's CLT needs
  (`ARMA/MLEAsymptotics.lean` assembles).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.3.2,
eq. (3.14) and Theorem 3.2 remarks (pp. 96–99); proof route from E. J. Hannan, *The
asymptotic theory of linear time-series models*, J. Appl. Probab. **10** (1973),
130–145, as streamlined in Brockwell & Davis (1991) §10.8. (`FY §3.3.2 / Hannan 1973`.)

**Bibliographic comments.** The auxiliary-AR representation of the ARMA information
matrix is due to Whittle (1953) and Walker (1962); Hannan (1973) gave the ergodic
proof; the martingale-difference score route is Hall–Heyde (1980) §6.2 and Yao &
Brockwell (2001, personal-communication route cited by FY).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

/-- The **AR(∞) inversion coefficients** `π_n = [zⁿ] b(z)/a(z)` (FY §3.3.1's
invertibility expansion; junk-total via the formal power-series inverse, well-defined
since `a(0) = 1`). -/
noncomputable def armaPi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) : ℝ :=
  PowerSeries.coeff n
    (((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
      (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)

/-- Geometric decay of the inversion coefficients on the constraint set. -/
theorem summable_abs_armaPi {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) :
    Summable fun n : ℕ => |armaPi b a n| := by
  sorry

/-- **Cross-ACVF of two one-sided filters over a common unit white noise**:
`E[(Σᵢ ψᵢ ε_{s−i})(Σⱼ φⱼ ε_{t−j})]` at lag `k = t − s` is `Σⱼ ψⱼ φ_{j+k}` (terms with
negative index vanish). -/
noncomputable def maCrossACVF (ψ φ : ℕ → ℝ) (k : ℤ) : ℝ :=
  ∑' j : ℕ, ψ j * (if h : 0 ≤ (j : ℤ) + k then φ ((j : ℤ) + k).toNat else 0)

/-- **FY eq. (3.14)**: the covariance matrix of the auxiliary vector
`Z = (U_{t−1..t−p}, V_{t−1..t−q})`, `b(B)U = ε`, `a(B)V = ε`, common `WN(0,1)`.
Block entries through `armaPsi`/`maCrossACVF`: `ψᵇ = armaPsi b elim0` are the
coefficients of `1/b`, `ψᵃ = armaPsi (fun j => −a j) elim0` those of `1/a`. -/
noncomputable def hannanVarZ {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  Matrix.of fun s t =>
    match s, t with
    | .inl i, .inl i' =>
        maCrossACVF (armaPsi b (Fin.elim0 : Fin 0 → ℝ))
          (armaPsi b (Fin.elim0 : Fin 0 → ℝ)) ((i' : ℤ) - (i : ℤ))
    | .inl i, .inr j =>
        maCrossACVF (armaPsi b (Fin.elim0 : Fin 0 → ℝ))
          (armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ)) ((j : ℤ) - (i : ℤ))
    | .inr j, .inl i =>
        maCrossACVF (armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ))
          (armaPsi b (Fin.elim0 : Fin 0 → ℝ)) ((i : ℤ) - (j : ℤ))
    | .inr j, .inr j' =>
        maCrossACVF (armaPsi (fun j'' => -a j'') (Fin.elim0 : Fin 0 → ℝ))
          (armaPsi (fun j'' => -a j'') (Fin.elim0 : Fin 0 → ℝ)) ((j' : ℤ) - (j : ℤ))

/-- **Positive-definiteness of the information matrix** under coprimality of the lag
polynomials (FY's implicit minimal-orders assumption; the ARMA(1,1) `a + b = 0`
degeneracy shows it is necessary). -/
theorem hannanVarZ_posDef {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a)
    -- USER-INPUT: coprime lag polynomials (minimal orders); FY §3.3.2 implicit,
    -- explicit in Hannan 1973
    (hcop : IsCoprime (arPoly b) (maPoly a)) :
    (hannanVarZ b a).PosDef := by
  sorry

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **θ-residual process** in the `L²` sense: `ε_t(θ)` is the `L²` limit of
`Σ_{j<N} π_j(θ) X_{t−j}` (the AR(∞) inversion applied to the data). -/
def IsARMAResidualOf {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (r X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℤ, Tendsto
    (fun N : ℕ => eLpNorm
      (fun ω => r t ω - ∑ j ∈ Finset.range N, armaPi b a j * X (t - (j : ℕ)) ω) 2 μ)
    atTop (𝓝 0)

/-- Existence of the residual process on the constraint set (geometric `π`-decay +
stationarity, mirroring `exists_isFilteredBy`). -/
theorem exists_isARMAResidualOf [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X : ℤ → Ω → ℝ}
    (hB : ARMAInvertibleParams b a) (hstat : IsStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) :
    ∃ r : ℤ → Ω → ℝ, (∀ t, Measurable (r t)) ∧ IsARMAResidualOf b a r X μ := by
  sorry

/-- **Residuals at the truth recover the innovations**: for a stationary causal
invertible ARMA at its true parameters, `ε_t(θ₀) = ε_t` a.e. -/
theorem isARMAResidualOf_eq_noise [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε r : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hB : ARMAInvertibleParams b a)
    (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    (hr : IsARMAResidualOf b a r X μ) (hrmeas : ∀ t, Measurable (r t)) (t : ℤ) :
    r t =ᵐ[μ] ε t := by
  sorry

/-- **The score is a martingale-difference sequence at the truth** (the Brown-CLT
input of the Hannan program): with `U/V` the auxiliary filtered processes of the data
(`U_t = Σ ψᵇ_j ε_{t−j}` etc. realized through the residual machinery), the score
coordinates `s_t = ε_t · Z_{t}` satisfy `E[s_t | σ(ε_s, s < t)] = 0`. Stated for the
generic coordinate combination `c`: the combined score is an MDS against the noise
past. -/
theorem armaScore_condexp_zero [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε U V : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ)
    (hB : ARMAInvertibleParams b a)
    (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: the auxiliary AR processes driven by the innovations; FY §3.3.2
    (hU : IsLinearProcessOf (armaPsi b (Fin.elim0 : Fin 0 → ℝ)) U ε μ)
    (hV : IsLinearProcessOf (armaPsi (fun j => -a j) (Fin.elim0 : Fin 0 → ℝ)) V ε μ)
    (hUmeas : ∀ t, Measurable (U t)) (hVmeas : ∀ t, Measurable (V t))
    (c : Fin p ⊕ Fin q → ℝ) (t : ℤ) :
    μ[fun ω => ε t ω *
        ((∑ i : Fin p, c (.inl i) * U (t - 1 - (i : ℕ)) ω) +
          ∑ j : Fin q, c (.inr j) * V (t - 1 - (j : ℕ)) ω)
      | sigmaLT ε t] =ᵐ[μ] 0 := by
  sorry

end Process

end StatLean.TimeSeries
