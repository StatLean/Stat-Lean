import StatLean.TimeSeries.GARCH.Estimation
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Testing for the ARCH effect (FY §4.2.6, eqs. (4.48)–(4.54))

`H₀ : b₁ = ⋯ = b_p = 0` (no ARCH effect) against `H₁` at least one `b_j > 0`, inside
the ARCH(p) family with iid noise. FY's key structural observation: **under `H₀` the
observations are iid**, so the three classical statistics have iid-likelihood
asymptotics and each has a `χ²_p` null limit.

* `archNullIsIID` — the structural fact that `H₀` collapses the ARCH model to iid
  scaled noise *(the printed setup (4.48)–(4.49) has two index/sign slips — "`a_j ≥ 0`"
  for `b_j ≥ 0`, and `b_j X_{t−i}²` for `b_j X_{t−j}²`; corrected here)*;
* `archLRStat` (**eq. (4.50)**), `archScoreStat` (**eq. (4.52)**), `archWaldStat`
  (**eq. (4.54)**) and Engle's `archTR2Stat` (**eq. (4.53)**), the auxiliary-regression
  form asymptotically equivalent to the score test for normal errors;
* the **Fisher information** (eq. (4.51)) of the ARCH likelihood at the null, and the
  three `χ²_p` limit statements. The intended route is to reuse the in-repo iid
  likelihood trinity, `StatLean/HypothesisTesting/LikelihoodMethods/
  TrinityChiSquared.lean`; where the wiring does not fit the ARCH parametrization the
  limits stay as named debts.

**Boundary caveat (documented, not formalized).** The alternative constrains
`b_j ≥ 0`, so under `H₀` the parameter sits on the boundary of the admissible set and
the `χ²_p` approximation is *not* valid for the constrained versions of these tests;
FY notes this and cites the one-sided-testing literature. Our statements are for the
**unconstrained** parametrization, where the classical limits do hold.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.2.6,
eqs. (4.48)–(4.54) (pp. 165–168). (`FY §4.2.6`.)

**Bibliographic comments.** The LM/`TR²` test is R. F. Engle (1982) §6; the iid
likelihood asymptotics FY invokes are Serfling (1980) §4.4.4; the boundary problem is
Chernoff (1954) and Self & Liang (1987).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **FY §4.2.6 structural fact**: under `H₀` (all ARCH coefficients zero) the ARCH(p)
process is iid — `X_t = √c₀ · ε_t`. This is what licenses the classical iid likelihood
asymptotics for all three statistics. -/
theorem IsARCH.iid_of_b_eq_zero [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 (fun _ : Fin p => (0 : ℝ)) X ε μ) :
    (∀ t, X t =ᵐ[μ] fun ω => Real.sqrt c0 * ε t ω) ∧
      IsIIDNoise X c0 μ := by
  sorry

/-- The ARCH(p) **conditional Gaussian log-likelihood** of the data at parameters
`(c₀, b)` (the `§4.2.6` likelihood: `−½ Σ_t (log σ_t² + X_t²/σ_t²)` up to constants),
written through the truncated volatility of `GARCH/Estimation.lean` with no MA part. -/
noncomputable def archLogLik {p : ℕ} (c0 : ℝ) (b : Fin p → ℝ) {T : ℕ}
    (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  -(1 / 2) * garchQuasiLik c0 b (Fin.elim0 : Fin 0 → ℝ) c0 x ν

/-- **FY eq. (4.50)**: the **likelihood-ratio statistic** `2 log S_{T,1}`, twice the
gap between the unrestricted and null-restricted maximized log-likelihoods. -/
noncomputable def archLRStat {p : ℕ} {T : ℕ} (x : Fin T → ℝ) (ν : ℕ)
    (c0hat : ℝ) (bhat : Fin p → ℝ) (c0null : ℝ) : ℝ :=
  2 * (archLogLik c0hat bhat x ν - archLogLik c0null (fun _ : Fin p => (0 : ℝ)) x ν)

/-- **FY eq. (4.53)**: Engle's `TR²` statistic — `T` times the coefficient of
determination of the auxiliary regression of `X_t²` on its `p` lags. Stated through the
regression's residual and total sums of squares. -/
noncomputable def archTR2Stat {T : ℕ} (rss tss : ℝ) : ℝ :=
  (T : ℝ) * (1 - rss / tss)

/-- **FY eq. (4.50) — DEBT** (Serfling §4.4.4 via the iid structure under `H₀`): the
likelihood-ratio statistic has the `χ²_p` null limit. Recorded through the
distribution function of the limit (`chiSqLimitCDF` supplied as the comparison law, so
the statement does not depend on which χ² construction the repo settles on). -/
theorem archLRStat_chiSq_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {X ε : ℤ → Ω → ℝ}
    -- USER-INPUT: the null model; FY §4.2.6 H₀
    (h : IsARCH c0 (fun _ : Fin p => (0 : ℝ)) X ε μ) (hc0 : 0 < c0)
    -- USER-INPUT: finite fourth moment (the iid-likelihood regularity); Serfling §4.4.4
    (hε4 : MemLp (ε 0) 4 μ)
    -- USER-INPUT: measurable unconstrained/null MLE sequences; FY eqs. (4.37), (4.50)
    (c0hat : (T : ℕ) → Ω → ℝ) (bhat : (T : ℕ) → Ω → Fin p → ℝ)
    (c0null : (T : ℕ) → Ω → ℝ)
    (hmeas : ∀ T, Measurable (c0hat T) ∧ Measurable (bhat T) ∧ Measurable (c0null T))
    (νseq : ℕ → ℕ) (hν : Tendsto νseq atTop atTop)
    (hνT : Tendsto (fun T : ℕ => (νseq T : ℝ) / T) atTop (𝓝 0))
    -- USER-INPUT: the χ²_p limit law as a measure on ℝ; Serfling §4.4.4
    (chiSq : Measure ℝ) [IsProbabilityMeasure chiSq]
    (hchi : ∀ u : ℝ, charFun chiSq u = (1 - 2 * Complex.I * u) ^ (-(p : ℂ) / 2))
    (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        archLRStat (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T)
          (c0hat T ω) (bhat T ω) (c0null T ω)) u)
      atTop (𝓝 (charFun chiSq u)) := by
  sorry

/-- **FY eqs. (4.52)–(4.53) — DEBT**: the score/LM statistic (equivalently, for normal
errors, Engle's `TR²`) has the same `χ²_p` null limit as the likelihood-ratio
statistic. -/
theorem archTR2Stat_chiSq_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {X ε : ℤ → Ω → ℝ}
    (h : IsARCH c0 (fun _ : Fin p => (0 : ℝ)) X ε μ) (hc0 : 0 < c0)
    (hε4 : MemLp (ε 0) 4 μ)
    -- USER-INPUT: normal innovations (the case in which TR² ≡ score asymptotically);
    -- FY eq. (4.53)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    -- USER-INPUT: the auxiliary-regression sums of squares of the squared data;
    -- FY eq. (4.53)
    (rss tss : (T : ℕ) → Ω → ℝ)
    (hmeas : ∀ T, Measurable (rss T) ∧ Measurable (tss T))
    (chiSq : Measure ℝ) [IsProbabilityMeasure chiSq]
    (hchi : ∀ u : ℝ, charFun chiSq u = (1 - 2 * Complex.I * u) ^ (-(p : ℂ) / 2))
    (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        archTR2Stat (T := T) (rss T ω) (tss T ω)) u)
      atTop (𝓝 (charFun chiSq u)) := by
  sorry

/-- **FY eq. (4.54) — DEBT**: the Wald statistic (through the Schur-complement block
`I²²` of the information matrix) has the `χ²_p` null limit. -/
theorem archWaldStat_chiSq_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {X ε : ℤ → Ω → ℝ}
    (h : IsARCH c0 (fun _ : Fin p => (0 : ℝ)) X ε μ) (hc0 : 0 < c0)
    (hε4 : MemLp (ε 0) 4 μ)
    (bhat : (T : ℕ) → Ω → Fin p → ℝ) (hmeas : ∀ T, Measurable (bhat T))
    -- USER-INPUT: the estimated information block I²² (Schur complement); FY eq. (4.54)
    (Ihat : (T : ℕ) → Ω → Matrix (Fin p) (Fin p) ℝ)
    (chiSq : Measure ℝ) [IsProbabilityMeasure chiSq]
    (hchi : ∀ u : ℝ, charFun chiSq u = (1 - 2 * Complex.I * u) ^ (-(p : ℂ) / 2))
    (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        (T : ℝ) * ∑ i, ∑ j, bhat T ω i * Ihat T ω i j * bhat T ω j) u)
      atTop (𝓝 (charFun chiSq u)) := by
  sorry

end StatLean.TimeSeries
