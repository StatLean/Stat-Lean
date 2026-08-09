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

## The three `χ²_p` debts: why the in-repo trinity does not discharge them

`IsARCH.iid_of_b_eq_zero` is proved, so the structural input FY relies on is available.
The intended follow-up — instantiating `logLR_tendsto_chiSquared_affine` (and its score /
Wald companions) of `HypothesisTesting/LikelihoodMethods/TrinityChiSquared.lean` at the
null `b = 0` — was examined and **rejected**. Two independent reasons, in order of
severity.

**(1) The three frozen statements are false as they stand, for every `p ≥ 1`, so no
proof of them exists.** None of them constrains its estimator arguments to the data:
`archLRStat_chiSq_debt` takes `c0hat`, `bhat`, `c0null` merely measurable,
`archTR2Stat_chiSq_debt` takes `rss`, `tss` merely measurable, and
`archWaldStat_chiSq_debt` takes `bhat` measurable and `Ihat` entirely free. Choosing the
constants `c0hat = c0null = c0`, `bhat = 0` (resp. `rss = tss = 1`, resp. `bhat = 0`)
makes each statistic *identically zero*, so its law is `δ₀`, whose characteristic
function is the constant `1`; the conclusion then forces `charFun chiSq u = 1` for
every `u`, while `hchi` at `u = 1/2` gives `‖(1 − i)^{−p/2}‖ = 2^{−p/4} < 1`. (Both
halves of this contradiction were machine-checked.) The repair is not a proof but a
*statement* amendment, which is out of scope here: each debt needs the missing
`USER-INPUT` hypothesis that its estimator sequence is the actual (quasi-)MLE — or,
in the trinity's currency, is asymptotically linear with the ARCH score and information.

**(2) Even after that repair the trinity's shape does not fit.** Ranked by how hard
each mismatch is to bridge:

* *Fatal — the ARCH likelihood is not an iid likelihood.* The trinity's statistic is
  `logLRStatistic M est est₀ n ω = 2 Σᵢ log(p_{θ̂}(ωᵢ) / p_{θ̂₀}(ωᵢ))`: one factor per
  observation, from a single `ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))`.
  `archLRStat` is built from `archLogLik = −½ · garchQuasiLik`, i.e.
  `−½ Σ_{t=ν}^{T−1} (log σ̃_t² + x_t²/σ̃_t²)` with `σ̃_t²` the truncated ARCH recursion
  `garchTruncVol`, which reads back `p` lags of the *same* sample. The `t`-th summand is
  a function of `x_{t−1}, …, x_{t−p}` as well as `x_t`, so it is not `log p_θ(x_t)` for
  any density family: the two are different functions of the data, not one function in
  two notations. This is intrinsic, not an artefact of the definitions — the likelihood
  ratio must be evaluated across the whole `(c₀, b)` space, where the ARCH observations
  are genuinely dependent; the iid collapse of `IsARCH.iid_of_b_eq_zero` holds only on
  the null slice `b = 0`. It is exactly why FY cites Serfling §4.4.4 as the source of the
  *limit law* rather than instantiating an iid-likelihood theorem: what the null iid
  structure makes classical is the behaviour of the score and information *averages* at
  `b = 0`, not the likelihood itself.
* *Fatal — no truncation parameter.* `archLRStat` carries the presample index `ν`, and
  `archLRStat_chiSq_debt` carries `νseq` with `ν → ∞`, `ν/T → 0`. The trinity has no such
  parameter, so the truncated-versus-exact conditional-likelihood bookkeeping that those
  hypotheses exist to control lies entirely outside its statement.
* *Serious — regularity currency.* The trinity consumes `IsPDFOf`, joint measurability of
  `(θ, x) ↦ p_θ(x)`, `DifferentiableQuadraticMean` at `θ₀` with an explicit score,
  a positive-definite Fisher matrix in the `⟪u, J v⟫` normalisation, `IsAsymptoticallyLinear`
  estimator sequences in the full *and* restricted charts, and the amended **two-point**
  second-order envelope `henv` with an integrable envelope `Menv`. The debts here supply
  only `MemLp (ε 0) 4 μ`. Nothing in this development establishes quadratic-mean
  differentiability of the ARCH family, and the Fisher information of eq. (4.51) is named
  in this docstring but never defined.
* *Bridgeable, but not free — the sample law.* The trinity concludes about
  `productMeasure M μ θ₀ n = Measure.pi …` on `Fin n → 𝓧`, whereas the debts push forward
  `μ` on the process space `Ω`. `IsARCH.iid_of_b_eq_zero` does give that the null law of
  `(X₁, …, X_T)` is such a product, so this mismatch alone would be honest work rather
  than an obstruction.
* *Bridgeable, but not free — the conclusion form.* The trinity concludes
  `WeakConverges … (MultipleTesting.chiSquared p)`; the debts ask for pointwise `charFun`
  convergence to an abstract `chiSq` pinned by `hchi`. Bridging needs both
  `WeakConverges → charFun` convergence and `charFun (MultipleTesting.chiSquared p) u =
  (1 − 2iu)^{−p/2}`, and the latter is not proved anywhere in the repo at present.

Only the affine-null *geometry* lines up cleanly: `k = p + 1` with coordinates
`(c₀, b₁, …, b_p)`, null subspace `a + range B` for `m = 1`, `B : ℝ → ℝ^{p+1}` the first
coordinate inclusion, giving exactly the `p` degrees of freedom FY reports (and, per the
boundary caveat above, the unconstrained parametrization the trinity needs). That
agreement is real but superficial: it fixes the degrees of freedom, not the statistic.

**Verdict: the trinity is not reusable here.** The three limits stay as named debts, and
closing them calls for a *time-series* likelihood theorem — a martingale CLT for the
conditional score of the ARCH quasi-likelihood, valid over the whole `(c₀, b)` space —
rather than an instance of the iid one.

## ⚠ The `hMLE` repair OVERSHOT: `archLRStat_chiSq_debt` and `archWaldStat_chiSq_debt` are VACUOUS

The `2026-08-09` amendment above (added to repair the falsity diagnosed in item (1)) pins
the estimators by requiring them to *globally maximize* `archLogLik` over **all** of
`ℝ × ℝᵖ`. No such maximizer exists, so `hMLE` and `hMLE0` are unsatisfiable and the two
statements carry no statistical content: both are proved below **by deriving `False` from
their own hypotheses**, not by any asymptotic argument. The two `sorry`s are gone; the
mathematics of FY eqs. (4.50), (4.54) is *not* formalized. Reading the module as
`1 sorry` would be a mistake — the honest count is one debt plus two vacuities.

The witness is `archLogLik_unbounded` (machine-checked): with `b = 0` the truncated
volatility is the *constant* `c₀` (`truncVol_const`, no positivity used, because the
presample value of `archLogLik` is `c₀` itself), so at `c₀ = −δ < 0`

  `archLogLik (−δ) 0 x ν = −½·(T−ν)·log δ + (Σ_{t=ν}^{T−1} x_t²)/(2δ) → +∞`  as `δ ↓ 0`,

using `Real.log (−δ) = Real.log δ` and the *sign flip* of the `x_t²/σ̃_t²` term at a
negative `σ̃_t²`: both summands of `−½(log σ̃_t² + x_t²/σ̃_t²)` diverge to `+∞` together.
`hνT` forces `νseq T < T` for all large `T`, so the sum is nonempty at some `T` and
`hMLE`/`hMLE0` are contradicted there (`false_of_bddAbove_archLogLik`). This is not an
artefact of `Real.log`'s totalization: restricting to `c₀ > 0` does not help either, since
negative `b` coordinates drive `σ̃_t² = c₀ + Σ b_i x_{t−i}²` negative just the same.

**The next amendment.** Maximization must be over the *admissible* set, on which the
criterion is bounded above — FY's `{c₀ > 0, b_j ≥ 0}`, or any constraint forcing
`σ̃_t² ≥ κ > 0` along the sample — or, better (item (2) above), the estimators should be
pinned in the trinity's currency: asymptotically linear with the ARCH score and
information. Either way it is a *statement* change, out of scope for a `sorry`-filling
lane. `archTR2Stat_chiSq_debt`'s `hrss`/`htss` do **not** have this defect: a
least-squares minimum is always attained, so its hypotheses are consistent and it remains
an honest debt.

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
  -- With `b = 0` the whole `Finset.sum` in the radicand vanishes, so the volatility is
  -- the *constant* `√c₀` and the recurrence reads `X_t = √c₀ · ε_t`.
  have hvol : ∀ (t : ℤ) (ω : Ω),
      archVol c0 (fun _ : Fin p => (0 : ℝ)) X t ω = Real.sqrt c0 := by
    intro t ω
    simp [archVol]
  have hX : ∀ t, X t =ᵐ[μ] fun ω => Real.sqrt c0 * ε t ω := by
    intro t
    filter_upwards [h.recurrence t] with ω hω
    rw [hω, hvol]
  refine ⟨hX, ?_⟩
  -- The scaling map `x ↦ √c₀ · x`, along which every `IsIIDNoise` field transports.
  have hsm : Measurable fun x : ℝ => Real.sqrt c0 * x := measurable_const_mul _
  have hsq : Real.sqrt c0 ^ 2 = c0 := Real.sq_sqrt h.c0_nonneg
  refine ⟨h.measurableX, ?_, ?_, ?_, ?_, ?_⟩
  · -- Independence: `iIndepFun` transports along the scaling and then along `=ᵐ`.
    have hind : iIndepFun (fun (t : ℤ) (ω : Ω) => Real.sqrt c0 * ε t ω) μ := by
      have := h.iid.iIndep.comp (fun _ : ℤ => fun x : ℝ => Real.sqrt c0 * x) fun _ => hsm
      simpa [Function.comp_def] using this
    exact (iIndepFun_congr fun t => (hX t).symm).mp hind
  · -- Identical distribution, through the scaled noise.
    intro s t
    have hs : IdentDistrib (X s) (fun ω => Real.sqrt c0 * ε s ω) μ μ :=
      IdentDistrib.of_ae_eq (h.measurableX s).aemeasurable (hX s)
    have ht : IdentDistrib (X t) (fun ω => Real.sqrt c0 * ε t ω) μ μ :=
      IdentDistrib.of_ae_eq (h.measurableX t).aemeasurable (hX t)
    exact (hs.trans ((h.iid.identDistrib s t).const_mul _)).trans ht.symm
  · exact (h.iid.memLp.const_mul (Real.sqrt c0)).ae_eq (hX 0).symm
  · rw [integral_congr_ae (hX 0)]
    have : ∫ ω, Real.sqrt c0 * ε 0 ω ∂μ = Real.sqrt c0 * ∫ ω, ε 0 ω ∂μ :=
      integral_const_mul _ _
    rw [this, h.iid.integral_eq_zero, mul_zero]
  · rw [variance_congr (hX 0), variance_const_mul, h.iid.variance_eq, mul_one, hsq]

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

/-! ### The unrestricted ARCH quasi-likelihood has no maximizer

The witness announced in the module docstring: `hMLE`/`hMLE0` of the two likelihood-based
debts below are unsatisfiable, so those debts are vacuous. -/

/-- At `b = 0` — and with the presample value `archLogLik` uses, namely `c₀` itself — the
truncated ARCH volatility is the *constant* `c₀`, for **every** real `c₀`. No positivity
is available here and none is needed: with `q = 0` the recursion has no volatility
feedback, so a single case split on `t` replaces the induction. -/
private lemma truncVol_const {p T : ℕ} (c : ℝ) (x : Fin T → ℝ) (t : ℕ) :
    garchTruncVol c (fun _ : Fin p => (0 : ℝ)) (Fin.elim0 : Fin 0 → ℝ) c x t = c := by
  cases t with
  | zero => simp [garchTruncVol]
  | succ n => simp [garchTruncVol]

/-- The closed form of the null log-likelihood at a **negative** variance parameter `−δ`:
`Real.log (−δ) = Real.log δ`, and the quadratic term keeps the factor `(−δ)⁻¹ < 0`, whose
sign the outer `−½` flips to `+`. So both summands push the criterion *up*. -/
private lemma archLogLik_neg {p T : ℕ} (δ : ℝ) (x : Fin T → ℝ) (ν : ℕ) :
    archLogLik (-δ) (fun _ : Fin p => (0 : ℝ)) x ν
      = -(1 / 2) * (((T - ν : ℕ) : ℝ) * Real.log δ
          + (∑ t ∈ Finset.Ico ν T, (if h : t < T then x ⟨t, h⟩ else 0) ^ 2) * (-δ)⁻¹) := by
  rw [archLogLik, garchQuasiLik]
  simp only [truncVol_const, Real.log_neg_eq_log, div_eq_mul_inv]
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul, Nat.card_Ico]
  simp

/-- **The witness.** As soon as the criterion's index set `Ico ν T` is nonempty, the null
ARCH log-likelihood is unbounded above on the unrestricted parameter space: take
`c₀ = −δ` with `δ = exp(−(2|M| + 2)/(T − ν))`, which makes the logarithmic part alone
equal `|M| + 1 > M` while the quadratic part is nonnegative. Hence no `(c₀, b)` maximizes
it, over the unrestricted set or over any set containing the negative axis. -/
private lemma archLogLik_unbounded {p T : ℕ} (x : Fin T → ℝ) {ν : ℕ} (hν : ν < T) (M : ℝ) :
    ∃ c : ℝ, M < archLogLik c (fun _ : Fin p => (0 : ℝ)) x ν := by
  have hn : 0 < T - ν := Nat.sub_pos_of_lt hν
  have hnR : (0 : ℝ) < ((T - ν : ℕ) : ℝ) := Nat.cast_pos.2 hn
  set δ : ℝ := Real.exp (-(2 * |M| + 2) / ((T - ν : ℕ) : ℝ)) with hδdef
  have hδ0 : 0 < δ := Real.exp_pos _
  refine ⟨-δ, ?_⟩
  rw [archLogLik_neg]
  have hlog : Real.log δ = -(2 * |M| + 2) / ((T - ν : ℕ) : ℝ) := Real.log_exp _
  have hS : 0 ≤ ∑ t ∈ Finset.Ico ν T, (if h : t < T then x ⟨t, h⟩ else 0) ^ 2 :=
    Finset.sum_nonneg fun t _ => sq_nonneg _
  have hkey : ((T - ν : ℕ) : ℝ) * Real.log δ = -(2 * |M| + 2) := by
    rw [hlog]; field_simp
  have hinv : (∑ t ∈ Finset.Ico ν T, (if h : t < T then x ⟨t, h⟩ else 0) ^ 2) * (-δ)⁻¹ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hS (inv_nonpos.2 (by linarith))
  have hM : M ≤ |M| := le_abs_self M
  rw [hkey]
  nlinarith [hinv, hM]

/-- The frozen `hMLE`/`hMLE0` shape — a global maximizer of the null log-likelihood, at
every sample size — is contradictory under `νseq T / T → 0`, which forces `νseq T < T` for
all large `T` and hence a nonempty criterion sum at some `T`. -/
private lemma false_of_bddAbove_archLogLik {p : ℕ} {νseq : ℕ → ℕ}
    (hνT : Tendsto (fun T : ℕ => (νseq T : ℝ) / T) atTop (𝓝 0))
    (data : (T : ℕ) → Fin T → ℝ) (F : ℕ → ℝ)
    (hmax : ∀ (T : ℕ) (c : ℝ),
      archLogLik c (fun _ : Fin p => (0 : ℝ)) (data T) (νseq T) ≤ F T) : False := by
  have h1 : ∀ᶠ T : ℕ in atTop, (νseq T : ℝ) / T < 1 / 2 :=
    hνT.eventually_lt_const (by norm_num)
  obtain ⟨T, hT, hT1⟩ := (h1.and (eventually_ge_atTop 1)).exists
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  have hlt : νseq T < T := by
    have : (νseq T : ℝ) < T := by
      have := (div_lt_iff₀ hTpos).1 hT
      linarith
    exact_mod_cast this
  obtain ⟨c, hc⟩ := archLogLik_unbounded (p := p) (data T) hlt (F T)
  exact absurd (hmax T c) (not_le.2 hc)

/-- A probability space is nonempty — needed to evaluate the contradictory hypotheses at a
sample point. -/
private lemma nonempty_of_isProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Nonempty Ω := by
  rcases isEmpty_or_nonempty Ω with hE | hE
  · have h1 : μ (Set.univ : Set Ω) = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.2 hE, measure_empty] at h1
    exact absurd h1 (by norm_num)
  · exact hE

/-- **FY eq. (4.50) — DEBT** (Serfling §4.4.4 via the iid structure under `H₀`): the
likelihood-ratio statistic has the `χ²_p` null limit. Recorded through the
distribution function of the limit (`chiSqLimitCDF` supplied as the comparison law, so
the statement does not depend on which χ² construction the repo settles on).

⚠ **VACUOUS as frozen, and the proof below says so.** `hMLE0` (equally `hMLE`) asks the
null-restricted estimator to maximize `archLogLik` over all of `ℝ`, and no maximizer
exists: `archLogLik_unbounded`. The proof is a derivation of `False` from the hypotheses;
it establishes nothing about FY eq. (4.50). See the module docstring for the amendment
this needs. -/
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
    -- USER-INPUT: the estimators are the unrestricted and null-restricted maximizers of
    -- the ARCH conditional log-likelihood. Added 2026-08-09: without them the statement
    -- is FALSE — arbitrary measurable sequences carry no distributional information.
    (hMLE : ∀ (T : ℕ) (ω : Ω) (c : ℝ) (bb : Fin p → ℝ),
      archLogLik c bb (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T)
        ≤ archLogLik (c0hat T ω) (bhat T ω)
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T))
    (hMLE0 : ∀ (T : ℕ) (ω : Ω) (c : ℝ),
      archLogLik c (fun _ : Fin p => (0 : ℝ))
          (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T)
        ≤ archLogLik (c0null T ω) (fun _ : Fin p => (0 : ℝ))
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T))
    -- USER-INPUT: the χ²_p limit law as a measure on ℝ; Serfling §4.4.4
    (chiSq : Measure ℝ) [IsProbabilityMeasure chiSq]
    (hchi : ∀ u : ℝ, charFun chiSq u = (1 - 2 * Complex.I * u) ^ (-(p : ℂ) / 2))
    (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        archLRStat (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T)
          (c0hat T ω) (bhat T ω) (c0null T ω)) u)
      atTop (𝓝 (charFun chiSq u)) := by
  -- The hypotheses are contradictory: `hMLE0` asserts a global maximizer of a criterion
  -- that `archLogLik_unbounded` shows is unbounded above.
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  exact (false_of_bddAbove_archLogLik (p := p) hνT
    (fun T => fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω₀)
    (fun T => archLogLik (c0null T ω₀) (fun _ : Fin p => (0 : ℝ))
      (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω₀) (νseq T))
    (fun T c => hMLE0 T ω₀ c)).elim

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
    -- USER-INPUT: `rss`/`tss` are the residual and centered total sums of squares of the
    -- auxiliary regression of `X_t²` on its `p` lags. Added 2026-08-09: without pinning
    -- them to the data the statement is FALSE (free reals carry no information).
    (hrss : ∀ (T : ℕ) (ω : Ω), IsLeast
      {r : ℝ | ∃ (β0 : ℝ) (β : Fin p → ℝ), r = ∑ t ∈ Finset.Ico p T,
        (X ((t : ℤ) + 1) ω ^ 2 - β0
          - ∑ j : Fin p, β j * X ((t : ℤ) - (j : ℕ)) ω ^ 2) ^ 2} (rss T ω))
    (htss : ∀ (T : ℕ) (ω : Ω), tss T ω = ∑ t ∈ Finset.Ico p T,
      (X ((t : ℤ) + 1) ω ^ 2
        - ((T : ℝ) - p)⁻¹ * ∑ u ∈ Finset.Ico p T, X ((u : ℤ) + 1) ω ^ 2) ^ 2)
    (chiSq : Measure ℝ) [IsProbabilityMeasure chiSq]
    (hchi : ∀ u : ℝ, charFun chiSq u = (1 - 2 * Complex.I * u) ^ (-(p : ℂ) / 2))
    (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        archTR2Stat (T := T) (rss T ω) (tss T ω)) u)
      atTop (𝓝 (charFun chiSq u)) := by
  sorry

/-- **FY eq. (4.54) — DEBT**: the Wald statistic (through the Schur-complement block
`I²²` of the information matrix) has the `χ²_p` null limit.

⚠ **VACUOUS as frozen, for the same reason as `archLRStat_chiSq_debt`**: `hMLE` asks for a
global maximizer of `archLogLik` over `ℝ × ℝᵖ`, which `archLogLik_unbounded` refutes. The
proof derives `False`; the consistency hypothesis `hIhat` on the information block is
never used, and FY eq. (4.54) is not formalized. -/
theorem archWaldStat_chiSq_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {X ε : ℤ → Ω → ℝ}
    (h : IsARCH c0 (fun _ : Fin p => (0 : ℝ)) X ε μ) (hc0 : 0 < c0)
    (hε4 : MemLp (ε 0) 4 μ)
    (bhat : (T : ℕ) → Ω → Fin p → ℝ) (hmeas : ∀ T, Measurable (bhat T))
    -- USER-INPUT: `bhat` is the unrestricted maximizer's ARCH block. Added 2026-08-09
    -- (an unconstrained sequence makes the statement FALSE).
    (c0hat : (T : ℕ) → Ω → ℝ)
    (νseq : ℕ → ℕ) (hν : Tendsto νseq atTop atTop)
    (hνT : Tendsto (fun T : ℕ => (νseq T : ℝ) / T) atTop (𝓝 0))
    (hMLE : ∀ (T : ℕ) (ω : Ω) (c : ℝ) (bb : Fin p → ℝ),
      archLogLik c bb (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T)
        ≤ archLogLik (c0hat T ω) (bhat T ω)
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (νseq T))
    -- USER-INPUT: the estimated information block I²² (Schur complement), assumed
    -- consistent for a positive-definite limit; FY eq. (4.54)
    (Ihat : (T : ℕ) → Ω → Matrix (Fin p) (Fin p) ℝ)
    (I0 : Matrix (Fin p) (Fin p) ℝ) (hI0 : Matrix.PosDef I0)
    (hIhat : ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ =>
      (μ {ω | δ ≤ ∑ i, ∑ j, |Ihat T ω i j - I0 i j|}).toReal) atTop (𝓝 0))
    (chiSq : Measure ℝ) [IsProbabilityMeasure chiSq]
    (hchi : ∀ u : ℝ, charFun chiSq u = (1 - 2 * Complex.I * u) ^ (-(p : ℂ) / 2))
    (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        (T : ℝ) * ∑ i, ∑ j, bhat T ω i * Ihat T ω i j * bhat T ω j) u)
      atTop (𝓝 (charFun chiSq u)) := by
  -- Contradictory hypotheses again: instantiate `hMLE` at the null direction `bb = 0`.
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  exact (false_of_bddAbove_archLogLik (p := p) hνT
    (fun T => fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω₀)
    (fun T => archLogLik (c0hat T ω₀) (bhat T ω₀)
      (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω₀) (νseq T))
    (fun T c => hMLE T ω₀ c (fun _ : Fin p => (0 : ℝ)))).elim

end StatLean.TimeSeries
