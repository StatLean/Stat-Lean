import StatLean.TimeSeries.ARMA.Likelihood
import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.Defs
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

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

section PiCoeff

/-- Negating the coefficients turns the MA polynomial into the AR polynomial (the two
differ only by FY's sign convention). -/
private lemma maPoly_neg {p : ℕ} (b : Fin p → ℝ) :
    maPoly (fun i => -b i) = arPoly b := by
  simp only [maPoly, arPoly, map_neg, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]

/-- ... and symmetrically: the AR polynomial of the negated MA coefficients is the MA
polynomial. -/
private lemma arPoly_neg {q : ℕ} (a : Fin q → ℝ) :
    arPoly (fun j => -a j) = maPoly a := by
  simp only [maPoly, arPoly, map_neg, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]

/-- **The inversion coefficients are the transfer coefficients with the roles of the two
lag polynomials swapped**: `π(z) = b(z)/a(z) = ψ(z)` for the parameters `(−a, −b)`. -/
private lemma armaPi_eq_armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) :
    armaPi b a n = armaPsi (fun j => -a j) (fun i => -b i) n := by
  rw [armaPi, armaPsi, maPoly_neg, arPoly_neg]

/-- Invertibility of `a` is root-freeness of the AR polynomial of `−a`. -/
private lemma noRootClosedDisc_neg {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) : NoRootClosedDisc (fun j => -a j) := by
  intro z hz
  rw [arPoly_neg]
  exact hB.2 z hz

end PiCoeff

/-- Geometric decay of the inversion coefficients on the constraint set. -/
theorem summable_abs_armaPi {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) :
    Summable fun n : ℕ => |armaPi b a n| := by
  simpa only [armaPi_eq_armaPsi] using
    summable_abs_armaPsi (fun i => -b i) (noRootClosedDisc_neg hB)

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
  -- **FALSE AS FROZEN** (reported debt; the statement is frozen, so no repair is applied).
  --
  -- `hannanVarZ b a` is the Gram matrix of the `ℓ²(ℤ)` vectors `g_i(m) = ψᵇ_{m+i}`,
  -- `h_j(m) = ψᵃ_{m+j}` (`ψᵇ = 1/b`, `ψᵃ = 1/a`), i.e. the covariance matrix of
  -- `(U_{t+i})_{i<p}, (V_{t+j})_{j<q}` over a common unit white noise. So
  -- `cᵀ (hannanVarZ b a) c = 0` iff `C(z)·a(z) + D(z)·b(z) = 0` for the polynomials
  -- `C(z) = Σ_i c_i z^{p-1-i}` (`deg C < p`) and `D(z) = Σ_j d_j z^{q-1-j}` (`deg D < q`).
  -- Coprimality gives `b ∣ C`, which forces `C = 0` only when `deg b = p`; with
  -- `deg b < p` a nonzero multiple `C = k·b` fits, and then `D = -k·a` fits as soon as
  -- `deg a < q` as well.
  --
  -- Witness (verified exactly): `p = q = 2`, `b = (1/2, 0)`, `a = (1/3, 0)`, so
  -- `arPoly b = 1 - z/2` and `maPoly a = 1 + z/3`. Both are root-free on the closed unit
  -- disc (roots `2` and `-3`), so `hB` holds; they are coprime, with the Bézout identity
  -- `(2/5)·(1 - z/2) + (3/5)·(1 + z/3) = 1`, so `hcop` holds. Yet with `ψᵇ_n = 2^{-n}`,
  -- `ψᵃ_n = (-3)^{-n}` the vector `c = (-1/2, 1, -1/3, -1)` (order `inl 0, inl 1,
  -- inr 0, inr 1`) satisfies `(hannanVarZ b a) *ᵥ c = 0`: the corresponding process
  -- combination is `(U_t - (1/2)U_{t-1}) - (V_t + (1/3)V_{t-1}) = ε_t - ε_t = 0`.
  -- (The same degeneracy occurs for the covariance matrix of the docstring's backward
  -- vector `Z = (U_{t-1-i}, V_{t-1-j})`, whose cross-blocks are the transposes of the
  -- ones used here, with the null vector `(1, -1/2, -1, -1/3)`.)
  --
  -- The missing hypothesis is FY's minimal-orders convention *in full*: besides `hcop`,
  -- `(arPoly b).natDegree = p` and `(maPoly a).natDegree = q` (equivalently
  -- `b_{p-1} ≠ 0` and `a_{q-1} ≠ 0`). Under those two extra hypotheses the argument
  -- above closes; as frozen, the statement admits the counterexample.
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

section ResidualAux

variable {X : ℤ → Ω → ℝ} {φ : ℕ → ℝ}

/-- `inner ℝ` on the reals is multiplication. -/
private lemma real_inner_mul (x y : ℝ) : inner ℝ x y = x * y := by
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp [mul_comm]

/-- The `L²` inner product of two classes is the integral of the product. -/
private lemma inner_toLp {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [real_inner_mul, h1, h2]

/-- The one-sided partial sum `Σ_{j<N} φ_j X_{t−j}` of the inversion filter. -/
private noncomputable def rpsum (φ : ℕ → ℝ) (X : ℤ → Ω → ℝ) (t : ℤ) (N : ℕ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.range N, φ j * X (t - (j : ℕ)) ω

private lemma memLp_rpsum (hX : IsStationary X μ) (t : ℤ) (N : ℕ) :
    MemLp (rpsum φ X t N) 2 μ :=
  memLp_finset_sum _ fun j _ => (hX.memLp (t - (j : ℕ))).const_mul (φ j)

private noncomputable def rpsumLp (hX : IsStationary X μ) (φ : ℕ → ℝ) (t : ℤ) (N : ℕ) :
    Lp ℝ 2 μ := (memLp_rpsum (φ := φ) hX t N).toLp _

private lemma coeFn_rpsumLp (hX : IsStationary X μ) (φ : ℕ → ℝ) (t : ℤ) (N : ℕ) :
    ⇑(rpsumLp hX φ t N) =ᵐ[μ] rpsum φ X t N :=
  (memLp_rpsum (φ := φ) hX t N).coeFn_toLp

/-- The `L²` norm of a stationary process is the same at every time. -/
private lemma norm_toLp_stationary [IsProbabilityMeasure μ] (hX : IsStationary X μ) (s : ℤ) :
    ‖(hX.memLp s).toLp (X s)‖ = ‖(hX.memLp 0).toLp (X 0)‖ := by
  have key : ∀ u : ℤ, ‖(hX.memLp u).toLp (X u)‖ ^ 2 = acvf X μ 0 + (∫ ω, X 0 ω ∂μ) ^ 2 := by
    intro u
    rw [← real_inner_self_eq_norm_sq, inner_toLp]
    have h := covariance_eq_sub (hX.memLp u) (hX.memLp u)
    have hcov : cov[X u, X u; μ] = acvf X μ 0 := by
      have h1 := hX.cov_eq_acvf u u
      rwa [sub_self] at h1
    have hmul : μ[X u * X u] = ∫ ω, X u ω * X u ω ∂μ := by simp [Pi.mul_apply]
    rw [hcov, hmul, hX.integral_eq u 0] at h
    have hsq : (∫ ω, X 0 ω ∂μ) ^ 2 = (∫ ω, X 0 ω ∂μ) * (∫ ω, X 0 ω ∂μ) := sq _
    linarith
  have e1 := Real.sqrt_sq (norm_nonneg ((hX.memLp s).toLp (X s)))
  have e2 := Real.sqrt_sq (norm_nonneg ((hX.memLp 0).toLp (X 0)))
  rw [← e1, ← e2, key s, key 0]

/-- Successive partial sums differ by the single term `φ_N X_{t−N}`. -/
private lemma dist_rpsumLp_succ [IsProbabilityMeasure μ] (hX : IsStationary X μ)
    (φ : ℕ → ℝ) (t : ℤ) (N : ℕ) :
    dist (rpsumLp hX φ t N) (rpsumLp hX φ t (N + 1))
      = |φ N| * ‖(hX.memLp 0).toLp (X 0)‖ := by
  rw [dist_comm, Lp.dist_def]
  have hae : (⇑(rpsumLp hX φ t (N + 1)) - ⇑(rpsumLp hX φ t N))
      =ᵐ[μ] (φ N • X (t - (N : ℕ))) := by
    filter_upwards [coeFn_rpsumLp hX φ t (N + 1), coeFn_rpsumLp hX φ t N] with ω h1 h2
    simp only [Pi.sub_apply, h1, h2, rpsum, Finset.sum_range_succ, Pi.smul_apply, smul_eq_mul]
    ring
  rw [eLpNorm_congr_ae hae, eLpNorm_const_smul, ENNReal.toReal_mul]
  have h : ((eLpNorm (X (t - (N : ℕ))) 2 μ)).toReal = ‖(hX.memLp 0).toLp (X 0)‖ := by
    rw [← Lp.norm_toLp _ (hX.memLp (t - (N : ℕ))), norm_toLp_stationary hX]
  rw [h]
  simp

/-- The `L²` limit of the one-sided partial sums exists for `ℓ¹` coefficients over a
stationary input (the one-sided instance of `exists_isFilteredBy`). -/
private lemma exists_rpsum_limit [IsProbabilityMeasure μ] (hφ : Summable fun n => |φ n|)
    (hX : IsStationary X μ) (t : ℤ) :
    ∃ f : Ω → ℝ, Measurable f ∧
      Tendsto (fun N => eLpNorm (fun ω => f ω - rpsum φ X t N ω) 2 μ) atTop (𝓝 0) := by
  have hsum : Summable fun N : ℕ =>
      dist (rpsumLp hX φ t N) (rpsumLp hX φ t N.succ) :=
    (hφ.mul_right ‖(hX.memLp 0).toLp (X 0)‖).congr fun N => (dist_rpsumLp_succ hX φ t N).symm
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
  refine ⟨(Lp.aestronglyMeasurable L).mk _,
    (Lp.aestronglyMeasurable L).stronglyMeasurable_mk.measurable, ?_⟩
  have heq : ∀ N : ℕ,
      eLpNorm (fun ω => ((Lp.aestronglyMeasurable L).mk _) ω - rpsum φ X t N ω) 2 μ
        = edist (rpsumLp hX φ t N) L := by
    intro N
    rw [edist_comm, Lp.edist_def]
    refine eLpNorm_congr_ae ?_
    filter_upwards [(Lp.aestronglyMeasurable L).ae_eq_mk, coeFn_rpsumLp hX φ t N] with ω h1 h2
    simp only [Pi.sub_apply, ← h1, h2]
  simp_rw [heq, edist_dist]
  simpa using ENNReal.tendsto_ofReal (tendsto_iff_dist_tendsto_zero.mp hL)

end ResidualAux

/-- Existence of the residual process on the constraint set (geometric `π`-decay +
stationarity, mirroring `exists_isFilteredBy`). -/
theorem exists_isARMAResidualOf [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X : ℤ → Ω → ℝ}
    (hB : ARMAInvertibleParams b a) (hstat : IsStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) :
    ∃ r : ℤ → Ω → ℝ, (∀ t, Measurable (r t)) ∧ IsARMAResidualOf b a r X μ := by
  choose r hrm hrlim using fun t : ℤ =>
    exists_rpsum_limit (φ := armaPi b a) (summable_abs_armaPi hB) hstat t
  exact ⟨r, hrm, hrlim⟩

/-- A finite linear combination of `L²`-approximable families is `L²`-approximable. -/
private lemma tendsto_eLpNorm_comb [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {F : ι → Ω → ℝ} {G : ι → ℕ → Ω → ℝ} (α : ι → ℝ)
    (hm : ∀ (i : ι) (N : ℕ), AEStronglyMeasurable (fun ω => F i ω - G i N ω) μ)
    (hconv : ∀ i : ι, Tendsto (fun N => eLpNorm (fun ω => F i ω - G i N ω) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (fun ω => (∑ i, α i * F i ω) - ∑ i, α i * G i N ω) 2 μ)
      atTop (𝓝 0) := by
  have hfun : ∀ N : ℕ, (fun ω => (∑ i, α i * F i ω) - ∑ i, α i * G i N ω)
      = ∑ i : ι, (α i • fun ω => F i ω - G i N ω) := by
    intro N
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
    rw [Finset.sum_sub_distrib]
  have hbd : ∀ N : ℕ, eLpNorm (fun ω => (∑ i, α i * F i ω) - ∑ i, α i * G i N ω) 2 μ
      ≤ ∑ i : ι, ‖α i‖ₑ * eLpNorm (fun ω => F i ω - G i N ω) 2 μ := by
    intro N
    rw [hfun N]
    refine (eLpNorm_sum_le (fun i _ => (hm i N).const_smul _) one_le_two).trans ?_
    exact le_of_eq (Finset.sum_congr rfl fun i _ => by rw [eLpNorm_const_smul])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun N => zero_le _) hbd
  have hterm : ∀ i : ι, Tendsto
      (fun N : ℕ => ‖α i‖ₑ * eLpNorm (fun ω => F i ω - G i N ω) 2 μ) atTop (𝓝 0) := fun i => by
    simpa using ENNReal.Tendsto.const_mul (a := ‖α i‖ₑ) (hconv i) (Or.inr (by simp))
  have hsum := tendsto_finset_sum (Finset.univ : Finset ι) fun i (_ : i ∈ Finset.univ) => hterm i
  simpa using hsum

section ResidualId

/-- The constant coefficient of the AR polynomial is `1`. -/
private lemma coeff_zero_arPoly {p : ℕ} (b : Fin p → ℝ) : (arPoly b).coeff 0 = 1 := by
  simp [arPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

/-- The constant coefficient of the MA polynomial is `1`. -/
private lemma coeff_zero_maPoly {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  simp [maPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

/-- **`π ∗ ψ = δ₀`**: the inversion coefficients (`b/a`) and the transfer coefficients
(`a/b`) are mutually inverse power series, so their convolution is the unit. -/
private lemma armaPi_conv_armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), armaPi b a k * armaPsi b a (m - k)
      = if m = 0 then 1 else 0 := by
  have hA : PowerSeries.constantCoeff (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_zero_arPoly]
    exact one_ne_zero
  have hMA : PowerSeries.constantCoeff (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_zero_maPoly]
    exact one_ne_zero
  have h1 := PowerSeries.mul_inv_cancel _ hA
  have h2 := PowerSeries.mul_inv_cancel _ hMA
  have key : ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ))
        * ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)
      * (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))
        * ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) = 1 := by
    calc ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ))
          * ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)
        * (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))
          * ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)
        = ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ))
            * ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)
          * (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))
            * ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have hc := congrArg (PowerSeries.coeff m) key
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_one] at hc
  exact hc

variable {ε : ℤ → Ω → ℝ} {σ2 : ℝ}

/-- The `L²` norm of white noise is the same at every time. -/
private lemma eLpNorm_noise_eq [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ) (s : ℤ) :
    eLpNorm (ε s) 2 μ = ENNReal.ofReal (Real.sqrt σ2) := by
  have hsq : ‖(hε.memLp s).toLp (ε s)‖ ^ 2 = σ2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp]
    have hc := covariance_eq_sub (hε.memLp s) (hε.memLp s)
    rw [hε.integral_eq_zero s, zero_mul, sub_zero,
      covariance_self (hε.memLp s).aestronglyMeasurable.aemeasurable, hε.variance_eq s] at hc
    have h2 : μ[ε s * ε s] = ∫ ω, ε s ω * ε s ω ∂μ := by simp [Pi.mul_apply]
    rw [h2] at hc
    exact hc.symm
  have hnorm : ‖(hε.memLp s).toLp (ε s)‖ = Real.sqrt σ2 := by
    have hh := Real.sqrt_sq (norm_nonneg ((hε.memLp s).toLp (ε s)))
    rw [hsq] at hh
    exact hh.symm
  rw [Lp.norm_toLp] at hnorm
  rw [← hnorm, ENNReal.ofReal_toReal (hε.memLp s).2.ne]

/-- The `L²` norm of a finite noise combination is at most the `ℓ¹` mass of the
coefficients times the noise scale. -/
private lemma eLpNorm_noise_comb_le [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    {ι : Type*} (s : Finset ι) (cc : ι → ℝ) (u : ι → ℤ) :
    eLpNorm (fun ω => ∑ i ∈ s, cc i * ε (u i) ω) 2 μ
      ≤ ENNReal.ofReal (∑ i ∈ s, |cc i|) * ENNReal.ofReal (Real.sqrt σ2) := by
  have hfun : (fun ω => ∑ i ∈ s, cc i * ε (u i) ω) = ∑ i ∈ s, fun ω => cc i * ε (u i) ω := by
    funext ω; simp
  rw [hfun]
  refine (eLpNorm_sum_le (fun i _ =>
    ((hε.measurable (u i)).const_mul (cc i)).aestronglyMeasurable) one_le_two).trans ?_
  have hterm : ∀ i, eLpNorm (fun ω => cc i * ε (u i) ω) 2 μ
      = ENNReal.ofReal |cc i| * ENNReal.ofReal (Real.sqrt σ2) := by
    intro i
    have hsm : (fun ω => cc i * ε (u i) ω) = cc i • (ε (u i)) := by funext ω; simp
    rw [hsm, eLpNorm_const_smul, eLpNorm_noise_eq hε]
    congr 1
    simp [Real.enorm_eq_ofReal_abs]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]

end ResidualId

/-- **Residuals at the truth recover the innovations**: for a stationary causal
invertible ARMA at its true parameters, `ε_t(θ₀) = ε_t` a.e. -/
theorem isARMAResidualOf_eq_noise [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε r : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hB : ARMAInvertibleParams b a)
    (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    (hr : IsARMAResidualOf b a r X μ) (hrmeas : ∀ t, Measurable (r t)) (t : ℤ) :
    r t =ᵐ[μ] ε t := by
  classical
  have hεWN : IsWhiteNoise ε σ2 μ := h.whiteNoise
  -- Opaque copies of the two coefficient sequences: their power-series definitions must
  -- never be unfolded during elaboration (`PowerSeries.inv` is well-founded recursion).
  obtain ⟨π, hπdef⟩ : ∃ f : ℕ → ℝ, f = armaPi b a := ⟨_, rfl⟩
  obtain ⟨ψc, hψdef⟩ : ∃ f : ℕ → ℝ, f = armaPsi b a := ⟨_, rfl⟩
  have hπ : Summable fun n : ℕ => |π n| := by
    rw [hπdef]; exact summable_abs_armaPi hB
  have hψ : Summable fun n : ℕ => |ψc n| := by
    rw [hψdef]; exact summable_abs_armaPsi a hB.1
  have hconv0 : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), π k * ψc (m - k)
      = if m = 0 then 1 else 0 := by
    rw [hπdef, hψdef]; exact armaPi_conv_armaPsi b a
  have hlin : ∀ s : ℤ, Tendsto (fun M : ℕ => eLpNorm
      (fun ω => X s ω - ∑ l ∈ Finset.range M, ψc l * ε (s - (l : ℕ)) ω) 2 μ) atTop (𝓝 0) := by
    rw [hψdef]; exact hcausal
  have hres : Tendsto (fun N : ℕ => eLpNorm
      (fun ω => r t ω - ∑ j ∈ Finset.range N, π j * X (t - (j : ℕ)) ω) 2 μ) atTop (𝓝 0) := by
    rw [hπdef]; exact hr t
  have hXmem : ∀ s, MemLp (X s) 2 μ :=
    hcausal.memLp (summable_abs_armaPsi a hB.1) hεWN hmeas
  have hF : Summable fun x : ℕ × ℕ => |π x.1| * |ψc x.2| :=
    hπ.mul_of_nonneg hψ (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  -- the triangular exhaustion of the coefficient index set
  obtain ⟨Tri, hTri⟩ : ∃ T : ℕ → Finset (ℕ × ℕ), T = fun N =>
      (Finset.range N ×ˢ Finset.range N).filter fun x => x.1 + x.2 < N := ⟨_, rfl⟩
  have hTriMem : ∀ (N : ℕ) (x : ℕ × ℕ), x ∈ Tri N ↔ x.1 + x.2 < N := by
    intro N x
    simp only [hTri, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  -- each antidiagonal contributes the convolution `π ∗ ψ`, i.e. `δ₀`
  have hantidiag : ∀ (m : ℕ) (ω : Ω),
      ∑ x ∈ Finset.antidiagonal m, (π x.1 * ψc x.2) * ε (t - (x.1 : ℕ) - (x.2 : ℕ)) ω
        = (if m = 0 then 1 else 0) * ε (t - (m : ℕ)) ω := by
    intro m ω
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hcong : ∀ k ∈ Finset.range (m + 1),
        (π k * ψc (m - k)) * ε (t - (k : ℕ) - ((m - k : ℕ) : ℕ)) ω
          = (π k * ψc (m - k)) * ε (t - (m : ℕ)) ω := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hidx : t - (k : ℤ) - ((m - k : ℕ) : ℤ) = t - (m : ℤ) := by omega
      rw [hidx]
    rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, hconv0]
  -- so the triangle sums telescope to the innovation itself
  have hTriSum : ∀ (N : ℕ) (ω : Ω),
      ∑ x ∈ Tri (N + 1), (π x.1 * ψc x.2) * ε (t - (x.1 : ℕ) - (x.2 : ℕ)) ω = ε t ω := by
    intro N ω
    induction N with
    | zero =>
      have h1 : Tri 1 = {((0 : ℕ), (0 : ℕ))} := by
        ext x
        rw [hTriMem]
        simp only [Finset.mem_singleton, Prod.ext_iff]
        omega
      have h0 : π 0 * ψc 0 = 1 := by
        have hh := hconv0 0
        simpa using hh
      rw [h1, Finset.sum_singleton, h0]
      simp
    | succ n ih =>
      have hsplit : Tri (n + 2) = Tri (n + 1) ∪ Finset.antidiagonal (n + 1) := by
        ext x
        rw [Finset.mem_union, hTriMem, hTriMem, Finset.mem_antidiagonal]
        omega
      have hdisj : Disjoint (Tri (n + 1)) (Finset.antidiagonal (n + 1)) := by
        rw [Finset.disjoint_left]
        intro x hx hx2
        rw [hTriMem] at hx
        rw [Finset.mem_antidiagonal] at hx2
        omega
      rw [hsplit, Finset.sum_union hdisj, ih, hantidiag]
      simp
  -- the one-sided partial sums of the inversion filter and their noise expansions
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Ω → ℝ, S = fun N ω =>
    ∑ j ∈ Finset.range N, π j * X (t - (j : ℕ)) ω := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ → Ω → ℝ, P = fun N M ω =>
    ∑ x ∈ Finset.range N ×ˢ Finset.range M,
      (π x.1 * ψc x.2) * ε (t - (x.1 : ℕ) - (x.2 : ℕ)) ω := ⟨_, rfl⟩
  have hSmeas : ∀ N, Measurable (S N) := by
    intro N
    rw [hS]
    exact Finset.measurable_sum _ fun j _ => (hmeas _).const_mul _
  have hPmeas : ∀ N M, Measurable (P N M) := by
    intro N M
    rw [hP]
    exact Finset.measurable_sum _ fun x _ => (hεWN.measurable _).const_mul _
  -- for a fixed number of `π`-terms the noise expansion converges in `L²`
  have hSP : ∀ N : ℕ, Tendsto (fun M => eLpNorm (fun ω => S N ω - P N M ω) 2 μ)
      atTop (𝓝 0) := by
    intro N
    have hcomb := tendsto_eLpNorm_comb (μ := μ)
      (F := fun i : Fin N => X (t - (i : ℕ)))
      (G := fun (i : Fin N) (M : ℕ) ω =>
        ∑ l ∈ Finset.range M, ψc l * ε (t - (i : ℕ) - (l : ℕ)) ω)
      (fun i : Fin N => π i)
      (fun i M => (hmeas _).aestronglyMeasurable.sub
        (Finset.measurable_sum _ fun l _ => (hεWN.measurable _).const_mul _).aestronglyMeasurable)
      (fun i => hlin (t - (i : ℕ)))
    refine hcomb.congr fun M => congrArg (fun f => eLpNorm f 2 μ) (funext fun ω => ?_)
    simp only [hS, hP]
    rw [Finset.sum_product]
    congr 1
    · exact Fin.sum_univ_eq_sum_range (fun j => π j * X (t - (j : ℕ)) ω) N
    · rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ l ∈ Finset.range M,
        (π j * ψc l) * ε (t - (j : ℕ) - (l : ℕ)) ω) N]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
  -- the coefficient mass outside the triangle
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℝ, E = fun N =>
    (∑' x : ℕ × ℕ, |π x.1| * |ψc x.2|) - ∑ x ∈ Tri N, |π x.1| * |ψc x.2| := ⟨_, rfl⟩
  have hPε : ∀ N M : ℕ, N + 1 ≤ M →
      eLpNorm (fun ω => P (N + 1) M ω - ε t ω) 2 μ
        ≤ ENNReal.ofReal (E (N + 1)) * ENNReal.ofReal (Real.sqrt σ2) := by
    intro N M hNM
    obtain ⟨D, hD⟩ : ∃ D : Finset (ℕ × ℕ),
        D = (Finset.range (N + 1) ×ˢ Finset.range M) \ Tri (N + 1) := ⟨_, rfl⟩
    have hsub : Tri (N + 1) ⊆ Finset.range (N + 1) ×ˢ Finset.range M := by
      intro x hx
      rw [hTriMem] at hx
      simp only [Finset.mem_product, Finset.mem_range]
      omega
    have hdiff : (fun ω => P (N + 1) M ω - ε t ω)
        = fun ω => ∑ x ∈ D, (π x.1 * ψc x.2) * ε (t - (x.1 : ℕ) - (x.2 : ℕ)) ω := by
      funext ω
      have hsd := Finset.sum_sdiff (f := fun x : ℕ × ℕ =>
        (π x.1 * ψc x.2) * ε (t - (x.1 : ℕ) - (x.2 : ℕ)) ω) hsub
      rw [hD]
      simp only [hP]
      rw [← hsd, hTriSum N ω]
      ring
    have hmass : ∑ x ∈ D, |π x.1 * ψc x.2| ≤ E (N + 1) := by
      have hdj : Disjoint D (Tri (N + 1)) := by
        rw [hD]; exact Finset.sdiff_disjoint
      have hunion := Finset.sum_union (f := fun x : ℕ × ℕ => |π x.1| * |ψc x.2|) hdj
      have hle : ∑ x ∈ D ∪ Tri (N + 1), |π x.1| * |ψc x.2|
          ≤ ∑' x : ℕ × ℕ, |π x.1| * |ψc x.2| :=
        hF.sum_le_tsum _ fun x _ => by positivity
      rw [hE]
      simp only [abs_mul]
      linarith
    rw [hdiff]
    refine (eLpNorm_noise_comb_le hεWN D (fun x => π x.1 * ψc x.2)
      (fun x => t - (x.1 : ℕ) - (x.2 : ℕ))).trans ?_
    -- (`mul_le_mul_right'` is deprecated upstream; the ENNReal `gcongr` route needs the
    -- same side goal, so keep the explicit form)
    exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal hmass) _
  -- the tail mass vanishes
  have hTriTendsto : Tendsto (fun N => ∑ x ∈ Tri N, |π x.1| * |ψc x.2|)
      atTop (𝓝 (∑' x : ℕ × ℕ, |π x.1| * |ψc x.2|)) := by
    refine hF.hasSum.comp (tendsto_atTop_finset_of_monotone ?_ ?_)
    · intro m n hmn
      simp only [Finset.le_eq_subset]
      intro x hx
      rw [hTriMem] at hx ⊢
      omega
    · intro x
      exact ⟨x.1 + x.2 + 1, (hTriMem _ _).2 (by omega)⟩
  have hE0 : Tendsto E atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => ∑' x : ℕ × ℕ, |π x.1| * |ψc x.2|) atTop
        (𝓝 (∑' x : ℕ × ℕ, |π x.1| * |ψc x.2|)) := tendsto_const_nhds
    rw [hE]
    simpa using hconst.sub hTriTendsto
  -- hence the `π`-partial sums converge to the innovation
  have hSε : ∀ N : ℕ, eLpNorm (fun ω => S (N + 1) ω - ε t ω) 2 μ
      ≤ ENNReal.ofReal (E (N + 1)) * ENNReal.ofReal (Real.sqrt σ2) := by
    intro N
    have hlim : Tendsto (fun M => eLpNorm (fun ω => S (N + 1) ω - P (N + 1) M ω) 2 μ
        + ENNReal.ofReal (E (N + 1)) * ENNReal.ofReal (Real.sqrt σ2)) atTop
        (𝓝 (ENNReal.ofReal (E (N + 1)) * ENNReal.ofReal (Real.sqrt σ2))) := by
      simpa using (hSP (N + 1)).add tendsto_const_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (N + 1)] with M hM
    have hfun : (fun ω => S (N + 1) ω - ε t ω)
        = (fun ω => S (N + 1) ω - P (N + 1) M ω) + fun ω => P (N + 1) M ω - ε t ω := by
      funext ω
      simp only [Pi.add_apply]
      ring
    calc eLpNorm (fun ω => S (N + 1) ω - ε t ω) 2 μ
        ≤ eLpNorm (fun ω => S (N + 1) ω - P (N + 1) M ω) 2 μ
          + eLpNorm (fun ω => P (N + 1) M ω - ε t ω) 2 μ := by
          rw [hfun]
          exact eLpNorm_add_le ((hSmeas _).sub (hPmeas _ _)).aestronglyMeasurable
            ((hPmeas _ _).sub (hεWN.measurable t)).aestronglyMeasurable one_le_two
      _ ≤ _ := add_le_add le_rfl (hPε N M hM)
  have hStend : Tendsto (fun N => eLpNorm (fun ω => S N ω - ε t ω) 2 μ) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ =>
        ENNReal.ofReal (E (N + 1)) * ENNReal.ofReal (Real.sqrt σ2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => ENNReal.ofReal (E (N + 1))) atTop (𝓝 0) := by
        have h2 := ENNReal.tendsto_ofReal (hE0.comp (tendsto_add_atTop_nat 1))
        simpa using h2
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inr ENNReal.ofReal_ne_top)
    have hshift : Tendsto (fun N => eLpNorm (fun ω => S (N + 1) ω - ε t ω) 2 μ) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
        (fun N => zero_le _) hSε
    exact (tendsto_add_atTop_iff_nat 1).1 hshift
  -- ... and the residual is that same limit
  have hrS : Tendsto (fun N => eLpNorm (fun ω => r t ω - S N ω) 2 μ) atTop (𝓝 0) := by
    simpa only [hS] using hres
  have hzero : eLpNorm (fun ω => r t ω - ε t ω) 2 μ = 0 := by
    have hlim : Tendsto (fun N => eLpNorm (fun ω => r t ω - S N ω) 2 μ
        + eLpNorm (fun ω => S N ω - ε t ω) 2 μ) atTop (𝓝 0) := by
      simpa using hrS.add hStend
    refine le_antisymm (ge_of_tendsto hlim (Eventually.of_forall fun N => ?_)) (zero_le _)
    have hfun : (fun ω => r t ω - ε t ω)
        = (fun ω => r t ω - S N ω) + fun ω => S N ω - ε t ω := by
      funext ω
      simp only [Pi.add_apply]
      ring
    rw [hfun]
    exact eLpNorm_add_le ((hrmeas t).sub (hSmeas N)).aestronglyMeasurable
      ((hSmeas N).sub (hεWN.measurable t)).aestronglyMeasurable one_le_two
  have hae := (eLpNorm_eq_zero_iff
    ((hrmeas t).sub (hεWN.measurable t)).aestronglyMeasurable two_ne_zero).1 hzero
  filter_upwards [hae] with ω hω
  have hω' : r t ω - ε t ω = 0 := hω
  linarith

section ScoreAux

omit [MeasurableSpace Ω] in
private lemma comap_le_sigmaLT {Z : ℤ → Ω → ℝ} {s t : ℤ} (hst : s < t) :
    MeasurableSpace.comap (Z s) inferInstance ≤ sigmaLT Z t :=
  le_iSup₂ (f := fun s (_ : s ∈ Set.Iio t) => MeasurableSpace.comap (Z s) inferInstance) s hst

private lemma sigmaLT_le {Z : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (Z t)) (t : ℤ) :
    sigmaLT Z t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun _ _ => (hm _).comap_le

omit [MeasurableSpace Ω] in
/-- Past values are measurable for the strict past. -/
private lemma measurable_sigmaLT {Z : ℤ → Ω → ℝ} {s t : ℤ} (hst : s < t) :
    Measurable[sigmaLT Z t] (Z s) :=
  (Measurable.of_comap_le (le_refl (MeasurableSpace.comap (Z s) inferInstance))).mono
    (comap_le_sigmaLT hst) le_rfl

/-- **One-vs-past independence of i.i.d. noise**: `ε_t` is independent of
`σ(ε_s : s < t)` (the `Stationarity/ARCH.lean` pull, replayed here). -/
private lemma indep_noise_sigmaLT {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t))
    (hi : iIndepFun ε μ) (t : ℤ) :
    Indep (MeasurableSpace.comap (ε t) inferInstance) (sigmaLT ε t) μ := by
  have hdisj : Disjoint ({t} : Set ℤ) (Set.Iio t) :=
    Set.disjoint_singleton_left.2 (by simp)
  have := indep_iSup_of_disjoint
    (m := fun s : ℤ => MeasurableSpace.comap (ε s) inferInstance)
    (fun s => (hm s).comap_le) hi hdisj
  simpa using this

/-- `E[ε_t | 𝓕_{t−1}] = 0`: independence of the past plus the vanishing mean. -/
private lemma condExp_noise_eq_zero [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hiid : IsIIDNoise ε σ2 μ) (t : ℤ) :
    μ[ε t | sigmaLT ε t] =ᵐ[μ] 0 := by
  have hle : sigmaLT ε t ≤ (inferInstance : MeasurableSpace Ω) := sigmaLT_le hiid.measurable t
  have hmean : ∫ ω, ε t ω ∂μ = 0 := by
    rw [(hiid.identDistrib t 0).integral_eq, hiid.integral_eq_zero]
  have h := condExp_indep_eq (hiid.measurable t).comap_le hle
    (Measurable.stronglyMeasurable
      (Measurable.of_comap_le (le_refl (MeasurableSpace.comap (ε t) inferInstance))))
    (indep_noise_sigmaLT hiid.measurable hiid.iIndep t)
  filter_upwards [h] with ω hω
  rw [hω, hmean]
  rfl

/-- **The martingale-difference brick**: if `W` is the `L²` limit of a sequence of
`σ(ε_s : s < t)`-measurable variables, then `E[ε_t · W | σ(ε_s : s < t)] = 0`. The
`L²` approximants are only *approximately* past-measurable, so the pull-out is applied
to them and the limit is taken in `L¹` (no measurable version of `W` is needed). -/
private lemma condExp_noise_mul_eq_zero [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hiid : IsIIDNoise ε σ2 μ) (t : ℤ) {W : Ω → ℝ} (hW : MemLp W 2 μ) {WN : ℕ → Ω → ℝ}
    (hWNmeas : ∀ N, StronglyMeasurable[sigmaLT ε t] (WN N))
    (hWNmem : ∀ N, MemLp (WN N) 2 μ)
    (hconv : Tendsto (fun N => eLpNorm (fun ω => W ω - WN N ω) 2 μ) atTop (𝓝 0)) :
    μ[fun ω => ε t ω * W ω | sigmaLT ε t] =ᵐ[μ] 0 := by
  have hεL2 : MemLp (ε t) 2 μ := ((hiid.identDistrib t 0).memLp_iff).2 hiid.memLp
  have hεint : Integrable (ε t) μ := hεL2.integrable one_le_two
  have hprod : ∀ g : Ω → ℝ, MemLp g 2 μ → Integrable (ε t * g) μ :=
    fun g hg => hεL2.integrable_mul hg
  have hlam : (fun ω => ε t ω * W ω) = ε t * W := rfl
  rw [hlam]
  -- the pull-out kills every approximant
  have hzeroN : ∀ N, μ[ε t * WN N | sigmaLT ε t] =ᵐ[μ] 0 := by
    intro N
    have hpull : μ[ε t * WN N | sigmaLT ε t] =ᵐ[μ] μ[ε t | sigmaLT ε t] * WN N :=
      condExp_mul_of_stronglyMeasurable_right (hWNmeas N) (hprod _ (hWNmem N)) hεint
    filter_upwards [hpull, condExp_noise_eq_zero hiid t] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
    simp
  -- the difference is small in `L¹`
  have hsplit : ∀ N, μ[ε t * W | sigmaLT ε t]
      =ᵐ[μ] μ[ε t * (W - WN N) | sigmaLT ε t] := by
    intro N
    have hadd : μ[ε t * WN N + ε t * (W - WN N) | sigmaLT ε t]
        =ᵐ[μ] μ[ε t * WN N | sigmaLT ε t] + μ[ε t * (W - WN N) | sigmaLT ε t] :=
      condExp_add (hprod _ (hWNmem N)) (hprod _ (hW.sub (hWNmem N))) _
    have hfun : (ε t * WN N + ε t * (W - WN N)) = ε t * W := by
      funext ω
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
      ring
    rw [hfun] at hadd
    filter_upwards [hadd, hzeroN N] with ω h1 h2
    rw [h1, Pi.add_apply, h2]
    simp
  -- ... and the `L¹` norm of the conditional expectation is dominated by it
  have hbound : ∀ N, eLpNorm (μ[ε t * W | sigmaLT ε t]) 1 μ
      ≤ eLpNorm (ε t) 2 μ * eLpNorm (fun ω => W ω - WN N ω) 2 μ := by
    intro N
    rw [eLpNorm_congr_ae (hsplit N)]
    refine (eLpNorm_one_condExp_le_eLpNorm _).trans ?_
    have hsmul : (ε t * (W - WN N)) = (ε t) • (fun ω => W ω - WN N ω) := by
      funext ω
      simp [smul_eq_mul]
    rw [hsmul]
    exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
      (hpqr := ENNReal.HolderConjugate.instTwoTwo)
      ((hW.sub (hWNmem N)).aestronglyMeasurable) hεL2.aestronglyMeasurable
  have hlim : Tendsto (fun N => eLpNorm (ε t) 2 μ * eLpNorm (fun ω => W ω - WN N ω) 2 μ)
      atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := eLpNorm (ε t) 2 μ) hconv (Or.inr hεL2.2.ne)
    simpa using this
  have hzero : eLpNorm (μ[ε t * W | sigmaLT ε t]) 1 μ = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound)) (zero_le _)
  -- (the `mono` keeps the elaborator from unifying `sigmaLT ε t` with the ambient σ-algebra)
  have hle : sigmaLT ε t ≤ (inferInstance : MeasurableSpace Ω) := sigmaLT_le hiid.measurable t
  exact (eLpNorm_eq_zero_iff
    (stronglyMeasurable_condExp.mono hle).aestronglyMeasurable one_ne_zero).1 hzero

end ScoreAux

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
  classical
  have hε : IsWhiteNoise ε σ2 μ := h.whiteNoise
  have hψb : Summable fun n => |armaPsi b (Fin.elim0 : Fin 0 → ℝ) n| :=
    summable_abs_armaPsi (Fin.elim0 : Fin 0 → ℝ) hB.1
  have hψa : Summable fun n => |armaPsi (fun j => -a j) (Fin.elim0 : Fin 0 → ℝ) n| :=
    summable_abs_armaPsi (Fin.elim0 : Fin 0 → ℝ) (noRootClosedDisc_neg hB)
  have hUmem : ∀ s, MemLp (U s) 2 μ := hU.memLp hψb hε hUmeas
  have hVmem : ∀ s, MemLp (V s) 2 μ := hV.memLp hψa hε hVmeas
  have hlt : ∀ k n : ℕ, t - 1 - (k : ℕ) - (n : ℕ) < t := by
    intro k n
    have h1 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    have h2 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    omega
  refine condExp_noise_mul_eq_zero hiid t ?_
    (WN := fun N ω =>
      (∑ i : Fin p, c (.inl i) * ∑ n ∈ Finset.range N,
          armaPsi b (Fin.elim0 : Fin 0 → ℝ) n * ε (t - 1 - (i : ℕ) - (n : ℕ)) ω)
        + ∑ j : Fin q, c (.inr j) * ∑ n ∈ Finset.range N,
            armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ) n
              * ε (t - 1 - (j : ℕ) - (n : ℕ)) ω) ?_ ?_ ?_
  · exact (memLp_finset_sum _ fun i _ => (hUmem _).const_mul _).add
      (memLp_finset_sum _ fun j _ => (hVmem _).const_mul _)
  · intro N
    refine Measurable.stronglyMeasurable (Measurable.add ?_ ?_) <;>
      exact Finset.measurable_sum _ fun i _ => measurable_const.mul
        (Finset.measurable_sum _ fun n _ => measurable_const.mul (measurable_sigmaLT (hlt _ _)))
  · intro N
    exact (memLp_finset_sum _ fun i _ =>
        (memLp_finset_sum _ fun n _ => (hε.memLp _).const_mul _).const_mul _).add
      (memLp_finset_sum _ fun j _ =>
        (memLp_finset_sum _ fun n _ => (hε.memLp _).const_mul _).const_mul _)
  · -- the two blocks converge separately
    have hUconv := tendsto_eLpNorm_comb (μ := μ)
      (F := fun i : Fin p => U (t - 1 - (i : ℕ)))
      (G := fun (i : Fin p) (N : ℕ) ω => ∑ n ∈ Finset.range N,
        armaPsi b (Fin.elim0 : Fin 0 → ℝ) n * ε (t - 1 - (i : ℕ) - (n : ℕ)) ω)
      (fun i => c (.inl i))
      (fun i N => (hUmeas _).aestronglyMeasurable.sub
        (Finset.measurable_sum _ fun n _ => (hε.measurable _).const_mul _).aestronglyMeasurable)
      (fun i => hU (t - 1 - (i : ℕ)))
    have hVconv := tendsto_eLpNorm_comb (μ := μ)
      (F := fun j : Fin q => V (t - 1 - (j : ℕ)))
      (G := fun (j : Fin q) (N : ℕ) ω => ∑ n ∈ Finset.range N,
        armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ) n
          * ε (t - 1 - (j : ℕ) - (n : ℕ)) ω)
      (fun j => c (.inr j))
      (fun j N => (hVmeas _).aestronglyMeasurable.sub
        (Finset.measurable_sum _ fun n _ => (hε.measurable _).const_mul _).aestronglyMeasurable)
      (fun j => hV (t - 1 - (j : ℕ)))
    have hbd : ∀ N : ℕ,
        eLpNorm (fun ω =>
          ((∑ i : Fin p, c (.inl i) * U (t - 1 - (i : ℕ)) ω)
              + ∑ j : Fin q, c (.inr j) * V (t - 1 - (j : ℕ)) ω)
            - ((∑ i : Fin p, c (.inl i) * ∑ n ∈ Finset.range N,
                  armaPsi b (Fin.elim0 : Fin 0 → ℝ) n * ε (t - 1 - (i : ℕ) - (n : ℕ)) ω)
                + ∑ j : Fin q, c (.inr j) * ∑ n ∈ Finset.range N,
                    armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ) n
                      * ε (t - 1 - (j : ℕ) - (n : ℕ)) ω)) 2 μ
        ≤ eLpNorm (fun ω => (∑ i : Fin p, c (.inl i) * U (t - 1 - (i : ℕ)) ω)
              - ∑ i : Fin p, c (.inl i) * ∑ n ∈ Finset.range N,
                  armaPsi b (Fin.elim0 : Fin 0 → ℝ) n * ε (t - 1 - (i : ℕ) - (n : ℕ)) ω) 2 μ
          + eLpNorm (fun ω => (∑ j : Fin q, c (.inr j) * V (t - 1 - (j : ℕ)) ω)
              - ∑ j : Fin q, c (.inr j) * ∑ n ∈ Finset.range N,
                  armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ) n
                    * ε (t - 1 - (j : ℕ) - (n : ℕ)) ω) 2 μ := by
      intro N
      have hfun : (fun ω =>
          ((∑ i : Fin p, c (.inl i) * U (t - 1 - (i : ℕ)) ω)
              + ∑ j : Fin q, c (.inr j) * V (t - 1 - (j : ℕ)) ω)
            - ((∑ i : Fin p, c (.inl i) * ∑ n ∈ Finset.range N,
                  armaPsi b (Fin.elim0 : Fin 0 → ℝ) n * ε (t - 1 - (i : ℕ) - (n : ℕ)) ω)
                + ∑ j : Fin q, c (.inr j) * ∑ n ∈ Finset.range N,
                    armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ) n
                      * ε (t - 1 - (j : ℕ) - (n : ℕ)) ω))
          = (fun ω => (∑ i : Fin p, c (.inl i) * U (t - 1 - (i : ℕ)) ω)
                - ∑ i : Fin p, c (.inl i) * ∑ n ∈ Finset.range N,
                    armaPsi b (Fin.elim0 : Fin 0 → ℝ) n * ε (t - 1 - (i : ℕ) - (n : ℕ)) ω)
            + (fun ω => (∑ j : Fin q, c (.inr j) * V (t - 1 - (j : ℕ)) ω)
                - ∑ j : Fin q, c (.inr j) * ∑ n ∈ Finset.range N,
                    armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ) n
                      * ε (t - 1 - (j : ℕ) - (n : ℕ)) ω) := by
        funext ω; simp only [Pi.add_apply]; ring
      rw [hfun]
      refine eLpNorm_add_le ?_ ?_ one_le_two
      · exact ((memLp_finset_sum _ fun i _ => (hUmem _).const_mul _).sub
          (memLp_finset_sum _ fun i _ =>
            (memLp_finset_sum _ fun n _ => (hε.memLp _).const_mul _).const_mul _)).1
      · exact ((memLp_finset_sum _ fun j _ => (hVmem _).const_mul _).sub
          (memLp_finset_sum _ fun j _ =>
            (memLp_finset_sum _ fun n _ => (hε.memLp _).const_mul _).const_mul _)).1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun N => zero_le _) hbd
    simpa using hUconv.add hVconv

end Process

end StatLean.TimeSeries
