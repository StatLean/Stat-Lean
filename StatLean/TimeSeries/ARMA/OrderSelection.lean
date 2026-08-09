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
  -- Both densities are integrable: a non-integrable function has integral `0 ≠ 1`.
  have hfi : Integrable f ν := by
    by_contra h
    rw [integral_undef h] at hf1
    exact zero_ne_one hf1
  have hgi : Integrable g ν := by
    by_contra h
    rw [integral_undef h] at hg1
    exact zero_ne_one hg1
  -- The pointwise comparison `f − g ≤ f log(f/g)`, i.e. `log x ≤ x − 1` at `x = g/f`.
  have hkey : ∀ v, f v - g v ≤ f v * Real.log (f v / g v) := by
    intro v
    rcases eq_or_lt_of_le (hf0 v) with h | h
    · -- `f v = 0`: the integrand vanishes (`0 · log` junk included) and `−g v ≤ 0`.
      rw [← h]
      simp only [zero_sub, zero_mul, neg_nonpos]
      exact hg0 v
    · have hgv : 0 < g v := hsupp v h
      have hlog : Real.log (g v / f v) ≤ g v / f v - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hneg : Real.log (f v / g v) = -Real.log (g v / f v) := by
        rw [← Real.log_inv]
        congr 1
        field_simp
      rw [hneg]
      have h2 : f v * (1 - g v / f v) ≤ f v * (-Real.log (g v / f v)) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt h)
      calc f v - g v = f v * (1 - g v / f v) := by field_simp
        _ ≤ _ := h2
  -- Integrate: `KL ≥ ∫ (f − g) = 1 − 1 = 0`.
  have hcomp : ∫ v, (f v - g v) ∂ν ≤ ∫ v, f v * Real.log (f v / g v) ∂ν :=
    integral_mono (hfi.sub hgi) hint hkey
  rw [integral_sub hfi hgi, hf1, hg1] at hcomp
  simpa [klInfo] using hcomp

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
  have hm' : (p : ℝ) + (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hT' : 2 * ((m : ℝ) + 1) ≤ (T : ℝ) := by exact_mod_cast hT
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hTpos : (0 : ℝ) < (T : ℝ) := by linarith
  -- `p + q + 1 ≤ m + 1 ≤ T/2`, so the AICC denominator is at least `T/2`.
  have hden : (T : ℝ) / 2 ≤ (T : ℝ) - (p : ℝ) - (q : ℝ) - 1 := by linarith
  have hdenpos : (0 : ℝ) < (T : ℝ) - (p : ℝ) - (q : ℝ) - 1 := by linarith
  -- The penalties differ by `2(p+q)(p+q+1)/(T − p − q − 1)`.
  have hdiff : armaAICC b a x - armaAIC b a x
      = 2 * ((p : ℝ) + (q : ℝ)) * (((p : ℝ) + (q : ℝ)) + 1)
        / ((T : ℝ) - (p : ℝ) - (q : ℝ) - 1) := by
    simp only [armaAICC, armaAIC]
    field_simp
    ring
  rw [hdiff, abs_of_nonneg (by positivity)]
  have h1 : 2 * ((p : ℝ) + (q : ℝ)) * (((p : ℝ) + (q : ℝ)) + 1)
      ≤ 2 * ((m : ℝ) + 1) ^ 2 := by nlinarith
  have h2 : 2 * ((p : ℝ) + (q : ℝ)) * (((p : ℝ) + (q : ℝ)) + 1)
        / ((T : ℝ) - (p : ℝ) - (q : ℝ) - 1)
      ≤ 2 * ((m : ℝ) + 1) ^ 2 / ((T : ℝ) / 2) := by
    gcongr
  calc 2 * ((p : ℝ) + (q : ℝ)) * (((p : ℝ) + (q : ℝ)) + 1)
        / ((T : ℝ) - (p : ℝ) - (q : ℝ) - 1)
      ≤ 2 * ((m : ℝ) + 1) ^ 2 / ((T : ℝ) / 2) := h2
    _ = 4 * ((m : ℝ) + 1) ^ 2 / (T : ℝ) := by
        rw [div_div_eq_mul_div]; ring

/-- The order-level BIC **value function**: the infimum of `armaBIC` over parameters
in the constraint set at fixed orders `(p, q)` (junk by the `iInf` convention when
unbounded below). -/
noncomputable def armaBICmin (p q : ℕ) {T : ℕ} (x : Fin T → ℝ) : ℝ :=
  ⨅ ba : {ba : (Fin p → ℝ) × (Fin q → ℝ) // ARMAInvertibleParams ba.1 ba.2},
    armaBIC ba.val.1 ba.val.2 x

/-! ### Assembly of BIC consistency over the grid cells

`P(selection = (p₀,q₀)) → 1` is equivalent to the finitely many wrong cells each having
vanishing probability: `tendsto_sel_of_cells` (**proved**) does the union bound, and the
cells split into the two genuinely different mechanisms — the contrast gap (underfitting)
and the penalty-vs-likelihood-ratio race (overfitting) — recorded as residues (U) and (O).
No measurability of `armaBICmin` is needed anywhere in the assembly, since the cells are
events of the *selection*, which is measurable by hypothesis. -/

section BICAssembly

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private lemma measurableSet_sel {psel qsel : ℕ → Ω → ℕ}
    (hmeassel : ∀ T, Measurable (psel T) ∧ Measurable (qsel T)) (T p q : ℕ) :
    MeasurableSet {ω | psel T ω = p ∧ qsel T ω = q} :=
  ((hmeassel T).1 (measurableSet_singleton p)).inter ((hmeassel T).2 (measurableSet_singleton q))

/-- The order-selection event decomposes over the grid: outside the true cell the
selection lands in one of the finitely many remaining cells. -/
private lemma tendsto_sel_of_cells [IsProbabilityMeasure μ] {P Q p0 q0 : ℕ}
    {psel qsel : ℕ → Ω → ℕ}
    (hmeassel : ∀ T, Measurable (psel T) ∧ Measurable (qsel T))
    (hgrid : ∀ (T : ℕ) (ω : Ω), psel T ω ≤ P ∧ qsel T ω ≤ Q)
    (hcells : ∀ p ≤ P, ∀ q ≤ Q, (p, q) ≠ (p0, q0) →
      Tendsto (fun T : ℕ => (μ {ω | psel T ω = p ∧ qsel T ω = q}).toReal) atTop (𝓝 0)) :
    Tendsto (fun T : ℕ => (μ {ω | psel T ω = p0 ∧ qsel T ω = q0}).toReal) atTop (𝓝 1) := by
  classical
  set S : Finset (ℕ × ℕ) :=
    (Finset.range (P + 1) ×ˢ Finset.range (Q + 1)).erase (p0, q0) with hS
  have hbadmeas : ∀ T : ℕ, MeasurableSet {ω | psel T ω = p0 ∧ qsel T ω = q0}ᶜ :=
    fun T => (measurableSet_sel hmeassel T p0 q0).compl
  -- the complement of the true cell is covered by the remaining grid cells
  have hsub : ∀ T : ℕ, {ω | psel T ω = p0 ∧ qsel T ω = q0}ᶜ ⊆
      ⋃ s ∈ S, {ω | psel T ω = s.1 ∧ qsel T ω = s.2} := by
    intro T ω hω
    have hgw := hgrid T ω
    have hmem : (psel T ω, qsel T ω) ∈ S := by
      rw [hS, Finset.mem_erase]
      refine ⟨fun hc => hω ⟨?_, ?_⟩,
        Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩⟩
      · exact congrArg Prod.fst hc
      · exact congrArg Prod.snd hc
    exact Set.mem_biUnion hmem (Set.mem_setOf.2 ⟨rfl, rfl⟩)
  -- Markov/subadditivity bound on the bad event
  have hbound : ∀ T : ℕ, (μ {ω | psel T ω = p0 ∧ qsel T ω = q0}ᶜ).toReal
      ≤ ∑ s ∈ S, (μ {ω | psel T ω = s.1 ∧ qsel T ω = s.2}).toReal := by
    intro T
    have h1 : μ {ω | psel T ω = p0 ∧ qsel T ω = q0}ᶜ
        ≤ ∑ s ∈ S, μ {ω | psel T ω = s.1 ∧ qsel T ω = s.2} :=
      le_trans (measure_mono (hsub T)) (measure_biUnion_finset_le _ _)
    have h2 : (∑ s ∈ S, μ {ω | psel T ω = s.1 ∧ qsel T ω = s.2}).toReal
        = ∑ s ∈ S, (μ {ω | psel T ω = s.1 ∧ qsel T ω = s.2}).toReal :=
      ENNReal.toReal_sum fun s _ => measure_ne_top _ _
    rw [← h2]
    refine ENNReal.toReal_mono ?_ h1
    exact ENNReal.sum_ne_top.2 fun s _ => measure_ne_top _ _
  -- each cell dies, so the finite sum does
  have hsum : Tendsto (fun T : ℕ =>
      ∑ s ∈ S, (μ {ω | psel T ω = s.1 ∧ qsel T ω = s.2}).toReal) atTop (𝓝 0) := by
    have hstep : ∀ s ∈ S, Tendsto
        (fun T : ℕ => (μ {ω | psel T ω = s.1 ∧ qsel T ω = s.2}).toReal) atTop (𝓝 0) := by
      intro s hs
      rw [hS, Finset.mem_erase, Finset.mem_product] at hs
      exact hcells s.1 (by have := hs.2.1; simp only [Finset.mem_range] at this; omega)
        s.2 (by have := hs.2.2; simp only [Finset.mem_range] at this; omega)
        (by simpa using hs.1)
    simpa using tendsto_finset_sum (x := atTop) S hstep
  have hbad : Tendsto (fun T : ℕ => (μ {ω | psel T ω = p0 ∧ qsel T ω = q0}ᶜ).toReal)
      atTop (𝓝 0) :=
    squeeze_zero (fun T => ENNReal.toReal_nonneg) hbound hsum
  have heq : ∀ T : ℕ, (μ {ω | psel T ω = p0 ∧ qsel T ω = q0}).toReal
      = 1 - (μ {ω | psel T ω = p0 ∧ qsel T ω = q0}ᶜ).toReal := by
    intro T
    rw [prob_compl_eq_one_sub (measurableSet_sel hmeassel T p0 q0),
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
    simp
  simp only [heq]
  simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub hbad


/-- **RESIDUE (U) — the underfitting cells** `p < p₀` or `q < q₀`.

**Mechanism.** On `{psel = p, qsel = q}` the selection hypothesis gives
`BICmin(p,q) ≤ BICmin(p₀,q₀) ≤ armaBIC b₀ a₀ x = T·ℓ*(b₀,a₀) + (p₀+q₀) log T`
(the truth is admissible by `hB`), while
`BICmin(p,q) ≥ T·(inf_{𝓑_{p,q}} ℓ*) + (p+q) log T`. So the cell dies as soon as
`inf_{(b,a) ∈ 𝓑_{p,q}} [ℓ*(b,a,x) − ℓ*(b₀,a₀,x)] ≥ γ > 0` with probability `→ 1`, the
penalty difference being `O(log T) = o(T)`.

**What is missing, precisely.** The infimum in `armaBICmin` runs over the **whole open**
region `𝓑_{p,q}`, up to its boundary. `Consistency.exists_contrast_gap` delivers exactly
this gap — but only on a **compact** `K ⊆ 𝓑`, which is all `mle_consistent` needs and
strictly less than what the frozen `iInf` asks for; the boundary regime (roots
approaching the unit circle) is uncontrolled. That, not the contrast gap itself, is the
content of (U).

**Well-posedness caveat.** `armaBICmin` is a real `iInf`: on a sample where `armaBIC` is
unbounded below on `𝓑_{p,q}` it takes the junk value `0` and `hminsel` becomes vacuous at
that `ω`. This is not hypothetical — for constant data `x ≡ c ≠ 0` and the AR(1) family,
`det Γ_T = (1−φ²)^{-1}` and `S = (1−φ²)c² + (T−1)(1−φ)²c²`, so
`armaBIC = T log(S/T) + log det Γ_T + pen ∼ (T−1) log(1−φ) → −∞` as `φ → 1⁻` for `T ≥ 2`.
Under the model this is a null event, but any proof has to discard it explicitly.

**Scope.** `ARMA/Consistency.lean` is **not** in this file's import closure
(`OrderSelection` imports only `ARMA/Likelihood`), and `exists_contrast_gap`,
`armaContrastVar` and `criterion_tendsto_contrast` are `private` or unreachable here. So
(U) cannot even be *stated* in contrast-variance terms without an import edge plus an
un-`private`ing.

**STATUS after wave `ts/s12b-model-repairs` (2026-08-09): NOT attempted, and the
obstruction is now named precisely.** The wave brief's instruction — "generalize
`exists_contrast_gap` to the open-region form" — is not a generalization of that lemma's
*proof*: that proof is `continuousOn_armaContrastVar` + `IsCompact.exists_isMinOn` on
`K ∩ {dist ≥ δ}`, and the region `𝓑_{p,q}` fails compactness **twice over**, in two
genuinely different ways:

* it is **unbounded** — the coefficient vector may escape to infinity inside `𝓑`;
* it is **not closed** — the escape to its boundary is roots of `b` or `a` approaching the
  unit circle, where `armaContrastVar` is not even defined (the geometric brick
  `exists_uniform_geometric_bound_arma`, on which every bound in the file rests, degenerates
  there: its `r ↑ 1`).

Un-`private`ing changes nothing about either. What is missing is a **lower** bound for
`armaContrastVar b₀ a₀ b a` along both escapes; the project supplies only
`one_le_armaContrastVar`, i.e. the bound `1`, and `1` is exactly the value the gap has to
beat. A spectral (Parseval) representation of `armaContrastVar` — absent from the project —
is the natural source of such a bound, since it exhibits the contrast as
`(2π)⁻¹∫|b(e^{iλ})a₀(e^{iλ})/(a(e^{iλ})b₀(e^{iλ}))|²dλ`, which blows up along both escapes.
Recorded as the honest shape of (U) rather than closed. -/
private theorem bic_underfit_residue [IsProbabilityMeasure μ] {p0 q0 : ℕ}
    {b0 : Fin p0 → ℝ} {a0 : Fin q0 → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB : ARMAInvertibleParams b0 a0)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {P Q : ℕ} (hpP : p0 ≤ P) (hqQ : q0 ≤ Q)
    (psel qsel : ℕ → Ω → ℕ)
    (hmeassel : ∀ T, Measurable (psel T) ∧ Measurable (qsel T))
    (hminsel : ∀ (T : ℕ) (ω : Ω), psel T ω ≤ P ∧ qsel T ω ≤ Q ∧
      ∀ p ≤ P, ∀ q ≤ Q,
        armaBICmin (psel T ω) (qsel T ω) (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          ≤ armaBICmin p q (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
    (p q : ℕ) (hp : p ≤ P) (hq : q ≤ Q) (hunder : p < p0 ∨ q < q0) :
    Tendsto (fun T : ℕ => (μ {ω | psel T ω = p ∧ qsel T ω = q}).toReal) atTop (𝓝 0) := by
  sorry

/-- **RESIDUE (O) — the overfitting cells** `p₀ ≤ p`, `q₀ ≤ q`, `(p,q) ≠ (p₀,q₀)`.

**Mechanism.** Here the contrast gap is *zero* — the larger model contains the truth — so
the whole margin is the penalty: the cell dies iff
`T·(ℓ*_min(p₀,q₀) − ℓ*_min(p,q)) < (p+q−p₀−q₀)·log T` with probability `→ 1`, i.e. iff the
profiled likelihood-ratio statistic is `O_p(1)`.

**What is missing, precisely.** `O_p(1)`-tightness of the likelihood ratio is a
*second-order* statement: it is the quadratic expansion of `ℓ*` around `θ₀`, i.e. the
score CLT together with the Hessian ULLN — exactly the content that
`MLEAsymptotics.armaMLE_linearization` leaves open (its own status note names the two
inputs). Consistency (`mle_consistent`, PROVED) is strictly weaker and cannot see this
scale. On top of that, the infimum is again over the open `𝓑_{p,q}`, so the boundary
control demanded by residue (U) is needed here too.

Note this is where the frozen statement's `in probability` reading matters: an a.s.
version would additionally need a summability/Borel-Cantelli upgrade of the same
expansion, which nothing in the project supplies.

**STATUS after wave `ts/s12b-model-repairs` (2026-08-09): NOT attempted; the brief's
"close BIC modulo `armaMLE_linearization` by citing it" is not available as stated**, for
two reasons that are visible in the two statements side by side:

* `armaMLE_linearization` consumes a *given measurable estimator sequence*
  `θ : (T : ℕ) → Ω → (Fin p → ℝ) × (Fin q → ℝ)` together with `hargmin`. `armaBICmin` is an
  `iInf` — a number, not a selection. Producing the `θ` the linearization needs is a
  **measurable-selection** step over the parameter region, which the frozen note does not
  mention and which nothing in the project supplies;
* the linearization's `hargmin` minimizes over a **compact** `K` with `θ₀ ∈ interior K`,
  while the BIC infimum is over the whole open `𝓑_{p,q}`. So even granted a selection, the
  two do not match without exactly the boundary control that residue (U) is missing.

The headline `bic_consistency_debt` is unaffected: it is proved over (U) and (O), so the
grid union bound and the cell decomposition are not part of this residue. -/
private theorem bic_overfit_residue [IsProbabilityMeasure μ] {p0 q0 : ℕ}
    {b0 : Fin p0 → ℝ} {a0 : Fin q0 → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB : ARMAInvertibleParams b0 a0)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {P Q : ℕ} (hpP : p0 ≤ P) (hqQ : q0 ≤ Q)
    (psel qsel : ℕ → Ω → ℕ)
    (hmeassel : ∀ T, Measurable (psel T) ∧ Measurable (qsel T))
    (hminsel : ∀ (T : ℕ) (ω : Ω), psel T ω ≤ P ∧ qsel T ω ≤ Q ∧
      ∀ p ≤ P, ∀ q ≤ Q,
        armaBICmin (psel T ω) (qsel T ω) (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          ≤ armaBICmin p q (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
    (p q : ℕ) (hp : p ≤ P) (hq : q ≤ Q) (hover : p0 ≤ p) (hover' : q0 ≤ q)
    (hne : (p, q) ≠ (p0, q0)) :
    Tendsto (fun T : ℕ => (μ {ω | psel T ω = p ∧ qsel T ω = q}).toReal) atTop (𝓝 0) := by
  sorry

end BICAssembly

/-- **DEBT (Hannan 1980; FY §3.4.3)**: BIC order-selection consistency. If the data
are a stationary causal invertible ARMA(p₀, q₀) with iid noise, any measurable
selection minimizing the BIC value function over a fixed grid containing `(p₀, q₀)`
picks the true orders with probability tending to one.

**STATUS after wave `ts/s12-model-selection` (2026-08-09).** PROVED over the two named
residues `bic_underfit_residue` (U) and `bic_overfit_residue` (O) above; the grid union
bound (`tendsto_sel_of_cells`) is proved and needs no measurability of `armaBICmin`.
Three findings recorded at the residues:

* the wave brief's expectation that underfitting "is killed by the contrast gap
  (`exists_contrast_gap`, PROVED)" is **overturned twice over**: that lemma gives the gap
  only on a **compact** `K ⊆ 𝓑`, whereas `armaBICmin` is an `iInf` over the whole *open*
  `𝓑_{p,q}` up to its boundary; and it is `private` to `ARMA/Consistency.lean`, which is
  not in this file's import closure at all;
* overfitting is not "only the criterion LLN plus a quadratic bound": it is `O_p(1)`
  tightness of the profiled likelihood ratio, i.e. precisely the second-order expansion
  left open at `MLEAsymptotics.armaMLE_linearization`;
* `armaBICmin` is a real `iInf` and *is* `−∞`-junk (hence `0`, making `hminsel` vacuous)
  on some samples — explicitly, constant data in the AR(1) family. Null under the model,
  but it has to be discarded by hand. -/
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
  refine tendsto_sel_of_cells hmeassel
    (fun T ω => ⟨(hminsel T ω).1, (hminsel T ω).2.1⟩) ?_
  intro p hpP q hqQ hne
  rcases lt_or_ge p p0 with hlt | hge
  · exact bic_underfit_residue h hiid hσ hB hcausal hmeas hp hq psel qsel hmeassel hminsel
      p q hpP hqQ (Or.inl hlt)
  · rcases lt_or_ge q q0 with hlt' | hge'
    · exact bic_underfit_residue h hiid hσ hB hcausal hmeas hp hq psel qsel hmeassel hminsel
        p q hpP hqQ (Or.inr hlt')
    · exact bic_overfit_residue h hiid hσ hB hcausal hmeas hp hq psel qsel hmeassel hminsel
        p q hpP hqQ hge hge' hne

end StatLean.TimeSeries
