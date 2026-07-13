import StatLean.Bayesian.DirichletLaplace.ShellDecomposition
import StatLean.Bayesian.DirichletLaplace.PriorMassRatio
import StatLean.Bayesian.DirichletLaplace.Theorem34
import StatLean.Bayesian.DirichletLaplace.DenominatorLowerBound
import StatLean.Bayesian.DirichletLaplace.TestingBound
import StatLean.Bayesian.ForMathlib.ExpOfRealCalc
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dirichlet–Laplace posterior contraction — BPPD Theorem 3.1 (C16)

Assembly of BPPD **Theorem 3.1**: in the normal-means model `y = θ + ε`, `ε ~ N(0, Iₙ)`, under the
Dirichlet–Laplace prior with scale `aₙ = n^{−(1+β)}` and the growth condition `‖θ₀‖² ≤ qₙ log⁴n`, the
posterior mass of `{ ‖θ − θ₀‖ > M√(qₙ log n) }` tends to `0` in `E_{θ₀}`.

Objects:
* `dl_contraction_engine` — the fixed-`n` bound assembled from three vanishing pieces: the Theorem 3.4
  compressibility term at `δ = r/n` (`Theorem34`), the denominator event `K θ₀{D < dbar} ≤ e^{−r²/8}`
  with `dbar := e^{−r²}·Π(B(θ₀,r))` (`DenominatorLowerBound.measure_dlDenom_lt_le` — note `dbar` needs
  no *absolute* lower bound; it cancels into the ratio below, see `PriorMassRatio` D10), and the summed
  shell/net bound (`ShellDecomposition` per shell, `PriorMassRatio.dlBetaRatio_le` per piece: each shell
  term `Π(shell)·e^{−j²r²/12}/dbar = [Π(shell)/Π(B(θ₀,r))]·e^{−j²r²/12}·e^{r²}` has `Π(B(θ₀,r))` cancel).
* `dl_theorem31` — the headline (rate `M√(qₙ log n)`, deviation D1). **Proven, modulo the one TRUE
  outer-series limit `dl_shellSum_tendsto_zero_beta`** (the term-(iii) shell double-series `→ 0`; its
  hard structural reduction is developed on branch `bay/dl-thm31-shellsum`).
* `dl_theorem31_ball` — the equivalent `𝓝 1` form (BPPD eq. (12)). Proven (reduces to `dl_theorem31`).
* `dl_theorem31_paper_rate` — under `qₙ ≤ n^{1−c}`, the paper's minimax rate `sₙ = √(qₙ log(n/qₙ))`.
  Proven (reduces to `dl_theorem31`).
* `dl_theorem31_recip` — the `aₙ = 1/n` companion. **DOCUMENTED OPEN CASE (D13, two-scale obstruction)** —
  not provable by the single-radius engine; see its proof body.

**Status (2 sorries).** The β-regime (main result) is proven modulo the single TRUE closable limit
`dl_shellSum_tendsto_zero_beta`; the `1/n`-regime `dl_theorem31_recip` is a documented open case (D13).
No false lemma underpins any headline (`#print axioms` on `dl_theorem31` shows exactly the beta-limit
`sorryAx`, on `dl_theorem34_beta` is clean).

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*,
JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Theorem 3.1 (statement p. 7, proof §6 pp. 14–16 with
Lemma 6.1); the §6 posterior-contraction assembly.

**Proof formalization notes.** The skeleton is *3.4-term + denominator event + Σ-shells*: split the
complement of the ball into radial shells (`ShellDecomposition`), cover each by a net and test it,
weight the Type II errors by the piece prior-mass ratio (`PriorMassRatio.dlBetaRatio_le`), and sum.
The outer support-pattern sum is `|{ |S| ≤ A'q }| ≤ (A'q+1)·n^{A'q}` via `Nat.choose_le_pow`
(`Mathlib.Data.Nat.Choose.Bounds`); the radial series `Σ_{j ≥ M} (1+β)e^{−j²r²/12} → 0` via
`ExpOfRealCalc` (`tsum_ofReal_exp_neg_sq_le`, `tendsto_ofReal_exp_neg`). The asymptotics live only in
the thin corollaries.

**Deviations.**
* **D1 (rate).** The paper states `sₙ² = qₙ log(n/qₙ)` but its proof fixes `rₙ² = qₙ log n` (p. 15) and
  only yields that. The headline `dl_theorem31` therefore states the rate `√(qₙ log n)`; the paper's
  `sₙ` is recovered as `dl_theorem31_paper_rate` under `qₙ ≤ n^{1−c}` (where `log(n/qₙ) ≍ log n`).
* **D2 (regime-dependent `r`).** `β`-regime uses `r² = qₙ log n`. The plan's original claim that the
  `1/n`-regime uses a single `r² = qₙ` is **wrong** — see D13.
* **D4 (net / test geometry).** Inherited from `ShellDecomposition`: `jr/4`-nets (`≤ 33^{|S|}`),
  pieces of radius `≤ (√5/4)jr`, two-parameter midpoint tests with errors `≤ e^{−j²r²/12}`.
* **D13 (`1/n` two-scale obstruction; `dl_theorem31_recip` open).** The `aₙ = 1/n` regime cannot use one
  radius: the compress (3.4) term needs `r² = qₙ` (small, with constant Chernoff `c` and `qₙ ≥ C₀ log n`),
  while the shell double-series needs `r² = qₙ log n` (large — with `r² = qₙ` the Type-I net count
  `exp(Aqₙ·log 33n − J₀²qₙ/12) → +∞` for fixed `J₀`). The intermediate lemma asserting the shell series
  `→ 0` at `r² = qₙ` was therefore **false** and is removed; `dl_theorem31_recip` is left as a documented
  open case pending a two-scale peeling sieve (BPPD §6). The β-regime and `dl_theorem34_recip` are proven.

**Bibliographic comments.** Posterior contraction rates after Ghosal, Ghosh, and van der Vaart
(*Ann. Statist.* 28 (2000), 500–531); sparse-normal-means Bayesian contraction after Castillo and van
der Vaart (*Ann. Statist.* 40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

/-- **The denominator threshold** `dbar := e^{−r²}·Π(B(θ₀,r))` used throughout the engine. Below it,
the ratio is controlled by the denominator event (`measure_dlDenom_lt_le`); above it, each shell ratio
is bounded by `shell_ratio_le` (whose `Π(B(θ₀,r))` cancels into the mass ratio). -/
private noncomputable def dbarVal {ι : Type*} [Fintype ι] (a r : ℝ) (θ₀ : EuclideanSpace ℝ ι) :
    ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(r ^ 2))) * (dlPrior a ι) (Metric.closedBall θ₀ r)

/-- `WithLp.toLp 2` as a measurable function (with the plain-function head, for `rw` into
`Measure.map_apply` — the `MeasurableEquiv` coercion does not match syntactically). -/
private lemma measurable_toLp {ι : Type*} [Fintype ι] :
    Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
  (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable

/-- The `δ`-support level set `{θ | (univ.filter (δ < |θ i|)) = S}` is measurable (a finite
intersection of measurable coordinate events). -/
private lemma measurableSet_dlSupp_eq {ι : Type*} [Fintype ι] (δ : ℝ) (S : Finset ι) :
    MeasurableSet {θ : EuclideanSpace ℝ ι | (Finset.univ.filter fun i => δ < |θ i|) = S} := by
  classical
  have hpre : {θ : EuclideanSpace ℝ ι | (Finset.univ.filter fun i => δ < |θ i|) = S}
      = ⋂ i : ι, (if i ∈ S then {θ : EuclideanSpace ℝ ι | δ < |θ i|}
          else {θ : EuclideanSpace ℝ ι | ¬ δ < |θ i|}) := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hS i
      by_cases hi : i ∈ S
      · simp only [hi, if_true, Set.mem_setOf_eq]
        have : i ∈ Finset.univ.filter fun i => δ < |θ i| := by rw [hS]; exact hi
        simpa [Finset.mem_filter] using this
      · simp only [hi, if_false, Set.mem_setOf_eq]
        intro hlt
        have : i ∈ Finset.univ.filter fun i => δ < |θ i| := by
          simp [Finset.mem_filter, hlt]
        rw [hS] at this; exact hi this
    · intro h
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hi := h i
      by_cases hiS : i ∈ S
      · simp only [hiS, if_true, Set.mem_setOf_eq] at hi
        simp [hiS, hi]
      · simp only [hiS, if_false, Set.mem_setOf_eq] at hi
        simp [hiS, hi]
  rw [hpre]
  refine MeasurableSet.iInter fun i => ?_
  have hmi : Measurable (fun θ : EuclideanSpace ℝ ι => |θ i|) :=
    ((measurable_pi_apply i).comp (EuclideanSpace.measurableEquiv ι).measurable).abs
  by_cases hi : i ∈ S
  · simp only [hi, if_true]; exact measurableSet_lt measurable_const hmi
  · simp only [hi, if_false]
    exact (measurableSet_lt measurable_const hmi).compl

/-- The shell `dlShell θ₀ S j r δ` is measurable. -/
private lemma measurableSet_dlShell {ι : Type*} [Fintype ι] (θ₀ : EuclideanSpace ℝ ι)
    (S : Finset ι) (j : ℕ) (r δ : ℝ) : MeasurableSet (dlShell θ₀ S j r δ) := by
  have hnorm : Measurable (fun θ : EuclideanSpace ℝ ι => ‖θ - θ₀‖) :=
    (continuous_id.sub continuous_const).norm.measurable
  refine (measurableSet_dlSupp_eq δ S).inter (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_le measurable_const hnorm
  · exact measurableSet_lt hnorm measurable_const

/-- **Fixed-`n` contraction bound** (BPPD Thm 3.1 engine, honest restatement). For a truth `θ₀`
supported on `S₀`, the `E_{θ₀}`-mean of the posterior mass of `{ ‖θ − θ₀‖ > M·r }` is bounded by three
pieces: the denominator event `e^{−r²/8}`, the Theorem 3.4 compressibility term (`compress_ratio_le_explicit`
on the `S₀ᶜ`-submodel), and the **honest shell double series** — over support patterns `S` (`|S| ≤ K`)
and radial shells `j ≥ J₀` — each term being exactly the `shell_ratio_le` bound
`33^{|S|}·e^{−j²r²/12} + Π(shell)·e^{−j²r²/12}/dbar`.

**Honest restatement (D12).** The previous RHS `… − (A−1)q log c + 3r² … + 2·e^{−M²r²/12}` is provably
false: the `3r²` folds the small-ball correction `2·card'·w` (false as `card' → ∞`), and the closed
`2·e^{−M²r²/12}` drops the net cardinality `33^{|S|}` and the mass ratio, which only vanish
asymptotically. The sum form below is the guaranteed-honest bound the closed bricks actually produce. -/
theorem dl_contraction_engine {ι : Type*} [Fintype ι] {a δ r : ℝ}
    -- LEAN-ONLY: 0 < a ≤ 1/2 — DL scale range (both density bounds); engine-internal.
    (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    -- LEAN-ONLY: δ-threshold window (dlBetaRatio / small-ball) and net radius control; engine-internal.
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδnet : Real.sqrt (Fintype.card ι : ℝ) * δ ≤ r)
    -- LEAN-ONLY: 0 < r — contraction radius (rₙ); engine-internal.
    (hr : 0 < r) (θ₀ : EuclideanSpace ℝ ι) (S₀ : Finset ι)
    -- LEAN-ONLY: θ₀ supported on S₀; engine-internal.
    (hθ₀ : ∀ i ∉ S₀, θ₀ i = 0)
    -- LEAN-ONLY: prior gives positive mass to the contraction ball (full support); engine-internal.
    (hBpos : 0 < (dlPrior a ι) (Metric.closedBall θ₀ r))
    -- LEAN-ONLY: 0 < M — contraction multiplier; engine-internal.
    (M : ℝ) (hM : 0 < M)
    -- LEAN-ONLY: support-count threshold K and radial floor J₀ = ⌈M/2⌉ ≥ 2; engine-internal.
    (K J₀ : ℕ) (hJ2 : 2 ≤ J₀) (hJ₀ : (J₀ : ℝ) ≤ M / 2)
    -- LEAN-ONLY: Chernoff cut `k` for the compress event `{K < |supp_δ|}`; engine-internal.
    (k : ℕ) (hk : (S₀.card : ℝ) + (k : ℝ) ≤ (K : ℝ))
    -- LEAN-ONLY: C3 δ-exceedance bound `z` and small-ball tail bound `w` (submodel); engine-internal.
    (z : ℝ) (hz : (dlMarginal a {x : ℝ | δ < |x|}).toReal ≤ z)
    (w : ℝ)
    (hw : (dlMarginal a
        {x : ℝ | min (r / Real.sqrt (Fintype.card {i : ι // i ∉ S₀} : ℝ)) (1 / 2) < |x|}).toReal ≤ w)
    (hw2 : w ≤ 1 / 2)
    -- LEAN-ONLY: 1 < c — Chernoff parameter; engine-internal.
    (c : ℝ) (hc : 1 < c) :
    ∫⁻ y, ((gaussShiftKernel ι)†(dlPrior a ι)) y {θ | M * r < ‖θ - θ₀‖}
          ∂(gaussShiftKernel ι θ₀)
      ≤ ENNReal.ofReal (Real.exp (- r ^ 2 / 8))
          + (ENNReal.ofReal (Real.exp ((Fintype.card {i : ι // i ∉ S₀} : ℝ) * z * (c - 1)
                - (k : ℝ) * Real.log c + r ^ 2 + 2 * (Fintype.card {i : ι // i ∉ S₀} : ℝ) * w))
              + ENNReal.ofReal (Real.exp (- r ^ 2 / 8)))
          + ∑ S ∈ (Finset.univ : Finset ι).powerset.filter (fun S => S.card ≤ K),
              ∑' j : ℕ, (if J₀ ≤ j then
                (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12))
                + (dlPrior a ι) (dlShell θ₀ S j r δ)
                    * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12)) / dbarVal a r θ₀
                else 0) := by
  classical
  set π : Measure (EuclideanSpace ℝ ι) := dlPrior a ι with hπ
  set μ := gaussShiftKernel ι θ₀ with hμ
  set C : Set (EuclideanSpace ℝ ι) := {θ | M * r < ‖θ - θ₀‖} with hCdef
  set Cbad : Set (EuclideanSpace ℝ ι) := {θ | (K : ℝ) < (dlSuppCount δ θ : ℝ)} with hCbaddef
  set 𝒮 := (Finset.univ : Finset ι).powerset.filter (fun S => S.card ≤ K) with h𝒮def
  set dbar : ℝ≥0∞ := dbarVal a r θ₀ with hdbardef
  set U : Set (EuclideanSpace ℝ ι) := ⋃ S ∈ 𝒮, ⋃ (j : ℕ), ⋃ (_ : J₀ ≤ j), dlShell θ₀ S j r δ
    with hUdef
  set G : Set (EuclideanSpace ℝ ι) := {y | dbar ≤ dlDenom θ₀ π y} with hGdef
  -- Basic facts.
  have hdbarpos : 0 < dbar := by
    rw [hdbardef, dbarVal]
    exact ENNReal.mul_pos (by simp [Real.exp_pos]) (ne_of_gt hBpos)
  have hCmeas : MeasurableSet C := by
    rw [hCdef]
    exact measurableSet_lt measurable_const ((continuous_id.sub continuous_const).norm.measurable)
  have hcast : Measurable (fun θ : EuclideanSpace ℝ ι => ((dlSuppCount δ θ : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_dlSuppCount δ)
  have hCbadmeas : MeasurableSet Cbad := by
    rw [hCbaddef]; exact measurableSet_lt measurable_const hcast
  have hGmeas : MeasurableSet G := by
    rw [hGdef]; exact measurableSet_le measurable_const (measurable_dlDenom θ₀ π)
  have hUmeas : MeasurableSet U := by
    rw [hUdef]
    refine MeasurableSet.biUnion (Finset.countable_toSet 𝒮) fun S _ => ?_
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => measurableSet_dlShell θ₀ S j r δ
  -- `dlNumer` as the `withDensity` measure of the parameter set (for subadditivity).
  have hν_eq : ∀ (y : EuclideanSpace ℝ ι) {D : Set (EuclideanSpace ℝ ι)}, MeasurableSet D →
      dlNumer θ₀ π D y = (π.withDensity (fun θ => dlLR θ₀ θ y)) D := by
    intro y D hD; rw [dlNumer, ← withDensity_apply _ hD]
  -- The geometric decomposition `C ⊆ Cbad ∪ U`.
  have hdecomp : C ⊆ Cbad ∪ U := by
    intro θ hθ
    rw [hCdef, Set.mem_setOf_eq] at hθ
    by_cases hbad : θ ∈ Cbad
    · exact Or.inl hbad
    · refine Or.inr ?_
      rw [hCbaddef, Set.mem_setOf_eq, not_lt] at hbad
      set S := Finset.univ.filter fun i => δ < |θ i| with hSdef
      have hScard : S.card ≤ K := by
        have : (dlSuppCount δ θ : ℝ) ≤ (K : ℝ) := hbad
        have hle : dlSuppCount δ θ ≤ K := by exact_mod_cast this
        rwa [dlSuppCount, ← hSdef] at hle
      have hSmem : S ∈ 𝒮 := by
        rw [h𝒮def, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.subset_univ _, hScard⟩
      have hd : 0 < ‖θ - θ₀‖ := lt_trans (by positivity) hθ
      set j := ⌊‖θ - θ₀‖ / (2 * r)⌋₊ with hjdef
      have hr2 : 0 < 2 * r := by linarith
      have hjle : (j : ℝ) ≤ ‖θ - θ₀‖ / (2 * r) := Nat.floor_le (by positivity)
      have hltj : ‖θ - θ₀‖ / (2 * r) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
      have hJ0j : J₀ ≤ j := by
        rw [hjdef]
        apply Nat.le_floor
        rw [le_div_iff₀ hr2]
        have : (J₀ : ℝ) ≤ M / 2 := hJ₀
        nlinarith [hθ, hM, hr]
      rw [hUdef, Set.mem_iUnion₂]
      refine ⟨S, hSmem, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨j, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨hJ0j, ?_⟩
      rw [dlShell, Set.mem_setOf_eq]
      refine ⟨hSdef.symm, ?_, ?_⟩
      · calc 2 * (j : ℝ) * r = (j : ℝ) * (2 * r) := by ring
          _ ≤ (‖θ - θ₀‖ / (2 * r)) * (2 * r) := by
              apply mul_le_mul_of_nonneg_right hjle (by positivity)
          _ = ‖θ - θ₀‖ := by field_simp
      · calc ‖θ - θ₀‖ = (‖θ - θ₀‖ / (2 * r)) * (2 * r) := by field_simp
          _ < ((j : ℝ) + 1) * (2 * r) := by apply mul_lt_mul_of_pos_right hltj hr2
          _ = 2 * ((j : ℝ) + 1) * r := by ring
  -- Bridge to the ratio, then split the integral at the denominator threshold `G`.
  rw [lintegral_posterior_eq_lintegral_ratio θ₀ π hCmeas]
  rw [← lintegral_add_compl (μ := μ) (f := fun y => dlNumer θ₀ π C y / dlDenom θ₀ π y) hGmeas]
  -- The complement `Gᶜ` is the denominator event.
  have hGc : Gᶜ = {y | dlDenom θ₀ π y
      < ENNReal.ofReal (Real.exp (-(r ^ 2))) * π (Metric.closedBall θ₀ r)} := by
    rw [hGdef]; ext y
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, hdbardef, dbarVal, hπ]
  -- Term (i): the denominator event.
  have hi : ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
      ≤ ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
    calc ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
        ≤ ∫⁻ _ in Gᶜ, 1 ∂μ := by
          refine setLIntegral_mono (measurable_const) fun y _ => ?_
          exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact dlNumer_le_dlDenom θ₀ π C y)
      _ = μ Gᶜ := by rw [setLIntegral_one]
      _ ≤ ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
          rw [hGc, hμ, show (- r ^ 2 / 8 : ℝ) = -(r ^ 2 / 8) by ring]
          exact measure_dlDenom_lt_le π θ₀ hr
  -- Term over `G`: split numerator `C ⊆ Cbad ∪ U`.
  have hnumer_le : ∀ y, dlNumer θ₀ π C y ≤ dlNumer θ₀ π Cbad y + dlNumer θ₀ π U y := by
    intro y
    calc dlNumer θ₀ π C y ≤ dlNumer θ₀ π (Cbad ∪ U) y := dlNumer_mono θ₀ π hdecomp y
      _ = (π.withDensity (fun θ => dlLR θ₀ θ y)) (Cbad ∪ U) := hν_eq y (hCbadmeas.union hUmeas)
      _ ≤ (π.withDensity (fun θ => dlLR θ₀ θ y)) Cbad
            + (π.withDensity (fun θ => dlLR θ₀ θ y)) U := measure_union_le _ _
      _ = dlNumer θ₀ π Cbad y + dlNumer θ₀ π U y := by
          rw [hν_eq y hCbadmeas, hν_eq y hUmeas]
  have hGsplit : ∫⁻ y in G, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
      ≤ ∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
        + ∫⁻ y in G, dlNumer θ₀ π U y / dlDenom θ₀ π y ∂μ := by
    rw [← lintegral_add_left ((measurable_dlNumer θ₀ π Cbad).div (measurable_dlDenom θ₀ π))]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.add_div]
    exact ENNReal.div_le_div_right (hnumer_le y) _
  -- Term (ii): the compressibility bound.
  have hii : ∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
      ≤ ENNReal.ofReal (Real.exp ((Fintype.card {i : ι // i ∉ S₀} : ℝ) * z * (c - 1)
            - (k : ℝ) * Real.log c + r ^ 2 + 2 * (Fintype.card {i : ι // i ∉ S₀} : ℝ) * w))
          + ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
    calc ∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
        ≤ ∫⁻ y, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ y, ((gaussShiftKernel ι)†π) y Cbad ∂μ := by
          rw [hμ, lintegral_posterior_eq_lintegral_ratio θ₀ π hCbadmeas]
      _ ≤ ∫⁻ y, ((gaussShiftKernel ι)†π) y
              {θ | ((S₀.card : ℝ) + (k : ℝ)) < (dlSuppCount δ θ : ℝ)} ∂μ := by
          rw [hμ]
          refine lintegral_mono fun y => measure_mono fun θ hθ => ?_
          rw [hCbaddef, Set.mem_setOf_eq] at hθ
          rw [Set.mem_setOf_eq]; linarith [hk, hθ]
      _ ≤ _ := (dl_compress_reduction ha θ₀ S₀ hθ₀ k).trans
          (compress_ratio_le_explicit ha hr k z hz w hw hw2 c hc)
  -- Term (iii): the shell double series.
  have hiii : ∫⁻ y in G, dlNumer θ₀ π U y / dlDenom θ₀ π y ∂μ
      ≤ ∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then
          (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12))
          + π (dlShell θ₀ S j r δ)
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12)) / dbar else 0) := by
    -- Pointwise: `numer U / denom ≤ ∑_S ∑'_j (if J₀≤j then numer(shell)/denom else 0)`.
    have hUsub : ∀ y, dlNumer θ₀ π U y / dlDenom θ₀ π y
        ≤ ∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then
            dlNumer θ₀ π (dlShell θ₀ S j r δ) y / dlDenom θ₀ π y else 0) := by
      intro y
      have hUmass : dlNumer θ₀ π U y
          ≤ ∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then dlNumer θ₀ π (dlShell θ₀ S j r δ) y else 0) := by
        rw [hν_eq y hUmeas, hUdef]
        refine le_trans (measure_biUnion_finset_le 𝒮 _) (Finset.sum_le_sum fun S _ => ?_)
        refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun j => ?_)
        by_cases hj : J₀ ≤ j
        · rw [if_pos hj]
          have : (⋃ (_ : J₀ ≤ j), dlShell θ₀ S j r δ) = dlShell θ₀ S j r δ := by simp [hj]
          rw [this, ← hν_eq y (measurableSet_dlShell θ₀ S j r δ)]
        · rw [if_neg hj]
          have : (⋃ (_ : J₀ ≤ j), dlShell θ₀ S j r δ) = ∅ := by simp [hj]
          rw [this, measure_empty]
      calc dlNumer θ₀ π U y / dlDenom θ₀ π y
          ≤ (∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then dlNumer θ₀ π (dlShell θ₀ S j r δ) y else 0))
              / dlDenom θ₀ π y := ENNReal.div_le_div_right hUmass _
        _ = ∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then
              dlNumer θ₀ π (dlShell θ₀ S j r δ) y / dlDenom θ₀ π y else 0) := by
            rw [div_eq_mul_inv, Finset.sum_mul]
            refine Finset.sum_congr rfl fun S _ => ?_
            rw [← ENNReal.tsum_mul_right]
            refine tsum_congr fun j => ?_
            by_cases hj : J₀ ≤ j <;> simp [hj, div_eq_mul_inv]
    refine le_trans (setLIntegral_mono ?_ fun y _ => hUsub y) ?_
    · exact Finset.measurable_sum _ fun S _ =>
        Measurable.ennreal_tsum fun j => by
          by_cases hj : J₀ ≤ j
          · simp only [hj, if_true]
            exact (measurable_dlNumer θ₀ π _).div (measurable_dlDenom θ₀ π)
          · simp only [hj, if_false]; exact measurable_const
    -- Integrate the finite sum / countable series term by term.
    rw [lintegral_finset_sum _ fun S _ => Measurable.ennreal_tsum fun j => by
        by_cases hj : J₀ ≤ j
        · simp only [hj, if_true]
          exact (measurable_dlNumer θ₀ π _).div (measurable_dlDenom θ₀ π)
        · simp only [hj, if_false]; exact measurable_const]
    refine Finset.sum_le_sum fun S _ => ?_
    rw [lintegral_tsum fun j => by
        by_cases hj : J₀ ≤ j
        · simp only [hj, if_true]
          exact ((measurable_dlNumer θ₀ π _).div (measurable_dlDenom θ₀ π)).aemeasurable
        · simp only [hj, if_false]; exact aemeasurable_const]
    refine ENNReal.tsum_le_tsum fun j => ?_
    by_cases hj : J₀ ≤ j
    · simp only [if_pos hj]
      have hj2 : 2 ≤ j := le_trans hJ2 hj
      exact shell_ratio_le θ₀ S hj2 ha hr hδnet dbar hdbarpos
    · simp only [if_neg hj]
      simp
  -- Assemble the three pieces `(i) + (ii) + (iii)`.
  have hfinal := add_le_add (add_le_add hi hii) hiii
  calc ∫⁻ y in G, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
        + ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
      ≤ (∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
            + ∫⁻ y in G, dlNumer θ₀ π U y / dlDenom θ₀ π y ∂μ)
          + ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ :=
        add_le_add hGsplit le_rfl
    _ = (∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
            + ∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ)
          + ∫⁻ y in G, dlNumer θ₀ π U y / dlDenom θ₀ π y ∂μ := by ring
    _ ≤ _ := hfinal

/-- **Density positivity off the origin.** For `0 < a` and `x ≠ 0`, `dlDensity a x > 0` (the mixture
integral of a strictly positive integrand over `(0,∞)`). -/
private lemma dlDensity_pos {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ≠ 0) : 0 < dlDensity a x := by
  rw [dlDensity_eq_ofReal_integral ha hx, ENNReal.ofReal_pos]
  -- The integrand is `> 0` on `Ioi 0`, and `Ioi 0` has positive measure.
  apply setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrable_dlDensity_integrand ha hx) |>.mpr
  · -- support ∩ Ioi 0 has positive measure: it is all of Ioi 0
    have hsupp : Function.support
        (fun ψ => dlNormConst a * ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ)) ∩ Set.Ioi (0:ℝ)
        = Set.Ioi (0:ℝ) := by
      ext ψ
      simp only [Set.mem_inter_iff, Function.mem_support, ne_eq, Set.mem_Ioi]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro hψ
        refine ⟨?_, hψ⟩
        have : 0 < dlNormConst a * ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ) := by
          apply mul_pos (mul_pos (dlNormConst_pos ha) (Real.rpow_pos_of_pos hψ _))
            (Real.exp_pos _)
        exact ne_of_gt this
    rw [hsupp]
    simp [Real.volume_Ioi]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun ψ (hψ : 0 < ψ) => ?_)
    exact le_of_lt (mul_pos (mul_pos (dlNormConst_pos ha) (Real.rpow_pos_of_pos hψ _))
      (Real.exp_pos _))

/-- **Marginal positivity on any interval.** For `0 < a`, the DL marginal charges every interval
`{x | |x − c| ≤ s}` of positive half-width `s > 0` with positive mass (the density is a.e. positive,
being `> 0` off the single origin). -/
private lemma dlMarginal_abs_sub_le_pos {a : ℝ} (ha : 0 < a) (c s : ℝ) (hs : 0 < s) :
    0 < dlMarginal a {x : ℝ | |x - c| ≤ s} := by
  have hset : {x : ℝ | |x - c| ≤ s} = Set.Icc (c - s) (c + s) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  have hmeas : MeasurableSet {x : ℝ | |x - c| ≤ s} := by
    rw [hset]; exact measurableSet_Icc
  rw [dlMarginal_eq_withDensity ha, withDensity_apply _ hmeas,
    setLIntegral_pos_iff measurable_dlDensity]
  -- `support (dlDensity a) ⊇ {x ≠ 0}`, so `support ∩ S ⊇ S \ {0}`, of positive volume.
  have hsub : {x : ℝ | |x - c| ≤ s} \ {0} ⊆ Function.support (dlDensity a) ∩ {x | |x - c| ≤ s} := by
    intro x hx
    obtain ⟨hxS, hx0⟩ := hx
    refine ⟨?_, hxS⟩
    simp only [Function.mem_support, ne_eq]
    exact ne_of_gt (dlDensity_pos ha (by simpa using hx0))
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [measure_diff_null (measure_singleton 0), hset, Real.volume_Icc]
  simp only [ENNReal.ofReal_pos]
  linarith

/-- **Shell double-series limit (β-regime).** The engine's term (iii) shell double series, evaluated
at the β-regime instantiation (`a = n^{−(1+β)}`, `r = √(qₙ log n)`, `δ = r/n`), tends to `0` for a
suitable fixed radial floor `J₀ ≥ 2`. This is BPPD's term-iii asymptotic — the summed net-cardinality
`33^{|S|}` and prior-mass-ratio shell contributions, both of which vanish as `n → ∞` (SANCTIONED
FALLBACK: the term-iii limit is the one heavy asymptotic piece left as a TRUE `sorry`). -/
private lemma dl_shellSum_tendsto_zero_beta {β : ℝ} (hβ : 0 < β) {q : ℕ → ℕ} (hq1 : ∀ n, 1 ≤ q n)
    (hqn : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖ ^ 2 ≤ (q n : ℝ) * (Real.log n) ^ 4) :
    ∃ J₀ : ℕ, 2 ≤ J₀ ∧
      Tendsto (fun n =>
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter
            (fun S => S.card ≤ ⌊(3 + 2 / β) * q n⌋₊),
          ∑' j : ℕ, (if J₀ ≤ j then
            (33 : ℝ≥0∞) ^ S.card
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * (Real.sqrt (q n * Real.log n)) ^ 2 / 12))
            + (dlPrior ((n : ℝ) ^ (-(1 + β))) (Fin n))
                (dlShell (θ₀ n) S j (Real.sqrt (q n * Real.log n)) (Real.sqrt (q n * Real.log n) / n))
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * (Real.sqrt (q n * Real.log n)) ^ 2 / 12))
              / dbarVal ((n : ℝ) ^ (-(1 + β))) (Real.sqrt (q n * Real.log n)) (θ₀ n)
            else 0))
        atTop (𝓝 0) := by
  sorry

/-- **Prior charges the contraction ball.** For `0 < a` and `0 < r`, the DL prior gives positive mass
to `closedBall θ₀ r`: a coordinatewise box `{θ | ∀ j, |θ j − θ₀ j| ≤ s}` with `s = r/√(card ι)` sits
inside the ball, and factorizes into a product of positive one-dimensional interval masses. -/
private lemma dlPrior_closedBall_pos {ι : Type*} [Fintype ι] {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (θ₀ : EuclideanSpace ℝ ι) : 0 < dlPrior a ι (Metric.closedBall θ₀ r) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- Empty index: the space is a single point and the ball is everything.
    have : Metric.closedBall θ₀ r = Set.univ := by
      ext θ; simp only [Metric.mem_closedBall, Set.mem_univ, iff_true]
      rw [Subsingleton.elim θ θ₀, dist_self]; exact hr.le
    rw [this, measure_univ]; exact one_pos
  set m : ℝ := (Fintype.card ι : ℝ) with hm_def
  have hmpos : 0 < m := by
    rw [hm_def]; exact_mod_cast Fintype.card_pos
  set s : ℝ := r / Real.sqrt m with hs_def
  have hspos : 0 < s := by rw [hs_def]; positivity
  -- The box sits inside `closedBall θ₀ r`.
  have hbox_sub : {θ : EuclideanSpace ℝ ι | ∀ j, |θ j - θ₀ j| ≤ s} ⊆ Metric.closedBall θ₀ r := by
    intro θ hθ
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsum : ∑ j, (θ j - θ₀ j) ^ 2 ≤ m * s ^ 2 := by
      calc ∑ j, (θ j - θ₀ j) ^ 2 ≤ ∑ _j : ι, s ^ 2 :=
            Finset.sum_le_sum fun j _ => by nlinarith [hθ j, abs_nonneg (θ j - θ₀ j), sq_abs (θ j - θ₀ j)]
        _ = m * s ^ 2 := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm_def]
    have hnormsq : ‖θ - θ₀‖ ^ 2 = ∑ j, (θ j - θ₀ j) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (θ - θ₀) j = θ j - θ₀ j from rfl]
    have hsm0 : Real.sqrt m ≠ 0 := Real.sqrt_ne_zero'.mpr hmpos
    have hsr : Real.sqrt m * s = r := by
      rw [hs_def]; field_simp
    calc ‖θ - θ₀‖ = Real.sqrt (‖θ - θ₀‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (∑ j, (θ j - θ₀ j) ^ 2) := by rw [hnormsq]
      _ ≤ Real.sqrt (m * s ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt m * s := by rw [Real.sqrt_mul hmpos.le, Real.sqrt_sq hspos.le]
      _ = r := hsr
  -- The box mass factorizes into positive one-dimensional masses.
  have hbox_meas : MeasurableSet {θ : EuclideanSpace ℝ ι | ∀ j, |θ j - θ₀ j| ≤ s} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun j => measurableSet_le ?_ measurable_const
    exact (((measurable_pi_apply j).comp
      (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable).sub measurable_const).abs
  have hbox_eq : dlPrior a ι {θ : EuclideanSpace ℝ ι | ∀ j, |θ j - θ₀ j| ≤ s}
      = ∏ j, dlMarginal a {x : ℝ | |x - θ₀ j| ≤ s} := by
    have hpre : (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) ⁻¹'
        {θ | ∀ j, |θ j - θ₀ j| ≤ s}
        = Set.univ.pi (fun j => {y : ℝ | |y - θ₀ j| ≤ s}) := by
      ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ_pi, PiLp.toLp_apply]
    rw [dlPrior, Measure.map_apply measurable_toLp hbox_meas, hpre, Measure.pi_pi]
  have hbox_pos : 0 < dlPrior a ι {θ : EuclideanSpace ℝ ι | ∀ j, |θ j - θ₀ j| ≤ s} := by
    rw [hbox_eq, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro j _
    exact (dlMarginal_abs_sub_le_pos ha (θ₀ j) s hspos).ne'
  exact lt_of_lt_of_le hbox_pos (measure_mono hbox_sub)

/-- `n^{−p} → 0` along `ℕ` for `p > 0` (rpow, cast). -/
private lemma tendsto_natRpow_neg' {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-p)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop

/-- `log n · n^{−p} → 0` along `ℕ` for `p > 0` (polynomial beats logarithm). -/
private lemma tendsto_log_mul_natRpow_neg' {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => Real.log n * (n : ℝ) ^ (-p)) atTop (𝓝 0) := by
  have hlit := (isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero
  have hcast := hlit.comp tendsto_natCast_atTop_atTop
  refine hcast.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  simp only [Function.comp_apply]
  rw [Real.rpow_neg hn0.le, div_eq_mul_inv]

/-- **Poly-beats-log envelope.** For `p > 0`, `(C + D·log n)·n^{−p} → 0`. -/
private lemma tendsto_affineLog_mul_natRpow_neg' {p : ℝ} (hp : 0 < p) (C D : ℝ) :
    Tendsto (fun n : ℕ => (C + D * Real.log n) * (n : ℝ) ^ (-p)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-p)) atTop (𝓝 0) := by
    simpa using (tendsto_natRpow_neg' hp).const_mul C
  have h2 : Tendsto (fun n : ℕ => D * (Real.log n * (n : ℝ) ^ (-p))) atTop (𝓝 0) := by
    simpa using (tendsto_log_mul_natRpow_neg' hp).const_mul D
  have h3 := h1.add h2
  simp only [add_zero] at h3
  refine h3.congr fun n => ?_
  ring

set_option maxHeartbeats 3200000 in
/-- **BPPD Theorem 3.1 (posterior contraction).** In the normal-means model with the Dirichlet–Laplace
prior at scale `aₙ = n^{−(1+β)}`, under the growth condition `‖θ₀‖² ≤ qₙ log⁴n`, there is a constant
`M > 0` such that the posterior mass of `{ θ : ‖θ − θ₀‖ > M√(qₙ log n) }` tends to `0` in `E_{θ₀}`.

**Deviation D1 (rate).** The stated rate is `√(qₙ log n)`, which is what the paper's proof (`rₙ² = qₙ
log n`, p. 15) yields; the paper's headline `sₙ = √(qₙ log(n/qₙ))` is recovered under `qₙ ≤ n^{1−c}` in
`dl_theorem31_paper_rate`. -/
theorem dl_theorem31 {β : ℝ}
    -- USER-INPUT: β > 0 (DL scale exponent aₙ = n^{−(1+β)}); BPPD Thm 3.1.
    (hβ : 0 < β) {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (nonempty approximate support; D3); BPPD Thm 3.1.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n) (sub-linear sparsity); BPPD Thm 3.1.
    (hqn : Tendsto (fun n => (q n : ℝ)/n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ is qₙ-sparse; BPPD Thm 3.1.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    -- USER-INPUT: ‖θ₀‖² ≤ qₙ log⁴n (signal-size growth condition, BPPD (11)); BPPD Thm 3.1.
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖^2 ≤ (q n : ℝ) * (Real.log n)^4) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | M * Real.sqrt (q n * Real.log n) < ‖θ - θ₀ n‖}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  classical
  -- Radial floor `J₀` and the term-(iii) shell double series limit.
  obtain ⟨J₀, hJ2, hshell⟩ := dl_shellSum_tendsto_zero_beta hβ hq1 hqn hθ₀ hnorm
  -- Regime instantiation (mirrors `dl_theorem34_beta`); the threshold `δ = rₙ/n`.
  set A : ℝ := 3 + 2 / β with hA_def
  set S₀ : (n : ℕ) → Finset (Fin n) := fun n => Finset.univ.filter fun j => θ₀ n j ≠ 0 with hS₀
  set av : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 + β)) with hav
  set cv : ℕ → ℝ := fun n => (n : ℝ) ^ (β / 2) with hcv
  set rv : ℕ → ℝ := fun n => Real.sqrt ((q n : ℝ) * Real.log n) with hrv
  set δv : ℕ → ℝ := fun n => rv n / n with hδv
  set mv : ℕ → ℝ := fun n =>
    (letI := Classical.decEq (Fin n); (Fintype.card {i : Fin n // i ∉ S₀ n} : ℝ)) with hmv
  set zv : ℕ → ℝ := fun n => Real.exp 1 * av n * (8 + 2 * Real.log (1 / δv n)) with hzv
  set sv : ℕ → ℝ := fun n => min (rv n / Real.sqrt (mv n)) (1 / 2) with hsv
  set wv : ℕ → ℝ := fun n => Real.exp 1 * av n * (8 + 2 * Real.log (1 / sv n)) with hwv
  set kv : ℕ → ℕ := fun n => ⌊A * q n⌋₊ - (S₀ n).card with hkv
  set P : ℕ → ℝ := fun n => mv n * zv n * (cv n - 1) - (kv n : ℝ) * Real.log (cv n)
      + rv n ^ 2 + 2 * mv n * wv n with hP
  set M : ℝ := 2 * (J₀ : ℝ) with hM_def
  have hJ2R : (2 : ℝ) ≤ (J₀ : ℝ) := by exact_mod_cast hJ2
  have hMpos : 0 < M := by rw [hM_def]; linarith
  refine ⟨M, hMpos, ?_⟩
  -- ===== shared envelope facts (mirror `dl_theorem34_beta`) =====
  have hav_pos : ∀ᶠ n in atTop, 0 < av n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hmv_le : ∀ n, mv n ≤ (n : ℝ) := by
    intro n
    letI := Classical.decEq (Fin n)
    have h : Fintype.card {i : Fin n // i ∉ S₀ n} ≤ n :=
      (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n)
    show (Fintype.card {i : Fin n // i ∉ S₀ n} : ℝ) ≤ (n : ℝ)
    exact_mod_cast h
  have hqlt : ∀ᶠ n in atTop, (q n : ℝ) < n := by
    filter_upwards [hqn.eventually (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)),
      eventually_gt_atTop 0] with n hlt hn0
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
    exact (div_lt_one hnpos).mp hlt
  have hmvpos : ∀ᶠ n in atTop, 0 < mv n := by
    filter_upwards [hqlt] with n hql
    letI := Classical.decEq (Fin n)
    have hcard : (S₀ n).card < n := lt_of_le_of_lt (hθ₀ n) (by exact_mod_cast hql)
    have hex : ∃ j : Fin n, j ∉ S₀ n := by
      by_contra hcon
      push_neg at hcon
      have huniv : S₀ n = Finset.univ := Finset.eq_univ_of_forall hcon
      rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard; omega
    obtain ⟨j, hj⟩ := hex
    haveI : Nonempty {i : Fin n // i ∉ S₀ n} := ⟨j, hj⟩
    show (0 : ℝ) < (Fintype.card {i : Fin n // i ∉ S₀ n} : ℝ)
    exact_mod_cast Fintype.card_pos
  -- `δ = rₙ/n` lies in the window `[n^{−2}, 1/2]` eventually.
  have hδwin : ∀ᶠ (n : ℕ) in atTop, (n : ℝ)^(-2 : ℝ) ≤ δv n ∧ δv n ≤ 1/2 := by
    filter_upwards [eventually_ge_atTop 3,
      hqn.eventually (Iio_mem_nhds (show (0:ℝ) < 1/8 by norm_num))] with n hn3 hqs
    have hn1R : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn3)
    have hnpos : (0:ℝ) < n := by linarith
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1R
    have hq1n : (1:ℝ) ≤ (q n : ℝ) := by exact_mod_cast hq1 n
    have hlogn1 : (1:ℝ) ≤ Real.log n := by
      have h3 : (3:ℝ) ≤ n := by exact_mod_cast hn3
      have := Real.exp_one_lt_d9
      have hle : Real.exp 1 ≤ n := by linarith
      calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) hle
    have hrv_pos : 0 < rv n := by
      rw [hrv]; exact Real.sqrt_pos.mpr (by nlinarith)
    have hrv_ge1 : (1:ℝ) ≤ rv n := by
      rw [hrv, show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    refine ⟨?_, ?_⟩
    · -- n^{−2} ≤ rₙ/n
      have hmono : (n:ℝ)^(-2:ℝ) ≤ (n:ℝ)^(-1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1R (by norm_num)
      have hinv : (n:ℝ)^(-1:ℝ) = 1 / n := by
        rw [Real.rpow_neg_one]; exact (one_div _).symm
      calc (n:ℝ)^(-2:ℝ) ≤ (n:ℝ)^(-1:ℝ) := hmono
        _ = 1 / n := hinv
        _ ≤ rv n / n := by gcongr
    · -- rₙ/n ≤ 1/2
      have hlogle : Real.log n ≤ (n : ℝ) := by
        have := Real.log_le_sub_one_of_pos hnpos; linarith
      have hqle : (q n : ℝ) ≤ n / 8 := by
        have : (q n : ℝ) / n < 1/8 := hqs
        rw [div_lt_iff₀ hnpos] at this; linarith
      have h4 : 4 * rv n ^ 2 ≤ (n : ℝ) ^ 2 := by
        rw [hrv, Real.sq_sqrt (by nlinarith)]
        nlinarith [hqle, hlogle, hlogn0, hq1n, hnpos]
      have h2rv : 2 * rv n ≤ (n : ℝ) := by
        have hsq : Real.sqrt (4 * rv n ^ 2) ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt h4
        rwa [show 4 * rv n ^ 2 = (2 * rv n) ^ 2 by ring, Real.sqrt_sq (by positivity),
          Real.sqrt_sq hnpos.le] at hsq
      rw [hδv, div_le_iff₀ hnpos]; linarith
  have hzv_le : ∀ᶠ n in atTop, zv n ≤ Real.exp 1 * av n * (8 + 4 * Real.log n) := by
    filter_upwards [hδwin, eventually_ge_atTop 1, hav_pos] with n hδn hn1 hapos
    obtain ⟨hδlb, hδub⟩ := hδn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hδpos : 0 < δv n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
    have h1 : Real.log (1 / δv n) ≤ 2 * Real.log n := by
      rw [one_div, Real.log_inv]
      have hle : Real.log ((n:ℝ)^(-2:ℝ)) ≤ Real.log (δv n) :=
        Real.log_le_log (Real.rpow_pos_of_pos hnpos _) hδlb
      rw [Real.log_rpow hnpos] at hle; linarith
    rw [hzv]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsv_ge : ∀ᶠ (n : ℕ) in atTop, 1 / Real.sqrt n ≤ sv n := by
    filter_upwards [eventually_ge_atTop 4, hmvpos] with n hn4 hmvp
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
    have hnpos : (0:ℝ) < n := by linarith
    have hlogn1 : (1:ℝ) ≤ Real.log n := by
      rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      exact Real.log_le_log (Real.exp_pos 1) (by
        have : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
        have h3 : (4:ℝ) ≤ n := by exact_mod_cast hn4
        linarith)
    have hrv1 : (1:ℝ) ≤ rv n := by
      rw [hrv, show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      apply Real.sqrt_le_sqrt
      have hq1n : (1:ℝ) ≤ (q n:ℝ) := by exact_mod_cast hq1 n
      nlinarith [hlogn1, hq1n]
    have hsqn2 : (2:ℝ) ≤ Real.sqrt n := by
      rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt; exact_mod_cast hn4
    have hmvsqle : Real.sqrt (mv n) ≤ Real.sqrt n := Real.sqrt_le_sqrt (hmv_le n)
    have hmvsqpos : 0 < Real.sqrt (mv n) := Real.sqrt_pos.mpr hmvp
    rw [hsv]
    apply le_min
    · calc 1 / Real.sqrt n ≤ 1 / Real.sqrt (mv n) :=
              one_div_le_one_div_of_le hmvsqpos hmvsqle
        _ ≤ rv n / Real.sqrt (mv n) := by gcongr
    · exact one_div_le_one_div_of_le (by norm_num) hsqn2
  have hlogsv_le : ∀ᶠ (n : ℕ) in atTop, Real.log (1 / sv n) ≤ (1/2) * Real.log n := by
    filter_upwards [hsv_ge, eventually_ge_atTop 4] with n hsvge hn4
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
    have hnpos : (0:ℝ) < n := by linarith
    have hsvpos : 0 < sv n := lt_of_lt_of_le (by positivity) hsvge
    have h1svle : 1 / sv n ≤ Real.sqrt n := by
      have h := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 1 / Real.sqrt n) hsvge
      rwa [one_div_one_div] at h
    calc Real.log (1 / sv n) ≤ Real.log (Real.sqrt n) :=
            Real.log_le_log (by positivity) h1svle
      _ = (1/2) * Real.log n := by rw [Real.log_sqrt hnpos.le]; ring
  have hwv_le : ∀ᶠ n in atTop, wv n ≤ Real.exp 1 * av n * (8 + Real.log n) := by
    filter_upwards [hlogsv_le, hav_pos] with n hlog hapos
    rw [hwv]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hWtend : Tendsto (fun n => Real.exp 1 * av n * (8 + Real.log n)) atTop (𝓝 0) := by
    have h := tendsto_affineLog_mul_natRpow_neg' (p := 1 + β) (by linarith)
      (8 * Real.exp 1) (Real.exp 1)
    refine h.congr fun n => ?_
    rw [hav]; ring
  have hw2 : ∀ᶠ n in atTop, wv n ≤ 1 / 2 := by
    have hev : ∀ᶠ n in atTop, Real.exp 1 * av n * (8 + Real.log n) ∈ Set.Iio (1/2 : ℝ) :=
      hWtend.eventually (Iio_mem_nhds (show (0:ℝ) < 1/2 by norm_num))
    filter_upwards [hwv_le, hev] with n h1 h2
    have h2' : Real.exp 1 * av n * (8 + Real.log n) < 1 / 2 := h2
    linarith
  have hcv_gt1 : ∀ᶠ n in atTop, 1 < cv n := by
    filter_upwards [eventually_ge_atTop 2] with n hn2
    have hnpos : (0:ℝ) < n := by
      have : (2:ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    rw [hcv]
    exact (Real.one_lt_rpow_iff_of_pos hnpos).mpr
      (Or.inl ⟨by exact_mod_cast hn2, by positivity⟩)
  -- ===== the three vanishing terms of the engine RHS =====
  have hlogtend : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hS1 : Tendsto (fun n => mv n * zv n * (cv n - 1)) atTop (𝓝 0) := by
    have hU1 : Tendsto (fun n : ℕ =>
        Real.exp 1 * (8 + 4 * Real.log n) * (n : ℝ) ^ (-(β / 2))) atTop (𝓝 0) := by
      have h := tendsto_affineLog_mul_natRpow_neg' (p := β / 2) (by linarith)
        (8 * Real.exp 1) (4 * Real.exp 1)
      refine h.congr fun n => ?_; ring
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU1 ?_ ?_
    · filter_upwards [hδwin, eventually_ge_atTop 1, hav_pos, hcv_gt1] with n hδn hn1 hapos hcvn
      obtain ⟨hδlb, hδub⟩ := hδn
      have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
      have hδpos : 0 < δv n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
      have hlogd : 0 ≤ Real.log (1 / δv n) :=
        Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
      have hzvnn : 0 ≤ zv n := by
        rw [hzv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
      have hmvnn : 0 ≤ mv n := by rw [hmv]; positivity
      exact mul_nonneg (mul_nonneg hmvnn hzvnn) (by linarith [hcvn])
    · filter_upwards [hzv_le, eventually_ge_atTop 1, hav_pos, hcv_gt1, hδwin] with
        n hzvle hn1 hapos hcvn hδn
      obtain ⟨hδlb, hδub⟩ := hδn
      have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
      have hn1R : (1:ℝ) ≤ n := by exact_mod_cast hn1
      have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1R
      have hδpos : 0 < δv n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
      have hlogd : 0 ≤ Real.log (1 / δv n) :=
        Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
      have hmvnn : 0 ≤ mv n := by rw [hmv]; positivity
      have hzvnn : 0 ≤ zv n := by
        rw [hzv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
      have henv_nn : 0 ≤ Real.exp 1 * av n * (8 + 4 * Real.log n) :=
        mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
      have hcvnn : 0 ≤ cv n - 1 := by linarith [hcvn]
      have hcvpos : 0 ≤ cv n := by rw [hcv]; positivity
      have hrpow : (n : ℝ) * av n * cv n = (n : ℝ) ^ (-(β / 2)) := by
        rw [mul_assoc, hav, hcv, ← Real.rpow_add hnpos]
        nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_add hnpos]; congr 1; ring
      calc mv n * zv n * (cv n - 1)
          ≤ (n : ℝ) * (Real.exp 1 * av n * (8 + 4 * Real.log n)) * cv n := by
            apply mul_le_mul _ (by linarith [hcvn]) hcvnn
              (mul_nonneg (by positivity) henv_nn)
            exact mul_le_mul (hmv_le n) hzvle hzvnn (by positivity)
        _ = Real.exp 1 * (8 + 4 * Real.log n) * ((n : ℝ) * av n * cv n) := by ring
        _ = Real.exp 1 * (8 + 4 * Real.log n) * (n : ℝ) ^ (-(β / 2)) := by rw [hrpow]
  have hS2 : Tendsto (fun n => mv n * wv n) atTop (𝓝 0) := by
    have hU2 : Tendsto (fun n : ℕ =>
        Real.exp 1 * (8 + Real.log n) * (n : ℝ) ^ (-β)) atTop (𝓝 0) := by
      have h := tendsto_affineLog_mul_natRpow_neg' (p := β) hβ (8 * Real.exp 1) (Real.exp 1)
      refine h.congr fun n => ?_; ring
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU2 ?_ ?_
    · filter_upwards [hw2, eventually_ge_atTop 4, hsv_ge] with n hw2n hn4 hsvge
      have hmvnn : 0 ≤ mv n := by rw [hmv]; positivity
      have hsvpos : 0 < sv n := lt_of_lt_of_le (by positivity) hsvge
      have hwvnn : 0 ≤ wv n := by
        rw [hwv]
        have : 0 ≤ Real.log (1 / sv n) :=
          Real.log_nonneg (by rw [le_div_iff₀ hsvpos]; linarith [hsvge, show sv n ≤ 1 from le_of_lt (lt_of_le_of_lt (min_le_right _ _) (by norm_num))])
        have hapos : 0 < av n := by
          rw [hav]; exact Real.rpow_pos_of_pos (by exact_mod_cast (le_trans (by norm_num) hn4)) _
        exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
      exact mul_nonneg hmvnn hwvnn
    · filter_upwards [hwv_le, eventually_ge_atTop 4, hav_pos, hsv_ge] with
        n hwvle hn4 hapos hsvge
      have hn1R : (1:ℝ) ≤ n := by
        have : (4:ℝ) ≤ n := by exact_mod_cast hn4
        linarith
      have hnpos : (0:ℝ) < n := by linarith
      have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1R
      have hwvnn : 0 ≤ wv n := by
        rw [hwv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le)
          (by
            have hsvpos : 0 < sv n := lt_of_lt_of_le (by positivity) hsvge
            have : 0 ≤ Real.log (1 / sv n) :=
              Real.log_nonneg (by rw [le_div_iff₀ hsvpos]; linarith [hsvge, show sv n ≤ 1 from le_of_lt (lt_of_le_of_lt (min_le_right _ _) (by norm_num))])
            linarith)
      have hrpow : (n : ℝ) * av n = (n : ℝ) ^ (-β) := by
        rw [hav]
        nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_add hnpos]; congr 1; ring
      calc mv n * wv n ≤ (n : ℝ) * (Real.exp 1 * av n * (8 + Real.log n)) := by
            exact mul_le_mul (hmv_le n) hwvle hwvnn (by positivity)
        _ = Real.exp 1 * (8 + Real.log n) * ((n : ℝ) * av n) := by ring
        _ = Real.exp 1 * (8 + Real.log n) * (n : ℝ) ^ (-β) := by rw [hrpow]
  have hbig : Tendsto (fun n => (kv n : ℝ) * Real.log (cv n) - rv n ^ 2) atTop atTop := by
    apply tendsto_atTop_mono' atTop (f₁ := fun n : ℕ => (β / 2) * Real.log n) ?_
      (hlogtend.const_mul_atTop (by positivity))
    filter_upwards [eventually_ge_atTop 4, hqlt] with n hn4 hql
    have hn1R : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
    have hnpos : (0:ℝ) < n := by linarith
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1R
    have hq1n : (1:ℝ) ≤ q n := by exact_mod_cast hq1 n
    have hlogcv : Real.log (cv n) = (β / 2) * Real.log n := by rw [hcv, Real.log_rpow hnpos]
    have hrv2 : rv n ^ 2 = (q n : ℝ) * Real.log n := by
      rw [hrv]; exact Real.sq_sqrt (mul_nonneg (by positivity) hlogn)
    have hcard_le : (S₀ n).card ≤ ⌊A * (q n : ℝ)⌋₊ := by
      apply Nat.le_floor
      have h1 : ((S₀ n).card : ℝ) ≤ q n := Nat.cast_le.mpr (hθ₀ n)
      have h2 : (1:ℝ) ≤ A := by rw [hA_def]; nlinarith [show (0:ℝ) < 2 / β by positivity]
      nlinarith
    have hklb : (A - 1) * (q n : ℝ) - 1 ≤ (kv n : ℝ) := by
      rw [hkv, Nat.cast_sub hcard_le]
      have hfloor : A * (q n : ℝ) - 1 < ⌊A * (q n : ℝ)⌋₊ := by
        have := Nat.lt_floor_add_one (A * (q n : ℝ)); linarith
      have hcardle : ((S₀ n).card : ℝ) ≤ q n := Nat.cast_le.mpr (hθ₀ n)
      push_cast; nlinarith
    have hAm1 : A - 1 = 2 + 2 / β := by rw [hA_def]; ring
    have hkβ : 2 * (q n : ℝ) * β + 2 * (q n) - β ≤ (kv n : ℝ) * β := by
      have h := mul_le_mul_of_nonneg_right hklb hβ.le
      rw [hAm1] at h
      have hLHS : ((2 + 2 / β) * (q n : ℝ) - 1) * β = 2 * (q n) * β + 2 * (q n) - β := by
        field_simp
      rwa [hLHS] at h
    have hbr : (0:ℝ) ≤ (kv n : ℝ) * β - 2 * (q n) - β := by
      nlinarith [hkβ, mul_nonneg hβ.le (sub_nonneg.mpr hq1n)]
    rw [hlogcv, hrv2]
    nlinarith [mul_nonneg hlogn hbr, hlogn]
  have hε2 : Tendsto (fun n => rv n ^ 2 / 8) atTop atTop := by
    apply tendsto_atTop_mono' atTop (f₁ := fun n : ℕ => Real.log n / 8) ?_
      ((hlogtend).atTop_div_const (by norm_num))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hrv2 : rv n ^ 2 = (q n : ℝ) * Real.log n := by
      rw [hrv]; exact Real.sq_sqrt (mul_nonneg (by positivity) (Real.log_nonneg hn1))
    have hq1n : (1:ℝ) ≤ q n := by exact_mod_cast hq1 n
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
    rw [hrv2]; nlinarith
  have hf1 : Tendsto (fun n => ENNReal.ofReal (Real.exp (P n))) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n => -(P n)) atTop atTop := by
      have hsmall : Tendsto (fun n => -(mv n * zv n * (cv n - 1)) - 2 * (mv n * wv n))
          atTop (𝓝 0) := by
        have h2S2 : Tendsto (fun n => 2 * (mv n * wv n)) atTop (𝓝 0) := by
          simpa using hS2.const_mul 2
        have hh := (hS1.neg).add (h2S2.neg)
        simpa [sub_eq_add_neg] using hh
      have hh := hbig.atTop_add hsmall
      refine hh.congr fun n => ?_
      rw [hP]; ring
    have hh := tendsto_ofReal_exp_neg hdiv
    refine hh.congr fun n => ?_; rw [neg_neg]
  have hf2 : Tendsto (fun n => ENNReal.ofReal (Real.exp (- rv n ^ 2 / 8))) atTop (𝓝 0) := by
    have hh := tendsto_ofReal_exp_neg hε2
    refine hh.congr fun n => ?_; rw [neg_div]
  -- The term-(iii) shell double series, restated over the regime abbreviations (defeq to `hshell`).
  have hshellR : Tendsto (fun n =>
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ ⌊A * (q n : ℝ)⌋₊),
        ∑' j : ℕ, (if J₀ ≤ j then
          (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * rv n ^ 2 / 12))
          + (dlPrior (av n) (Fin n)) (dlShell (θ₀ n) S j (rv n) (δv n))
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * rv n ^ 2 / 12)) / dbarVal (av n) (rv n) (θ₀ n)
          else 0)) atTop (𝓝 0) := hshell
  -- Assemble: the full engine RHS tends to `0`.
  have hRHS : Tendsto (fun n =>
      ENNReal.ofReal (Real.exp (- rv n ^ 2 / 8))
      + (ENNReal.ofReal (Real.exp (P n)) + ENNReal.ofReal (Real.exp (- rv n ^ 2 / 8)))
      + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ ⌊A * (q n : ℝ)⌋₊),
          ∑' j : ℕ, (if J₀ ≤ j then
            (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * rv n ^ 2 / 12))
            + (dlPrior (av n) (Fin n)) (dlShell (θ₀ n) S j (rv n) (δv n))
                * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * rv n ^ 2 / 12)) / dbarVal (av n) (rv n) (θ₀ n)
            else 0)) atTop (𝓝 0) := by
    have h := ((hf2.add (hf1.add hf2)).add hshellR)
    simpa only [add_zero, zero_add] using h
  -- Squeeze the posterior mass between `0` and the engine RHS.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hRHS
    (Filter.Eventually.of_forall fun n => zero_le _) ?_
  filter_upwards [hδwin, eventually_ge_atTop 4, hsv_ge, hw2, hcv_gt1, hav_pos] with
    n hδn hn4 hsvge hw2n hcvn hapos
  obtain ⟨hδlb, hδub⟩ := hδn
  have hn1R : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
  have hnpos : (0:ℝ) < n := by linarith
  have hn2 : (1:ℝ) < n := by
    have : (4:ℝ) ≤ n := by exact_mod_cast hn4
    linarith
  have hn2N : 2 ≤ n := by
    have : (4:ℝ) ≤ n := by exact_mod_cast hn4
    exact_mod_cast (by linarith : (2:ℝ) ≤ n)
  have ha_le1 : av n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1R (by linarith)
  have ha_le2 : av n ≤ 1/2 := by
    show (n:ℝ)^(-(1+β)) ≤ 1/2
    rw [Real.rpow_neg hnpos.le, show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num]
    apply inv_anti₀ (by norm_num)
    calc (2:ℝ) ≤ n := by exact_mod_cast hn2N
      _ = (n:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ (n:ℝ)^(1+β) := Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
  have hδpos : 0 < δv n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
  have hδlt1 : δv n ≤ 1 := le_trans hδub (by norm_num)
  have hlogn_pos : 0 < Real.log n := Real.log_pos hn2
  have hr_pos : 0 < rv n := by
    rw [hrv]; exact Real.sqrt_pos.mpr (mul_pos (by exact_mod_cast hq1 n) hlogn_pos)
  have hsupp : ∀ i ∉ S₀ n, θ₀ n i = 0 := by
    intro i hi
    simp only [hS₀, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    exact hi
  -- `hδnet`: √(card)·δ ≤ r.
  have hδnet : Real.sqrt (Fintype.card (Fin n) : ℝ) * δv n ≤ rv n := by
    rw [Fintype.card_fin, hδv]
    have hsqn : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      calc Real.sqrt (n : ℝ) ≤ Real.sqrt ((n:ℝ)*(n:ℝ)) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = n := by rw [Real.sqrt_mul_self hnpos.le]
    calc Real.sqrt (n : ℝ) * (rv n / n) ≤ (n : ℝ) * (rv n / n) := by
          apply mul_le_mul_of_nonneg_right hsqn (by positivity)
      _ = rv n := by field_simp
  -- C3 tail discharges.
  have hδlt1' : δv n < 1 := lt_of_le_of_lt hδub (by norm_num)
  have hz : (dlMarginal (av n) {x : ℝ | δv n < |x|}).toReal ≤ zv n := by
    have hm := dlMarginal_abs_gt_le' hapos ha_le1 hδpos hδlt1'
    have hlogd : 0 ≤ Real.log (1 / δv n) :=
      Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
    have hznn : (0:ℝ) ≤ zv n := by
      rw [hzv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
    calc (dlMarginal (av n) {x : ℝ | δv n < |x|}).toReal
        ≤ (ENNReal.ofReal (zv n)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
      _ = zv n := ENNReal.toReal_ofReal hznn
  have hsvpos : 0 < sv n := lt_of_lt_of_le (by positivity) hsvge
  have hsvlt1 : sv n < 1 := by
    rw [hsv]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hlogs : 0 ≤ Real.log (1 / sv n) :=
    Real.log_nonneg (by rw [le_div_iff₀ hsvpos]; linarith [hsvlt1])
  have hw : (dlMarginal (av n) {x : ℝ | sv n < |x|}).toReal ≤ wv n := by
    have hm := dlMarginal_abs_gt_le' hapos ha_le1 hsvpos hsvlt1
    have hwnn : (0:ℝ) ≤ wv n := by
      rw [hwv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
    calc (dlMarginal (av n) {x : ℝ | sv n < |x|}).toReal
        ≤ (ENNReal.ofReal (wv n)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
      _ = wv n := ENNReal.toReal_ofReal hwnn
  -- `hk`: the Chernoff cut inclusion.
  have hAqn : (0:ℝ) ≤ A * q n := by rw [hA_def]; positivity
  have hcard_le : (S₀ n).card ≤ ⌊A * (q n : ℝ)⌋₊ := by
    apply Nat.le_floor
    have h1 : ((S₀ n).card : ℝ) ≤ q n := Nat.cast_le.mpr (hθ₀ n)
    have h2 : (1:ℝ) ≤ A := by rw [hA_def]; have : 0 < 2 / β := by positivity
                              linarith
    have h3 : (1:ℝ) ≤ (q n : ℝ) := by exact_mod_cast hq1 n
    nlinarith
  have hk : ((S₀ n).card : ℝ) + (kv n : ℝ) ≤ (⌊A * (q n : ℝ)⌋₊ : ℝ) := by
    rw [hkv, Nat.cast_sub hcard_le]; push_cast; linarith
  have hbBpos : 0 < (dlPrior (av n) (Fin n)) (Metric.closedBall (θ₀ n) (rv n)) :=
    dlPrior_closedBall_pos hapos hr_pos (θ₀ n)
  have hJ₀ : (J₀ : ℝ) ≤ M / 2 := by rw [hM_def]; linarith
  -- Apply the engine (its conclusion is exactly the RHS of the squeeze).
  exact dl_contraction_engine hapos ha_le2 hδpos hδlt1 hδnet hr_pos (θ₀ n) (S₀ n) hsupp hbBpos
    M hMpos (⌊A * (q n : ℝ)⌋₊) J₀ hJ2 hJ₀ (kv n) hk (zv n) hz (wv n) hw hw2n (cv n) hcvn

/-- **BPPD Theorem 3.1, ball / `𝓝 1` form** (BPPD eq. (12)). Equivalent restatement of `dl_theorem31`:
the posterior mass of the contraction ball `{ θ : ‖θ − θ₀‖ ≤ M√(qₙ log n) }` tends to `1` in
`E_{θ₀}`. -/
theorem dl_theorem31_ball {β : ℝ}
    -- USER-INPUT: β > 0; BPPD Thm 3.1.
    (hβ : 0 < β) {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (D3); BPPD Thm 3.1.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n); BPPD Thm 3.1.
    (hqn : Tendsto (fun n => (q n : ℝ)/n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ qₙ-sparse; BPPD Thm 3.1.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    -- USER-INPUT: ‖θ₀‖² ≤ qₙ log⁴n; BPPD Thm 3.1.
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖^2 ≤ (q n : ℝ) * (Real.log n)^4) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | ‖θ - θ₀ n‖ ≤ M * Real.sqrt (q n * Real.log n)}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 1) := by
  obtain ⟨M, hMpos, hlim⟩ := dl_theorem31 hβ hq1 hqn hθ₀ hnorm
  refine ⟨M, hMpos, ?_⟩
  -- Ball mass = 1 − complement mass, pointwise in `y`, then integrate.
  have hcongr : (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | ‖θ - θ₀ n‖ ≤ M * Real.sqrt (q n * Real.log n)}
        ∂(gaussShiftKernel (Fin n) (θ₀ n)))
      = (fun n => 1 - ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | M * Real.sqrt (q n * Real.log n) < ‖θ - θ₀ n‖}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) := by
    funext n
    set r : ℝ := M * Real.sqrt (q n * Real.log n) with hr
    set κ := (gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n)) with hκ
    set μ := gaussShiftKernel (Fin n) (θ₀ n) with hμ
    have hcompl_meas : MeasurableSet {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖} :=
      measurableSet_lt measurable_const ((continuous_id.sub continuous_const).norm.measurable)
    have hg_meas : Measurable (fun y => κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖}) :=
      Kernel.measurable_coe κ hcompl_meas
    have hball_eq : {θ : EuclideanSpace ℝ (Fin n) | ‖θ - θ₀ n‖ ≤ r}
        = {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖}ᶜ := by
      ext θ; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have hpt : ∀ y, κ y {θ : EuclideanSpace ℝ (Fin n) | ‖θ - θ₀ n‖ ≤ r}
        = 1 - κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖} := by
      intro y
      rw [hball_eq, measure_compl hcompl_meas (measure_ne_top _ _), measure_univ]
    have hgle : (fun y => κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖}) ≤ᵐ[μ]
        (fun _ => (1 : ℝ≥0∞)) := ae_of_all _ fun y => prob_le_one
    have hgfin : ∫⁻ y, κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖} ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [lintegral_one]; exact measure_ne_top μ _)
        (lintegral_mono_ae hgle)
    calc ∫⁻ y, κ y {θ : EuclideanSpace ℝ (Fin n) | ‖θ - θ₀ n‖ ≤ r} ∂μ
        = ∫⁻ y, ((1 : ℝ≥0∞) - κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖}) ∂μ :=
          lintegral_congr fun y => hpt y
      _ = (∫⁻ _, (1 : ℝ≥0∞) ∂μ)
            - ∫⁻ y, κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖} ∂μ :=
          lintegral_sub hg_meas hgfin hgle
      _ = 1 - ∫⁻ y, κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖} ∂μ := by
          rw [lintegral_one, measure_univ]
  rw [hcongr]
  have := ((ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt (x := 0)).tendsto.comp hlim
  simpa using this

/-- **BPPD Theorem 3.1, paper rate** (D1 recovery). Under the polynomial-sparsity regime
`qₙ ≤ n^{1−c}` (so `log(n/qₙ) ≍ log n`), the posterior contracts at the paper's minimax rate
`sₙ = √(qₙ log(n/qₙ))`. -/
theorem dl_theorem31_paper_rate {β : ℝ}
    -- USER-INPUT: β > 0; BPPD Thm 3.1.
    (hβ : 0 < β) {c : ℝ}
    -- USER-INPUT: 0 < c < 1 (polynomial-sparsity exponent for qₙ ≤ n^{1−c}); BPPD Thm 3.1 / D1.
    (hc : 0 < c) (hc1 : c < 1) {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (D3); BPPD Thm 3.1.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n); BPPD Thm 3.1.
    (hqn : Tendsto (fun n => (q n : ℝ)/n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ qₙ-sparse; BPPD Thm 3.1.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    -- USER-INPUT: ‖θ₀‖² ≤ qₙ log⁴n; BPPD Thm 3.1.
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖^2 ≤ (q n : ℝ) * (Real.log n)^4)
    -- USER-INPUT: qₙ ≤ n^{1−c} (polynomial sparsity, D1 — makes sₙ ≍ √(qₙ log n)); BPPD Thm 3.1.
    (hqpoly : ∀ᶠ n in Filter.atTop, (q n : ℝ) ≤ (n:ℝ)^(1-c)) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | M * Real.sqrt (q n * Real.log ((n:ℝ)/q n)) < ‖θ - θ₀ n‖}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  obtain ⟨M', hM'pos, hlim⟩ := dl_theorem31 hβ hq1 hqn hθ₀ hnorm
  have hsc : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine ⟨M' / Real.sqrt c, div_pos hM'pos hsc, ?_⟩
  -- Under `qₙ ≤ n^{1−c}`, the paper radius dominates the `√(qₙ log n)` radius, so its exceedance
  -- set is contained in the latter's and the posterior mass is monotone.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ≥0∞))) hlim
    (Filter.Eventually.of_forall fun n => zero_le _) ?_
  filter_upwards [hqpoly, eventually_ge_atTop 2] with n hqp hn2
  -- Radius domination `M' √(qₙ log n) ≤ (M'/√c) √(qₙ log(n/qₙ))`.
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn2
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hqpos : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hq1 n
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
  -- `n / qₙ ≥ n^c`.
  have hnq_ge : (n : ℝ) ^ c ≤ (n : ℝ) / q n := by
    rw [le_div_iff₀ hqpos]
    calc (n : ℝ) ^ c * q n ≤ (n : ℝ) ^ c * (n : ℝ) ^ (1 - c) :=
          mul_le_mul_of_nonneg_left hqp (by positivity)
      _ = (n : ℝ) := by rw [← Real.rpow_add hn0]; simp
  have hlogdom : c * Real.log n ≤ Real.log ((n : ℝ) / q n) := by
    calc c * Real.log n = Real.log ((n : ℝ) ^ c) := (Real.log_rpow hn0 c).symm
      _ ≤ Real.log ((n : ℝ) / q n) := Real.log_le_log (by positivity) hnq_ge
  -- Multiply by `qₙ ≥ 0` and take square roots.
  have hprod : c * ((q n : ℝ) * Real.log n) ≤ (q n : ℝ) * Real.log ((n : ℝ) / q n) := by
    have := mul_le_mul_of_nonneg_left hlogdom hqpos.le
    nlinarith [this]
  have hsqrt : Real.sqrt c * Real.sqrt ((q n : ℝ) * Real.log n)
      ≤ Real.sqrt ((q n : ℝ) * Real.log ((n : ℝ) / q n)) := by
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt hprod
  have hrad : M' * Real.sqrt ((q n : ℝ) * Real.log n)
      ≤ M' / Real.sqrt c * Real.sqrt ((q n : ℝ) * Real.log ((n : ℝ) / q n)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hsc]
    calc M' * Real.sqrt ((q n : ℝ) * Real.log n) * Real.sqrt c
        = M' * (Real.sqrt c * Real.sqrt ((q n : ℝ) * Real.log n)) := by ring
      _ ≤ M' * Real.sqrt ((q n : ℝ) * Real.log ((n : ℝ) / q n)) :=
          mul_le_mul_of_nonneg_left hsqrt hM'pos.le
  -- Set inclusion + monotone posterior mass.
  refine lintegral_mono fun y => measure_mono fun θ hθ => ?_
  simp only [Set.mem_setOf_eq] at hθ ⊢
  exact lt_of_le_of_lt hrad hθ

/-- **BPPD Theorem 3.1, `1/n`-regime companion — DOCUMENTED OPEN CASE (D13).** Same conclusion
(rate `M√(qₙ log n)`) at scale `aₙ = 1/n` under `qₙ ≥ C₀ log n`. **Not proven** by the single-radius
engine route: the `1/n` regime has a genuine two-scale obstruction (compress term needs `r² = qₙ`, shell
series needs `r² = qₙ log n`; the two are incompatible for a single `r`), so it requires a two-scale
peeling sieve the current engine does not model. The proof body carries a full `D13` explanation. The
β-regime `dl_theorem31` (the main result) and `dl_theorem34_recip` (Thm 3.4 at `aₙ=1/n`) are proven and
unaffected. -/
theorem dl_theorem31_recip {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (D3); BPPD Thm 3.1.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n); BPPD Thm 3.1.
    (hqn : Tendsto (fun n => (q n : ℝ)/n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ qₙ-sparse; BPPD Thm 3.1.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    -- USER-INPUT: ‖θ₀‖² ≤ qₙ log⁴n; BPPD Thm 3.1.
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖^2 ≤ (q n : ℝ) * (Real.log n)^4)
    -- USER-INPUT: qₙ ≥ C₀ log n (needed for the 1/n-regime denominator error, D2); BPPD Thm 3.1.
    (hqlog : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ (n : ℕ) in atTop, C₀ * Real.log n ≤ (q n : ℝ)) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)⁻¹) (Fin n))) y
          {θ | M * Real.sqrt (q n * Real.log n) < ‖θ - θ₀ n‖}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  -- OPEN CASE (D13 — two-scale obstruction; the β-regime `dl_theorem31` is proven and unaffected).
  -- The `aₙ = 1/n` regime cannot be closed by the single-radius `dl_contraction_engine` route: the
  -- engine fixes ONE radius `r`, but this regime needs two incompatible scales.
  --   • Compressibility (3.4) needs `r² = qₙ` (small): with `aₙ = 1/n`, the Chernoff exponent
  --     `−(A−1)qₙ·log c + (card')·zₙ·(c−1) + r²` vanishes only for `r² = qₙ` and CONSTANT `c` (then
  --     `qₙ ≥ C₀ log n` lets `−(A−1)qₙ log c` beat the `O(log n)` mixture term `(card')zₙ(c−1)`).
  --   • The shell double-series needs `r² = qₙ log n` (large): the Type-I net count
  --     `∑_{|S|≤Aqₙ} 33^{|S|} ≤ (Aqₙ+1)(33n)^{Aqₙ} = exp(Aqₙ·log 33n)` is beaten by the shell decay
  --     `exp(−J₀²r²/12)` for a FIXED `J₀` ONLY when `r² = qₙ log n`; with `r² = qₙ` it DIVERGES
  --     (`A·log 33n → ∞ > J₀²/12`). This is why the intermediate `dl_shellSum_tendsto_zero_recip` was
  --     provably FALSE and has been removed. Conversely `r² = qₙ log n` breaks the compress term at
  --     `aₙ = 1/n` (`(card')zₙ(c−1) ≍ log n · n^{s}` blows up for any growing `c = n^{s}`).
  -- A sound proof needs a genuine TWO-SCALE (peeling) sieve — a compress radius `≍ √qₙ` and a separate
  -- shell radius `≍ √(qₙ log n)` — which the current single-`r` engine does not model (BPPD §6). Left as
  -- a documented open case; `dl_theorem31` (β-regime) and `dl_theorem34_recip` (Thm 3.4, 1/n) are proven.
  sorry
end StatLean.Bayesian
