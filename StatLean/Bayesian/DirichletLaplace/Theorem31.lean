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
* `dl_theorem31` — the headline (rate `M√(qₙ log n)`, deviation D1).
* `dl_theorem31_ball` — the equivalent `𝓝 1` form (posterior mass of the ball `{‖θ − θ₀‖ ≤ M√(qₙ log
  n)}` tends to `1`; BPPD eq. (12)).
* `dl_theorem31_paper_rate` — under `qₙ ≤ n^{1−c}`, the paper's minimax rate `sₙ = √(qₙ log(n/qₙ))`.
* `dl_theorem31_recip` — the `aₙ = 1/n` companion under `qₙ ≥ C₀ log n`.

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
* **D2 (regime-dependent `r`).** `β`-regime uses `r² = qₙ log n`; `1/n`-regime (`dl_theorem31_recip`)
  uses `r² = qₙ` and needs `qₙ ≥ C₀ log n`. Same free-`r` engine, two instantiations.
* **D4 (net / test geometry).** Inherited from `ShellDecomposition`: `jr/4`-nets (`≤ 33^{|S|}`),
  pieces of radius `≤ (√5/4)jr`, two-parameter midpoint tests with errors `≤ e^{−j²r²/12}`.

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
  sorry

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
  sorry

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
  sorry

/-- **BPPD Theorem 3.1, `1/n`-regime companion.** Same conclusion (rate `M√(qₙ log n)`) at scale
`aₙ = 1/n`, additionally requiring `qₙ ≥ C₀ log n` so the internal `r² = qₙ` (D2) makes the
denominator error vanish. -/
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
  sorry

end StatLean.Bayesian
