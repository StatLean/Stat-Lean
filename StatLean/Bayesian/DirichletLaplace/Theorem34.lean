import StatLean.Bayesian.DirichletLaplace.CompressEngine
import StatLean.Bayesian.DirichletLaplace.CoordinateSplit
import StatLean.Bayesian.DirichletLaplace.NormalMeansModel
import StatLean.Bayesian.DirichletLaplace.DensityBounds
import StatLean.Bayesian.ForMathlib.ExpOfRealCalc
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dirichlet–Laplace posterior compressibility — BPPD Theorem 3.4 (C15)

Assembly of BPPD **Theorem 3.4**: in the normal-means model `y = θ + ε`, `ε ~ N(0, Iₙ)`, under the
Dirichlet–Laplace prior with scale `aₙ`, the posterior probability that more than `A·qₙ` coordinates
exceed `δₙ` in absolute value tends to `0` in `E_{θ₀}`.

Objects:
* `dl_compress_reduction` — the single passage from the abstract posterior `κ†Π` to the ratio
  functions (`NormalMeansModel` bridge) together with the count split `|supp_δ(θ)| ≤ q + |supp_δ|_{Sᶜ}`
  and the tensorization (BPPD eq. (26), `CoordinateSplit`): the general-`θ₀` compress event is bounded
  by the truth-`0` compress event on the `S₀ᶜ`-submodel.
* `dl_theorem34_engine` — the fixed-`n` explicit bound: reduction + `CompressEngine`
  (`compress_ratio_le_explicit`).
* `dl_theorem34_beta` — the headline for the `β`-regime `aₙ = n^{−(1+β)}`, with internal choice
  `r² = qₙ log n`, `c` chosen so the Chernoff exponent dominates (`A > 2(C+2)/β`).
* `dl_theorem34_recip` — the companion for `aₙ = 1/n`, with internal `r² = qₙ` (which requires
  `qₙ ≥ C₀ log n → ∞` for the denominator error to vanish).

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*,
JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Theorem 3.4 (statement p. 9, proof pp. 18–19).

**Proof formalization notes.** The skeleton is *reduction → denominator event → Chernoff*: bridge the
posterior once (`dl_compress_reduction`), split the ratio integral at the denominator threshold
(`DenominatorLowerBound`), identify the numerator mean with the prior mass (`NormalMeansModel`), and
bound the prior mass of a large δ-support by the support-count Chernoff bound (`PriorSmallBall`,
`DensityBounds` for `ζ`). The asymptotics live only in the two thin corollaries.

**Deviations.**
* **D2 (regime-dependent `r`).** `dl_theorem34_beta` uses `r² = qₙ log n` (failure term needs only
  `qₙ ≥ 1`); `dl_theorem34_recip` uses `r² = qₙ` (failure term `e^{−qₙ}` vanishes only via
  `qₙ ≥ C₀ log n → ∞`). No single `r` serves both regimes — hence two corollaries off one engine.
* **D3 (`1 ≤ qₙ`).** Necessary: for `qₙ = 0` the δ-support of a continuous prior is everything, so
  Theorem 3.4 is false. Carried as the explicit `hq1` hypothesis (implicit in the paper).

**Bibliographic comments.** Posterior contraction after Ghosal, Ghosh, and van der Vaart
(*Ann. Statist.* 28 (2000), 500–531); sparse-sequence compressibility after Castillo and van der Vaart
(*Ann. Statist.* 40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

/-- **Count split off the truth block.** At most `|S₀|` of the large coordinates of `θ` can sit in
`S₀`, so `|supp_δ(θ)| ≤ |S₀| + |supp_δ(projS S₀ᶜ θ)|`. -/
private lemma dlSuppCount_le_card_add_projS {ι : Type*} [Fintype ι] (δ : ℝ) (S₀ : Finset ι)
    (θ : EuclideanSpace ℝ ι) :
    dlSuppCount δ θ ≤ S₀.card + dlSuppCount δ (projS (↑S₀ : Set ι)ᶜ θ) := by
  classical
  -- The `S₀ᶜ`-submodel count equals the count of large coordinates outside `S₀`.
  have hBeq : dlSuppCount δ (projS (↑S₀ : Set ι)ᶜ θ)
      = (Finset.univ.filter (fun j : ι => δ < |θ j| ∧ j ∉ S₀)).card := by
    unfold dlSuppCount
    refine Finset.card_bij
      (fun (i : {j // j ∈ (↑S₀ : Set ι)ᶜ}) _ => (i : ι)) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      have hval : (projS (↑S₀ : Set ι)ᶜ θ) a = θ a.val := rfl
      have hmem : (a : ι) ∉ S₀ := by
        have hp : (a : ι) ∈ (↑S₀ : Set ι)ᶜ := a.property
        rwa [Set.mem_compl_iff, Finset.mem_coe] at hp
      exact ⟨by rwa [hval] at ha, hmem⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hmem : b ∈ (↑S₀ : Set ι)ᶜ := by
        rw [Set.mem_compl_iff, Finset.mem_coe]; exact hb.2
      refine ⟨⟨b, hmem⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hval : (projS (↑S₀ : Set ι)ᶜ θ) ⟨b, hmem⟩ = θ b := rfl
      rw [hval]; exact hb.1
  rw [hBeq]
  -- `|supp_δ θ| = |{large}∩S₀| + |{large}\S₀| ≤ |S₀| + |{large}\S₀|`.
  unfold dlSuppCount
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ.filter (fun j : ι => δ < |θ j|)) (p := fun j => j ∈ S₀)
  have hle : ((Finset.univ.filter (fun j : ι => δ < |θ j|)).filter (fun j => j ∈ S₀)).card
      ≤ S₀.card := by
    refine Finset.card_le_card ?_
    intro j hj
    simp only [Finset.mem_filter] at hj
    exact hj.2
  have hcompl : ((Finset.univ.filter (fun j : ι => δ < |θ j|)).filter
        (fun j => ¬ j ∈ S₀)).card
      = (Finset.univ.filter (fun j : ι => δ < |θ j| ∧ j ∉ S₀)).card := by
    rw [Finset.filter_filter]
  omega

/-- **Compressibility reduction** (BPPD §6, eq. (26)). The `E_{θ₀}`-mean of the posterior mass of
`{ |supp_δ(θ)| > |S₀| + k }` (for a truth `θ₀` supported on `S₀`) is bounded by the truth-`0`
compress-ratio integral on the `S₀ᶜ`-submodel: the posterior is bridged once
(`NormalMeansModel`), the count split off the `S₀` block, and the cylinder ratio tensorized
(`CoordinateSplit`). -/
theorem dl_compress_reduction {ι : Type*} [Fintype ι] {a δ : ℝ}
    -- LEAN-ONLY: 0 < a — DL scale at a junk-free index; engine-internal.
    (ha : 0 < a) (θ₀ : EuclideanSpace ℝ ι) (S₀ : Finset ι)
    -- LEAN-ONLY: θ₀ supported on S₀; engine-internal (the truth's support, `= o(n)` in the assembly).
    (hθ₀ : ∀ i ∉ S₀, θ₀ i = 0) (k : ℕ) :
    ∫⁻ y, ((gaussShiftKernel ι)†(dlPrior a ι)) y
            {θ | ((S₀.card : ℝ) + k) < (dlSuppCount δ θ : ℝ)}
          ∂(gaussShiftKernel ι θ₀)
      ≤ ∫⁻ y, dlNumer (0 : EuclideanSpace ℝ {i : ι // i ∉ S₀}) (dlPrior a {i : ι // i ∉ S₀})
              {θ | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y
            / dlDenom (0 : EuclideanSpace ℝ {i : ι // i ∉ S₀}) (dlPrior a {i : ι // i ∉ S₀}) y
          ∂(gaussShiftKernel {i : ι // i ∉ S₀} (0 : EuclideanSpace ℝ {i : ι // i ∉ S₀})) := by
  classical
  set S : Set ι := (↑S₀ : Set ι) with hSdef
  set π := dlPrior a ι with hπ
  -- The truth vanishes on `Sᶜ`.
  have hθ₀' : projS Sᶜ θ₀ = (0 : EuclideanSpace ℝ {j // j ∈ Sᶜ}) := by
    ext i
    have hval : (projS Sᶜ θ₀) i = θ₀ i.val := rfl
    have hi : (i : ι) ∉ S₀ := i.property
    rw [hval, hθ₀ i.val hi]; rfl
  -- Measurability of the two count events.
  have hcast₁ : Measurable (fun θ : EuclideanSpace ℝ ι => ((dlSuppCount δ θ : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_dlSuppCount δ)
  have hCmeas : MeasurableSet
      {θ : EuclideanSpace ℝ ι | ((S₀.card : ℝ) + k) < (dlSuppCount δ θ : ℝ)} :=
    measurableSet_lt measurable_const hcast₁
  have hcast₂ : Measurable
      (fun θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} => ((dlSuppCount δ θ : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_dlSuppCount δ)
  have hDmeas : MeasurableSet
      {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} :=
    measurableSet_lt measurable_const hcast₂
  -- The compress event sits inside the `Sᶜ`-cylinder over `{count > k}`.
  have hsub : {θ : EuclideanSpace ℝ ι | ((S₀.card : ℝ) + k) < (dlSuppCount δ θ : ℝ)}
      ⊆ projS Sᶜ ⁻¹' {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} := by
    intro θ hθ
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hθ ⊢
    have hcount := dlSuppCount_le_card_add_projS δ S₀ θ
    have : ((S₀.card : ℝ) + k) < (S₀.card : ℝ) + (dlSuppCount δ (projS Sᶜ θ) : ℝ) :=
      lt_of_lt_of_le hθ (by exact_mod_cast hcount)
    linarith
  -- Numerator measurability on the submodel (for the change of variables).
  have hratio_meas : Measurable (fun y' : EuclideanSpace ℝ {j // j ∈ Sᶜ} =>
      dlNumer (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ})
          {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y'
        / dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) y') :=
    (measurable_dlNumer _ _ _).div (measurable_dlDenom _ _)
  have hmproj : Measurable (projS (ι := ι) Sᶜ) := by
    unfold projS
    exact (WithLp.measurable_toLp _ _).comp
      (measurable_pi_lambda _ fun i =>
        (measurable_pi_apply (i : ι)).comp (WithLp.measurable_ofLp 2 _))
  -- Assemble.
  rw [lintegral_posterior_eq_lintegral_ratio θ₀ π hCmeas]
  calc ∫⁻ y, dlNumer θ₀ π
            {θ : EuclideanSpace ℝ ι | ((S₀.card : ℝ) + k) < (dlSuppCount δ θ : ℝ)} y
          / dlDenom θ₀ π y ∂(gaussShiftKernel ι θ₀)
      ≤ ∫⁻ y, dlNumer θ₀ π
            (projS Sᶜ ⁻¹'
              {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)}) y
          / dlDenom θ₀ π y ∂(gaussShiftKernel ι θ₀) := by
        refine lintegral_mono fun y => ?_
        exact ENNReal.div_le_div_right (dlNumer_mono θ₀ π hsub y) _
    _ = ∫⁻ y, dlNumer (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ})
            {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} (projS Sᶜ y)
          / dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) (projS Sᶜ y)
          ∂(gaussShiftKernel ι θ₀) := by
        refine lintegral_congr fun y => ?_
        exact dlRatio_cylinder a S θ₀ y hθ₀' hDmeas
    _ = ∫⁻ y', dlNumer (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ})
            {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y'
          / dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) y'
          ∂((gaussShiftKernel ι θ₀).map (projS Sᶜ)) := by
        rw [lintegral_map hratio_meas hmproj]
    _ = ∫⁻ y', dlNumer (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ})
            {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y'
          / dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) y'
          ∂(gaussShiftKernel {j // j ∈ Sᶜ} (projS Sᶜ θ₀)) := by
        rw [gaussShift_map_projS]
    _ = ∫⁻ y', dlNumer (0 : EuclideanSpace ℝ {j // j ∈ Sᶜ}) (dlPrior a {j // j ∈ Sᶜ})
              {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y'
            / dlDenom (0 : EuclideanSpace ℝ {j // j ∈ Sᶜ}) (dlPrior a {j // j ∈ Sᶜ}) y'
          ∂(gaussShiftKernel {j // j ∈ Sᶜ} (0 : EuclideanSpace ℝ {j // j ∈ Sᶜ})) := by
        rw [hθ₀']

/-- **Fixed-`n` compressibility bound** (BPPD Thm 3.4 engine). For a `q`-sparse truth `θ₀`, the
`E_{θ₀}`-mean of the posterior mass of `{ |supp_δ(θ)| > A·q }` is at most an explicit exponential
(reduction + `compress_ratio_le_explicit`): the Chernoff exponent `−(A−1)q·log c` against the model
size, plus the denominator-event error `e^{−r²/8}`. -/
theorem dl_theorem34_engine {ι : Type*} [Fintype ι] {a δ r : ℝ}
    -- LEAN-ONLY: 0 < a ≤ 1/2 — DL scale range (both density bounds); engine-internal.
    (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    -- LEAN-ONLY: 0 < δ ≤ 1 — δ-window at fixed n; engine-internal.
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    -- LEAN-ONLY: 0 < r — denominator small-ball radius; engine-internal.
    (hr : 0 < r) (θ₀ : EuclideanSpace ℝ ι) {q : ℕ}
    -- LEAN-ONLY: θ₀ q-sparse; engine-internal.
    (hq : (Finset.univ.filter fun i => θ₀ i ≠ 0).card ≤ q)
    -- LEAN-ONLY: 0 < A — compressibility multiplier; engine-internal.
    (A : ℝ) (hA : 0 < A)
    -- LEAN-ONLY: 1 < c — Chernoff parameter; engine-internal.
    (c : ℝ) (hc : 1 < c) :
    ∫⁻ y, ((gaussShiftKernel ι)†(dlPrior a ι)) y {θ | A * (q : ℝ) < (dlSuppCount δ θ : ℝ)}
          ∂(gaussShiftKernel ι θ₀)
      ≤ ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ)
              * (Real.exp 1 * a * (8 + 2 * Real.log (1 / δ))) * (c - 1)
              - (A - 1) * (q : ℝ) * Real.log c + 3 * r ^ 2))
          + ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
  -- RESIDUAL DEBT (engine composition — renegotiation required, see CompressEngine D2/D3 note).
  -- Route: set `S₀ = supp θ₀` (`|S₀| ≤ q`), pick `k` with `|S₀|+k ≤ A·q`, then
  --   `dl_compress_reduction ha θ₀ S₀ hθ₀supp k` (monotone in the event `{A·q<count} ⊆ {|S₀|+k<count}`)
  --   ∘ `compress_ratio_le_explicit` on the `S₀ᶜ`-submodel (`card' = card − |S₀| ≤ card`, `z` from
  --   `dlMarginal_abs_gt_le'`, `w` the C3 tail at `s = min(rₙ/√card', 1/2)`).
  -- Obstruction: the FROZEN exponent is provably not attainable as written and must be renegotiated:
  --   (i) `3 r²` folds the honest small-ball correction `2·card'·w` into `2 r²` via `card'·w ≤ r²`,
  --       which is false for fixed `r` as `card' → ∞` (the tail `w = ζ(s)` does not shrink like
  --       `r²/card'`); the honest engine carries `+ r² + 2·card'·w` (cf. `compress_ratio_le_explicit`).
  --   (ii) `−(A−1)·q·log c` requires `k ≥ (A−1)q` but `k = ⌊A·q⌋ − |S₀| ≥ (A−1)q − 1`, off by `log c`.
  -- Plus edge branches `card' = 0` (dense truth: submodel trivial, LHS = 0) and `δ = 1`
  -- (`dlMarginal_abs_gt_le'` needs `δ < 1`). Deferred: composition is routine once the statement is
  -- renegotiated to the honest exponent; the asymptotic headlines below call reduction ∘ explicit
  -- directly and do not depend on this intermediate.
  sorry

/-- **BPPD Theorem 3.4 (posterior compressibility, `β`-regime).** In the normal-means model with the
Dirichlet–Laplace prior at scale `aₙ = n^{−(1+β)}`, there is a threshold `A > 0` such that the
posterior probability of `{ θ : more than A·qₙ coordinates exceed δₙ }` tends to `0` in `E_{θ₀}`.
Internal radius `r² = qₙ log n` (D2). -/
theorem dl_theorem34_beta {β : ℝ}
    -- USER-INPUT: β > 0 (DL scale exponent aₙ = n^{−(1+β)}); BPPD Thm 3.4.
    (hβ : 0 < β) {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (nonempty approximate support; D3 — for qₙ = 0 Thm 3.4 is false); BPPD Thm 3.4.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n) (sparsity grows sub-linearly); BPPD Thm 3.4.
    (hqn : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ is qₙ-sparse (at most qₙ nonzero coordinates); BPPD Thm 3.4.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    {δ : ℕ → ℝ}
    -- USER-INPUT: δ-window n^{−2} ≤ δₙ ≤ 1/2 (thresholding level; D2 — supports the internal δ = rₙ/n); BPPD Thm 3.4.
    (hδ : ∀ᶠ (n : ℕ) in atTop, (n : ℝ)^(-2 : ℝ) ≤ δ n ∧ δ n ≤ 1/2) :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | A * q n < (dlSuppCount (δ n) θ : ℝ)}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  -- RESIDUAL DEBT (asymptotic assembly). Route (per n, eventually): `dl_compress_reduction` ∘
  -- `compress_ratio_le_explicit` on the `S₀ᶜ`-submodel gives
  --   `∫⁻ … ≤ exp(card'·z·(cₙ−1) − kₙ·log cₙ + rₙ² + 2·card'·wₙ) + exp(−rₙ²/8)`,
  -- with `aₙ = n^{−(1+β)}`, `rₙ² = qₙ log n`, `z ≤ e·aₙ·(8+4 log n)` (C3, `δₙ ≥ n^{−2}`),
  -- `wₙ ≈ z`, `card' ≤ n`, `kₙ ≈ (A−1)qₙ`.
  -- KEY (beyond the frozen note): the Chernoff parameter MUST GROW — with fixed `c`,
  -- `−(A−1)qₙ log c + rₙ² = qₙ(log n − (A−1)log c) → +∞`, so the bound does NOT vanish. Take
  -- `cₙ = n^{1/(A−1)}` so `−(A−1)qₙ log cₙ = −qₙ log n` cancels `+rₙ²`; then the count term
  -- `card'·z·cₙ ≈ n^{−β + 1/(A−1)} log n → 0` requires `A > 1 + C/β` (C the density constant), and the
  -- residual `exp(−rₙ²/8) = exp(−qₙ log n /8) → 0` from `qₙ ≥ 1` (D3). Conclude by
  -- `tendsto_ofReal_exp_neg` (F6) on both terms + `tendsto_of_tendsto_of_tendsto_of_le_of_le'` squeeze.
  -- Deferred: the eventually-discharges (`aₙ ≤ 1/2`, `δₙ < 1`, `wₙ ≤ 1/2`, `card' > 0`, `S₀`-padding to
  -- size `q`) and the growing-`cₙ` limit algebra are ~several hundred lines; not closed in this window.
  sorry

/-- **BPPD Theorem 3.4 (posterior compressibility, `1/n`-regime).** Same conclusion with scale
`aₙ = 1/n`, additionally requiring `qₙ ≥ C₀ log n` so the internal `r² = qₙ` (D2) forces the
denominator error `e^{−qₙ}` to vanish. -/
theorem dl_theorem34_recip {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (D3); BPPD Thm 3.4.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n); BPPD Thm 3.4.
    (hqn : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ qₙ-sparse; BPPD Thm 3.4.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    {δ : ℕ → ℝ}
    -- USER-INPUT: δ-window n^{−2} ≤ δₙ ≤ 1/2 (D2); BPPD Thm 3.4.
    (hδ : ∀ᶠ (n : ℕ) in atTop, (n : ℝ)^(-2 : ℝ) ≤ δ n ∧ δ n ≤ 1/2)
    -- USER-INPUT: qₙ ≥ C₀ log n (needed for the 1/n-regime denominator error, D2); BPPD Thm 3.4.
    (hqlog : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ (n : ℕ) in atTop, C₀ * Real.log n ≤ (q n : ℝ)) :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)⁻¹) (Fin n))) y
          {θ | A * q n < (dlSuppCount (δ n) θ : ℝ)}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  -- RESIDUAL DEBT (asymptotic assembly, `1/n`-regime). Same route as `dl_theorem34_beta` with
  -- `aₙ = 1/n` and `rₙ² = qₙ` (D2). Here the count term `card'·z·cₙ ≈ n^{−1+1/(A−1)}·qₙ/n·…` needs
  -- `A > 2`, and the Chernoff/`+rₙ²` balance uses `cₙ` growing; the residual `exp(−rₙ²/8)=exp(−qₙ/8)`
  -- vanishes only because `qₙ ≥ C₀ log n → ∞` (hypothesis `hqlog`, D2), unlike the `β`-regime where
  -- `qₙ ≥ 1` sufficed. Same deferred discharges + growing-`cₙ` limit algebra as `dl_theorem34_beta`.
  sorry

end StatLean.Bayesian
