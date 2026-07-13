import StatLean.Bayesian.DirichletLaplace.GaussianTests
import StatLean.Bayesian.DirichletLaplace.CoveringNets
import StatLean.Bayesian.DirichletLaplace.CoordinateSplit

/-!
# Dirichlet–Laplace posterior contraction — shell/net decomposition (C13)

The geometric decomposition behind BPPD **Theorem 3.1** (§6 assembly). The complement of the
contraction ball `{ ‖θ − θ₀‖ > M r }` is partitioned into *shells* indexed by a δ-support pattern
`S` and a radial index `j`; each shell is covered by a finite `jr/4`-net, and a two-parameter
midpoint test controls the posterior mass of each net piece.

Objects:
* `dlShell θ₀ S j r δ` — the set of `θ` whose δ-support equals `S` and whose distance from `θ₀` lies
  in the `j`-th radial shell `[jr, (j+1)r)`. Each admissible `θ` (with bounded δ-support) falls into
  exactly one shell, so the complement of the ball is `⋃_{S} ⋃_{j ≥ M} dlShell θ₀ S j r δ`.
* `exists_shell_net` — a `jr/4`-net of `dlShell θ₀ S j r δ` of cardinality `≤ 33^{|S|}`
  (`CoveringNets`, volumetric covering of a `|S|`-dimensional ball) whose pieces have radius
  `≤ (√5/4)·jr` (using `√n·δ ≤ r` and `j ≥ 2`).
* `shell_ratio_le` — the per-shell posterior bound assembled from the midpoint tests
  (`GaussianTests`, Type I/II errors `≤ e^{−(d−ρ)²/8}` with margin `d − ρ ≥ (7/8)jr`, whence
  `≤ e^{−j²r²/12}`) and the testing→posterior conversion (`TestingBound`, `CoordinateSplit`).

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*,
JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Theorem 3.1 (statement p. 7); the shell/test machinery
is the §6 posterior-contraction assembly, in the framework of Ghosal–Ghosh–van der Vaart.

**Proof formalization notes.** The skeleton is *shells → nets → per-piece tests → series*: cover each
shell by its net, test each net piece against `θ₀`, sum the Type I errors over the `≤ 33^{|S|}` pieces
and the Type II errors against the piece prior mass. The outer summation over `(S, j)` is closed in
`Theorem31.lean` (`Nat.choose_le_pow` for the support patterns, `ExpOfRealCalc` for the radial
series).

**Deviations.**
* **D4 (net / test geometry).** The paper's `jr`-net with `2jr`-balls degenerates (a net point may
  coincide with `θ₀`), and a `(jr/2)`-net is inconsistent with a `d/3`-margin test. We use `jr/4`-nets
  (`≤ 33^{|S|}` points), pieces of radius `ρ ≤ (√5/4)jr` (from `√n·δ ≤ r`, `j ≥ 2`), and the
  two-parameter midpoint test `{ y | d(d−ρ)/2 ≤ ⟪y−θ₀, φ−θ₀⟫ }` with both errors `≤ e^{−(d−ρ)²/8}` and
  `d − ρ ≥ (7/8)jr ⇒ ≤ e^{−j²r²/12}`. The non-optimized `(1+β)` testing bound replaces the paper's
  `2√β`, avoiding Neyman–Pearson machinery at no bookkeeping cost.
* **D9 (degenerate index sets).** The `S = ∅` shell is covered by the singleton net `{0}`; handled
  proof-internally, not as a hypothesis.

**Bibliographic comments.** Sieve/net posterior-contraction testing after Ghosal, Ghosh, and van der
Vaart (*Ann. Statist.* 28 (2000), 500–531) and Castillo and van der Vaart (*Ann. Statist.* 40 (2012),
2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Contraction shell** (BPPD §6): the set of `θ` whose δ-support is exactly `S` and whose distance
from `θ₀` lies in the `j`-th radial band `[jr, (j+1)r)`. The complement of the contraction ball is the
disjoint union of these over support patterns `S` and radial indices `j`. Degenerate inputs are not
special-cased in the definition (an empty band or `S` gives the empty shell). -/
noncomputable def dlShell (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι) (j : ℕ) (r δ : ℝ) :
    Set (EuclideanSpace ℝ ι) :=
  {θ | (Finset.univ.filter fun i => δ < |θ i|) = S ∧
       (j : ℝ) * r ≤ ‖θ - θ₀‖ ∧ ‖θ - θ₀‖ < ((j : ℝ) + 1) * r}

/-! ### Private geometry helpers for `exists_shell_net` (D4) -/

/-- From `a² ≤ b²` and `0 ≤ b`, deduce `a ≤ b`. -/
private lemma le_of_sq_le_sq {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : a ≤ b := by
  have habs : |a| ≤ |b| := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h
  calc a ≤ |a| := le_abs_self a
    _ ≤ |b| := habs
    _ = b := abs_of_nonneg hb

/-- Local copy of `CoordinateSplit.projS_ofLp` (there `private`): the `i`-th coordinate of
`projS S θ` is `θ.ofLp i.val`. -/
private lemma projS_ofLp' (S : Set ι) [DecidablePred (· ∈ S)] (θ : EuclideanSpace ℝ ι)
    (i : {j // j ∈ S}) : (projS S θ).ofLp i = θ.ofLp i.val := rfl

/-- Local copy of `CoordinateSplit.projS_sub` (there `private`): `projS S` respects subtraction. -/
private lemma projS_sub' (S : Set ι) [DecidablePred (· ∈ S)] (a b : EuclideanSpace ℝ ι) :
    projS S (a - b) = projS S a - projS S b := by
  unfold projS
  rw [← WithLp.toLp_sub]
  congr 1

/-- `projS S` is norm-nonincreasing (Pythagoras drops the complementary block). -/
private lemma norm_projS_le (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    (x : EuclideanSpace ℝ ι) : ‖projS S x‖ ≤ ‖x‖ := by
  have h := norm_sq_split S x
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  nlinarith [sq_nonneg (‖projS Sᶜ x‖)]

/-- `projS S` recovers the `S`-block of `extendS S u`, which is `u`. -/
private lemma projS_extendS_self (S : Set ι) [DecidablePred (· ∈ S)]
    (u : EuclideanSpace ℝ {j // j ∈ S}) : projS S (extendS S u) = u := by
  apply WithLp.ofLp_injective 2
  funext i
  rw [projS_ofLp']
  unfold extendS
  rw [WithLp.ofLp_toLp, dif_pos i.property]

/-- The complementary block of `extendS S u` is zero. -/
private lemma projS_compl_extendS_self (S : Set ι) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ Sᶜ)] (u : EuclideanSpace ℝ {j // j ∈ S}) :
    projS Sᶜ (extendS S u) = 0 := by
  apply WithLp.ofLp_injective 2
  funext i
  rw [projS_ofLp']
  unfold extendS
  have hi : (i : ι) ∉ S := by have hp := i.property; rwa [Set.mem_compl_iff] at hp
  rw [WithLp.ofLp_toLp, dif_neg hi]
  simp

/-- If every coordinate of `θ` inside `T` is `≤ δ` in modulus, then the `T`-block has norm
`≤ √n·δ ≤ r`. (Kept generic over the `Set T` to fix one uniform `Subtype.fintype` instance.) -/
private lemma norm_projS_le_of_coords {T : Set ι} [DecidablePred (· ∈ T)]
    {θ : EuclideanSpace ℝ ι} {δ r : ℝ}
    (hr : 0 < r) (hδ : Real.sqrt (Fintype.card ι : ℝ) * δ ≤ r)
    (hθ : ∀ i : {x // x ∈ T}, |θ.ofLp i.val| ≤ δ) :
    ‖projS T θ‖ ≤ r := by
  classical
  have hsum : ‖projS T θ‖ ^ 2 ≤ (Fintype.card ι : ℝ) * δ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp_rw [projS_ofLp']
    calc ∑ i : {x // x ∈ T}, (θ.ofLp (i : ι)) ^ 2
        ≤ ∑ _i : {x // x ∈ T}, δ ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          nlinarith [sq_abs (θ.ofLp (i : ι)), abs_nonneg (θ.ofLp (i : ι)), hθ i]
      _ = (Fintype.card {x // x ∈ T} : ℝ) * δ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (Fintype.card ι : ℝ) * δ ^ 2 := by
          gcongr
          exact_mod_cast Fintype.card_subtype_le _
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
  rcases le_or_gt (0 : ℝ) δ with hd | hd
  · have hr2 : (Fintype.card ι : ℝ) * δ ^ 2 ≤ r ^ 2 := by
      have hsd0 : 0 ≤ Real.sqrt (Fintype.card ι : ℝ) * δ := mul_nonneg (Real.sqrt_nonneg _) hd
      calc (Fintype.card ι : ℝ) * δ ^ 2
          = (Real.sqrt (Fintype.card ι : ℝ) * δ) ^ 2 := by rw [mul_pow, Real.sq_sqrt hcard]
        _ ≤ r ^ 2 := by nlinarith [hδ, hsd0, hr.le]
    exact le_of_sq_le_sq (le_trans hsum hr2) hr.le
  · have hempty : IsEmpty {x // x ∈ T} := by
      refine ⟨fun i => ?_⟩
      have := hθ i
      have := abs_nonneg (θ.ofLp (i : ι))
      linarith
    have hz : projS T θ = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]; exact hr.le

/-- **Shell net** (BPPD §6, D4). Every contraction shell `dlShell θ₀ S j r δ` is covered by a finite
`(√5/4)·jr`-net of cardinality `≤ 33^{|S|}` living in the `|S|`-dimensional support coordinates
(`CoveringNets` volumetric covering + `CoordinateSplit`). The radius `(√5/4)jr` uses `√n·δ ≤ r` and
`j ≥ 2` (D4); the `S = ∅` case is the singleton net `{0}` (D9). -/
theorem exists_shell_net (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι) {j : ℕ}
    -- LEAN-ONLY: 2 ≤ j — radial index in the tested range; geometry regularity for the (√5/4)jr radius.
    (hj : 2 ≤ j) {r δ : ℝ}
    -- LEAN-ONLY: 0 < r — radial band width; engine-internal.
    (hr : 0 < r)
    -- LEAN-ONLY: √n·δ ≤ r — box-vs-radius control (δ = r/n regime); engine-internal (D4).
    (hδ : Real.sqrt (Fintype.card ι : ℝ) * δ ≤ r) :
    ∃ net : Finset (EuclideanSpace ℝ ι),
      net.card ≤ 33 ^ S.card ∧
      dlShell θ₀ S j r δ ⊆ ⋃ φ ∈ net, Metric.closedBall φ (Real.sqrt 5 / 4 * ((j : ℝ) * r)) := by
  classical
  set T : Set ι := (↑S : Set ι) with hTdef
  clear_value T
  set R : ℝ := ((j : ℝ) + 1) * r with hRdef
  set ε : ℝ := (j : ℝ) * r / 4 with hεdef
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjr : (0 : ℝ) < (j : ℝ) := by linarith
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεR : ε < R := by rw [hRdef, hεdef]; nlinarith [hjr, hr, mul_pos hjr hr]
  obtain ⟨F₀, hF₀ball, hF₀cover, hF₀card⟩ :=
    exists_finset_net_closedBall (projS T θ₀) R ε hRpos hεpos hεR
  refine ⟨F₀.image (extendS T), ?_, ?_⟩
  · -- Cardinality bound `≤ 33^{|S|}`.
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ {j // j ∈ T}) = S.card := by
      rw [finrank_euclideanSpace, ← Set.toFinset_card, hTdef, Finset.toFinset_coe]
    have hbase : 1 + 2 * R / ε ≤ 33 := by
      have key : 2 * R / ε ≤ 32 := by
        rw [hRdef, hεdef, div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) * r / 4)]
        nlinarith [hj2, hr, mul_pos hjr hr]
      linarith
    have hbnn : (0 : ℝ) ≤ 1 + 2 * R / ε := by positivity
    have hRℝ : ((F₀.image (extendS T)).card : ℝ) ≤ (33 : ℝ) ^ S.card := by
      calc ((F₀.image (extendS T)).card : ℝ)
          ≤ (F₀.card : ℝ) := by exact_mod_cast Finset.card_image_le
        _ ≤ (1 + 2 * R / ε) ^ (Module.finrank ℝ (EuclideanSpace ℝ {j // j ∈ T})) := hF₀card
        _ = (1 + 2 * R / ε) ^ S.card := by rw [hfr]
        _ ≤ (33 : ℝ) ^ S.card := by exact pow_le_pow_left₀ hbnn hbase _
    have : ((F₀.image (extendS T)).card : ℝ) ≤ ((33 ^ S.card : ℕ) : ℝ) := by
      rw [Nat.cast_pow]; push_cast; exact hRℝ
    exact_mod_cast this
  · -- Covering: each shell point is within `√5/4·jr` of a lifted net point.
    intro θ hθmem
    obtain ⟨hfilter, hlow, hhigh⟩ := hθmem
    have hθcoord : ∀ i, i ∉ S → |θ.ofLp i| ≤ δ := by
      intro i hi
      have hnotmem : i ∉ Finset.univ.filter (fun k => δ < |θ.ofLp k|) := by rw [hfilter]; exact hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnotmem
      exact hnotmem
    have hballmem : projS T θ ∈ Metric.closedBall (projS T θ₀) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, ← projS_sub']
      calc ‖projS T (θ - θ₀)‖
          ≤ ‖θ - θ₀‖ := norm_projS_le T (θ - θ₀)
        _ ≤ R := by rw [hRdef]; linarith [hhigh]
    obtain ⟨u, huF₀, hudist⟩ := hF₀cover (projS T θ) hballmem
    refine Set.mem_iUnion₂.mpr ⟨extendS T u, Finset.mem_image_of_mem _ huF₀, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    set c := extendS T u with hcdef
    have hSpart : projS T (θ - c) = projS T θ - u := by
      rw [projS_sub', hcdef, projS_extendS_self]
    have hScpart : projS Tᶜ (θ - c) = projS Tᶜ θ := by
      rw [projS_sub', hcdef, projS_compl_extendS_self, sub_zero]
    have hnormsq : ‖θ - c‖ ^ 2 = ‖projS T θ - u‖ ^ 2 + ‖projS Tᶜ θ‖ ^ 2 := by
      have hsplit := norm_sq_split T (θ - c)
      rw [hSpart, hScpart] at hsplit
      exact hsplit
    have hA : ‖projS T θ - u‖ ≤ ε := by rw [← dist_eq_norm]; exact hudist
    have hB : ‖projS Tᶜ θ‖ ≤ r := by
      refine norm_projS_le_of_coords hr hδ (fun i => ?_)
      have hi : (i : ι) ∉ S := by
        have hp : (i : ι) ∉ T := (Set.mem_compl_iff T _).mp i.property
        set k : ι := (i : ι) with hk
        clear_value k
        rw [hTdef, Finset.mem_coe] at hp
        exact hp
      exact hθcoord i.val hi
    have hA2 : ‖projS T θ - u‖ ^ 2 ≤ ε ^ 2 := by
      nlinarith [hA, norm_nonneg (projS T θ - u), hεpos.le]
    have hB2 : ‖projS Tᶜ θ‖ ^ 2 ≤ r ^ 2 := by
      nlinarith [hB, norm_nonneg (projS Tᶜ θ), hr.le]
    have hbnd : ‖θ - c‖ ^ 2 ≤ (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ 2 := by
      have hεsq : ε ^ 2 = (j : ℝ) ^ 2 * r ^ 2 / 16 := by rw [hεdef]; ring
      have h5 : (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ 2 = 5 / 16 * ((j : ℝ) ^ 2 * r ^ 2) := by
        rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; ring
      rw [hnormsq, h5]
      have hj4 : (4 : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith [hj2]
      nlinarith [hA2, hB2, hεsq, hr, hj4, sq_nonneg r, mul_le_mul_of_nonneg_right hj4 (sq_nonneg r)]
    exact le_of_sq_le_sq hbnd (by positivity)

/-- **Per-shell posterior bound** (BPPD §6, D4). The `E_{θ₀}`-mean of the un-normalized posterior
ratio for a single shell is bounded by the sum over its `≤ 33^{|S|}` net pieces of the Type I test
error `e^{−j²r²/12}`, plus the shell prior mass weighted by the Type II error over the denominator
threshold `dbar`. Assembled from `GaussianTests` (the midpoint tests) and `TestingBound`. -/
theorem shell_ratio_le (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι) {j : ℕ}
    -- LEAN-ONLY: 2 ≤ j — tested radial range (margin d − ρ ≥ (7/8)jr needs j ≥ 2); engine-internal.
    (hj : 2 ≤ j) {a r δ : ℝ}
    -- LEAN-ONLY: 0 < a, 0 < r — DL scale and band width; engine-internal.
    (ha : 0 < a) (hr : 0 < r)
    -- LEAN-ONLY: √n·δ ≤ r — piece-radius control (D4); engine-internal.
    (hδ : Real.sqrt (Fintype.card ι : ℝ) * δ ≤ r)
    -- LEAN-ONLY: 0 < dbar — denominator lower threshold from `DenominatorLowerBound`; engine-internal.
    (dbar : ℝ≥0∞) (hdbar : 0 < dbar) :
    ∫⁻ y in {y | dbar ≤ dlDenom θ₀ (dlPrior a ι) y},
        dlNumer θ₀ (dlPrior a ι) (dlShell θ₀ S j r δ) y / dlDenom θ₀ (dlPrior a ι) y
        ∂(gaussShiftKernel ι θ₀)
      ≤ (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12))
          + (dlPrior a ι) (dlShell θ₀ S j r δ)
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12)) / dbar := by
  -- RESIDUAL DEBT (geometry/constant bug in the FROZEN signature, reported — do NOT weaken it).
  --
  -- The denominator-event restriction added to the LHS DOES fix the earlier `dbar = ⊤` falseness
  -- (on `{⊤ ≤ dlDenom}` the ratio `dlNumer/⊤ = 0`, so the LHS is `0`). But the restricted statement is
  -- still not provable from the supplied machinery, because of a factor-two mismatch between the
  -- radial BAND of `dlShell` and the net-piece radius delivered by `exists_shell_net`.
  --
  -- The recipe (and the old comment) needs, for every NONEMPTY net piece `P_c ⊆ closedBall c ρ ∩ shell`
  -- with `d := ‖c − θ₀‖`, the Type-I margin `d − ρ ≥ (7/8)jr`, which it derives from `‖θ − θ₀‖ ≥ 2jr`.
  -- But `dlShell θ₀ S j r δ` is the BAND `jr ≤ ‖θ − θ₀‖ < (j+1)r`, so every shell point satisfies
  --   `‖θ − θ₀‖ < (j+1)r ≤ (3/2)·jr < 2·jr`   (for `j ≥ 2`),
  -- directly CONTRADICTING the premise `‖θ − θ₀‖ ≥ 2jr`. With the true band floor `jr`, the closest a
  -- nonempty piece's centre can lie to `θ₀` is `d ≥ jr − ρ` (nearest point on the inner sphere), so the
  -- best provable Type-I margin is
  --   `d − ρ ≥ jr − 2ρ = (1 − √5/2)·jr ≈ −0.118·jr < 0`   (since `ρ = √5/4·jr ≈ 0.559·jr`).
  -- The margin is NEGATIVE for every `j ≥ 2` (`ρ > jr/2` always), so `measure_dlTestSet_le`'s hypothesis
  -- `ρ < ‖φ − θ₀‖` fails for near pieces, its Type-I error is `≈ 1/2`, and it is nowhere near the
  -- required `exp(−(d−ρ)²/8) ≤ exp(−j²r²/12)` (which would need margin `≥ √(2/3)·jr ≈ 0.816·jr`).
  --
  -- Root cause: `ρ ≥ r` always (piece radius `ρ² = ε² + r²` from the `Sᶜ`-block of width `≤ √n·δ ≤ r`),
  -- so no refinement of the net can push `ρ` below `r ≥ (1/2)·jr` at `j = 2`, and the recipe's `2jr`
  -- floor is impossible anyway (the band `[2jr,(j+1)r)` would be EMPTY for `j ≥ 2`). The statement is
  -- provable only with a strictly weaker RHS exponent (roughly `exp(−c·r²)`, `c` matching the achievable
  -- `O(r)` margin), not the frozen `exp(−j²r²/12)`. Filling this `sorry` requires either raising the
  -- `dlShell` band floor to `~2jr` (impossible without widening the band) or weakening the RHS constant
  -- — both outside the frozen touch-set. Left as a reported residual debt.
  sorry

end StatLean.Bayesian
