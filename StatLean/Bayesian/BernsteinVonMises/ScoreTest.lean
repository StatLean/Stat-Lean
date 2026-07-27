import StatLean.Bayesian.BernsteinVonMises.Defs
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.SubGaussian.Bounded

/-!
# The truncated-score test (moderate range of Lemma 10.3)

The first half of vdV Lemma 10.3: a test based on the empirical mean of the coordinatewise
**truncated score** `sc^L` detects alternatives in the moderate range
`Mₙ/√n ≤ ‖θ − θ₀‖ ≤ ε` with exponential type-II error.

* `bvmOneObs` — the single-observation law `P_θ = p_θ · μ`;
* `bvmTruncScore` — the coordinatewise clamp of the score to `[−L, L]`;
* `truncScore_mean_expansion` — the DQM differentiation of `θ ↦ P_θ sc^L`:
  `P_θ sc^L − P_{θ₀} sc^L = ∫ ⟪θ−θ₀, sc⟫ sc^L dP_{θ₀} + o(‖θ−θ₀‖)` (via the `L²`
  expansion of `√p_θ` and Cauchy–Schwarz);
* `truncScore_separation` — for a suitable truncation level the mean displacement is bounded
  below: `c‖θ−θ₀‖ ≤ ‖P_θ sc^L − P_{θ₀} sc^L‖` on a neighborhood (the matrix
  `P_{θ₀} sc^L (sc^L)ᵀ` tends to the nonsingular `J` as `L → ∞`);
* `truncScore_empirical_dev_tail` — the Hoeffding tail for the empirical mean of the bounded
  vector `sc^L` under `P^n_θ` (coordinatewise Hoeffding + union bound over `2k` events);
* `exists_moderate_tests` — the headline: measurable `[0,1]`-tests with vanishing size at
  `θ₀` and type-II error `≤ exp(−c n ‖θ−θ₀‖²)` on `Mₙ/√n ≤ ‖θ−θ₀‖ ≤ ε`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Lemma 10.3, pp. 143–144 (first test sequence `ω_n`; Hoeffding's inequality via Pollard 1984,
Appendix B).

**Proof formalization notes.** The Type-I bound uses Chebyshev (vdV invokes the CLT; the
variance bound suffices since the threshold is `√(Mₙ/n)` with `Mₙ → ∞`). The Type-II bound
uses `StatLean.ConcentrationInequalities.hoeffding` on each coordinate of the centered
truncated score under `P^n_θ` (`ProbabilityTheory.iIndepFun_pi` supplies coordinate
independence on the product), with two one-sided tails per coordinate.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}

/-- The single-observation law `P_θ = p_θ · μ` of the dominated model. -/
noncomputable def bvmOneObs (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝓧) (θ : EuclideanSpace ℝ (Fin k)) : Measure 𝓧 :=
  μ.withDensity fun x => ENNReal.ofReal (M.density θ x)

/-- The **coordinatewise truncated score** `sc^L`: each coordinate of `sc` clamped to
`[−L, L]` (vdV p. 143: "the score function truncated to the interval `[−L, L]`"). -/
noncomputable def bvmTruncScore (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (L : ℝ) :
    𝓧 → EuclideanSpace ℝ (Fin k) :=
  fun x => (WithLp.equiv 2 (Fin k → ℝ)).symm
    (fun i => max (-L) (min L ((WithLp.equiv 2 (Fin k → ℝ)) (sc x) i)))

lemma measurable_bvmTruncScore
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc) (L : ℝ) :
    Measurable (bvmTruncScore sc L) := by
  unfold bvmTruncScore
  refine (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp (measurable_pi_lambda _ fun i => ?_)
  exact measurable_const.max
    (measurable_const.min (((measurable_pi_apply i).comp
      (WithLp.measurable_ofLp 2 (Fin k → ℝ))).comp hsc))

lemma norm_bvmTruncScore_le (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) {L : ℝ}
    -- LEAN-ONLY: nonnegative truncation level
    (hL : 0 ≤ L) (x : 𝓧) :
    ‖bvmTruncScore sc L x‖ ≤ Real.sqrt k * L := by
  have hcoord : ∀ i, ‖(bvmTruncScore sc L x) i‖ ≤ L := by
    intro i
    change |max (-L) (min L ((WithLp.equiv 2 (Fin k → ℝ)) (sc x) i))| ≤ L
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hsum : ∑ i, ‖(bvmTruncScore sc L x) i‖ ^ 2 ≤ (k : ℝ) * L ^ 2 := by
    calc ∑ i : Fin k, ‖(bvmTruncScore sc L x) i‖ ^ 2
        ≤ ∑ _i : Fin k, L ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
      _ = (k : ℝ) * L ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i, ‖(bvmTruncScore sc L x) i‖ ^ 2)
      ≤ Real.sqrt ((k : ℝ) * L ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt k * L := by
        rw [Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq hL]

/-- The one-observation law is a probability measure (normalisation of the density). -/
private lemma bvmOneObs_isProbabilityMeasure (hPDF : IsPDFOf M μ)
    (θ : EuclideanSpace ℝ (Fin k)) : IsProbabilityMeasure (bvmOneObs M μ θ) := by
  refine ⟨?_⟩
  rw [bvmOneObs, MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hPDF.density_integrable θ)
      (Filter.Eventually.of_forall (M.density_nonneg θ)),
    hPDF.density_integral_eq_one θ, ENNReal.ofReal_one]

/-- The `n`-fold product experiment is the `n`-fold `Measure.pi` of the one-observation law. -/
private lemma productMeasure_eq_pi (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    productMeasure M μ θ n = Measure.pi (fun _ : Fin n => bvmOneObs M μ θ) := rfl

/-- Under `Measure.pi`, the law of a single coordinate is the factor law. -/
private lemma integral_eval_pi {P : Measure 𝓧} [IsProbabilityMeasure P] {n : ℕ}
    (g : 𝓧 → ℝ) (hg : Measurable g) (i : Fin n) :
    ∫ ω, g (ω i) ∂(Measure.pi fun _ : Fin n => P) = ∫ x, g x ∂P := by
  have h := integral_map (μ := Measure.pi fun _ : Fin n => P)
    (φ := fun ω : Fin n → 𝓧 => ω i) (f := g)
    (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable
  rw [(measurePreserving_eval (fun _ : Fin n => P) i).map_eq] at h
  exact h.symm

/-- **Hoeffding for one bounded coordinate under the product experiment.** -/
private lemma coord_hoeffding {P : Measure 𝓧} [IsProbabilityMeasure P] {n : ℕ} (hn : 1 ≤ n)
    (g : 𝓧 → ℝ) (hg : Measurable g) {L : ℝ} (hL : 0 < L)
    (hgb : ∀ x, g x ∈ Set.Icc (-L) L) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin n => P).real
        {ω | (n : ℝ) * t ≤ ∑ i, (g (ω i) - ∫ x, g x ∂P)}
      ≤ Real.exp (-(n : ℝ) * t ^ 2 / (2 * L ^ 2)) := by
  classical
  set Pn : Measure (Fin n → 𝓧) := Measure.pi fun _ : Fin n => P with hPn
  haveI : IsProbabilityMeasure Pn := by rw [hPn]; infer_instance
  set c : NNReal := (‖L - (-L)‖₊ / 2) ^ 2 with hc
  have hcval : ((c : NNReal) : ℝ) = L ^ 2 := by
    rw [hc]; push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ L - (-L))]
    ring
  -- independence of the centered coordinates
  have hindep : iIndepFun (fun (i : Fin n) (ω : Fin n → 𝓧) => g (ω i) - ∫ x, g x ∂P) Pn := by
    rw [hPn]
    exact iIndepFun_pi (X := fun _ : Fin n => fun x : 𝓧 => g x - ∫ x, g x ∂P)
      (fun _ => (hg.sub_const _).aemeasurable)
  -- sub-Gaussianity of each centered coordinate
  have hsubG : ∀ i : Fin n, i ∈ (Finset.univ : Finset (Fin n)) →
      HasSubgaussianMGF (fun ω : Fin n → 𝓧 => g (ω i) - ∫ x, g x ∂P) c Pn := by
    intro i _
    have hicc : StatLean.ConcentrationInequalities.IsSubGaussian
        (fun ω : Fin n → 𝓧 => g (ω i)) c Pn := by
      refine StatLean.ConcentrationInequalities.isSubGaussian_of_mem_Icc (a := -L) (b := L)
        (hg.comp (measurable_pi_apply (X := fun _ : Fin n => 𝓧) i)).aemeasurable ?_
      exact Filter.Eventually.of_forall fun ω => hgb (ω i)
    have hmean : ∫ ω, g (ω i) ∂Pn = ∫ x, g x ∂P := by rw [hPn]; exact integral_eval_pi g hg i
    have : HasSubgaussianMGF (fun ω : Fin n → 𝓧 => g (ω i) - ∫ ω, g (ω i) ∂Pn) c Pn := hicc
    rwa [hmean] at this
  have hε : (0 : ℝ) ≤ (n : ℝ) * t := mul_nonneg (Nat.cast_nonneg n) ht
  have hmain := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (μ := Pn) hindep
    (c := fun _ : Fin n => c) (s := Finset.univ) hsubG hε
  refine hmain.trans_eq ?_
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsumc : ((∑ _i : Fin n, c : NNReal) : ℝ) = (n : ℝ) * L ^ 2 := by
    rw [Finset.sum_const]
    push_cast
    rw [hcval]
    simp [nsmul_eq_mul]
  congr 1
  rw [hsumc]
  field_simp

/-- **DQM differentiation of the truncated-score mean** (vdV p. 143, "It follows that
`P_θ ℓ̇^L_{θ₀} − P_{θ₀} ℓ̇^L_{θ₀} = (P_{θ₀} ℓ̇^L_{θ₀} ℓ̇^T_{θ₀} + o(1))(θ − θ₀)`"): the map
`θ ↦ P_θ sc^L` is differentiable at `θ₀` with derivative acting as
`u ↦ ∫ ⟪u, sc x⟫ • sc^L x dP_{θ₀}(x)`, in little-o form. -/
theorem truncScore_mean_expansion
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV Thm 10.1
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc) {L : ℝ}
    -- LEAN-ONLY: positive truncation level
    (hL : 0 < L) :
    (fun θ => ∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ)
        - ∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ₀)
        - ∫ x, ⟪θ - θ₀, sc x⟫ • bvmTruncScore sc L x ∂(bvmOneObs M μ θ₀))
      =o[𝓝 θ₀] fun θ => ‖θ - θ₀‖ := by
  sorry

/-- **Mean-displacement separation** (vdV p. 144, top): for a suitable truncation level `L`
the displacement of the truncated-score mean is bounded below by `c‖θ − θ₀‖` on a
neighborhood of `θ₀` (choose `L` with `P_{θ₀} sc^L (sc^L)ᵀ` close enough to the nonsingular
`J`, by dominated convergence). -/
theorem truncScore_separation
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV Thm 10.1
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV Thm 10.1
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫) :
    ∃ L ε c : ℝ, 0 < L ∧ 0 < ε ∧ 0 < c ∧
      ∀ θ, ‖θ - θ₀‖ < ε →
        c * ‖θ - θ₀‖ ≤ ‖∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ)
          - ∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ₀)‖ := by
  sorry

/-- **Vector Hoeffding**: coordinatewise Hoeffding plus a union bound over the `2k` one-sided
coordinate events. -/
private lemma vector_hoeffding {P : Measure 𝓧} [IsProbabilityMeasure P] {n : ℕ} (hn : 1 ≤ n)
    (f : 𝓧 → EuclideanSpace ℝ (Fin k)) (hfm : Measurable f) {L : ℝ} (hL : 0 < L)
    (hfb : ∀ x (j : Fin k), f x j ∈ Set.Icc (-L) L) {s : ℝ} (hs : 0 < s) :
    (Measure.pi fun _ : Fin n => P).real
        {ω | s ≤ ‖(n : ℝ)⁻¹ • ∑ i, f (ω i) - ∫ x, f x ∂P‖}
      ≤ 2 * k * Real.exp (-(n : ℝ) * s ^ 2 / (2 * k * L ^ 2)) := by
  classical
  set Pn : Measure (Fin n → 𝓧) := Measure.pi fun _ : Fin n => P with hPn
  haveI : IsProbabilityMeasure Pn := by rw [hPn]; infer_instance
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hempty : {ω : Fin n → 𝓧 | s ≤ ‖(n : ℝ)⁻¹ • ∑ i, f (ω i) - ∫ x, f x ∂P‖} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have : ‖(n : ℝ)⁻¹ • ∑ i, f (ω i) - ∫ x, f x ∂P‖ = 0 := by
        rw [EuclideanSpace.norm_eq]; simp
      rw [this]; exact hs
    rw [hempty]
    simp
  -- `k ≥ 1`: the coordinate threshold is `t = s / √k`
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
  have hsqk : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.2 hkR
  have hsqk_sq : Real.sqrt k ^ 2 = (k : ℝ) := Real.sq_sqrt hkR.le
  set t : ℝ := s / Real.sqrt k with htdef
  have htpos : (0 : ℝ) < t := div_pos hs hsqk
  have ht_sq : t ^ 2 = s ^ 2 / (k : ℝ) := by
    rw [htdef, div_pow, hsqk_sq]
  -- the vector mean and its coordinates
  set mvec : EuclideanSpace ℝ (Fin k) := ∫ x, f x ∂P with hmvec
  have hfint : Integrable f P :=
    (integrable_const (Real.sqrt k * L)).mono' hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [EuclideanSpace.norm_eq]
        have hsum : ∑ j, ‖f x j‖ ^ 2 ≤ (k : ℝ) * L ^ 2 := by
          calc ∑ j : Fin k, ‖f x j‖ ^ 2
              ≤ ∑ _j : Fin k, L ^ 2 := Finset.sum_le_sum fun j _ => by
                have := hfb x j
                rw [Set.mem_Icc] at this
                rw [Real.norm_eq_abs]
                have : |f x j| ≤ L := abs_le.2 ⟨this.1, this.2⟩
                exact pow_le_pow_left₀ (abs_nonneg _) this 2
            _ = (k : ℝ) * L ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
        calc Real.sqrt (∑ j, ‖f x j‖ ^ 2) ≤ Real.sqrt ((k : ℝ) * L ^ 2) :=
              Real.sqrt_le_sqrt hsum
          _ = Real.sqrt k * L := by rw [Real.sqrt_mul hkR.le, Real.sqrt_sq hL.le])
  have hprojm : ∀ j : Fin k, mvec j = ∫ x, f x j ∂P := fun j =>
    ((EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm hfint).symm
  -- coordinates of the centered empirical mean
  have hVj : ∀ (ω : Fin n → 𝓧) (j : Fin k),
      ((n : ℝ)⁻¹ • ∑ i, f (ω i) - mvec) j = (n : ℝ)⁻¹ * (∑ i, f (ω i) j) - mvec j := by
    intro ω j
    have hlin : (EuclideanSpace.proj (𝕜 := ℝ) j) ((n : ℝ)⁻¹ • ∑ i, f (ω i) - mvec)
        = (n : ℝ)⁻¹ * (∑ i, f (ω i) j) - mvec j := by
      rw [map_sub, map_smul, map_sum]
      rfl
    exact hlin
  -- coordinate events
  set E : Set (Fin n → 𝓧) := {ω | s ≤ ‖(n : ℝ)⁻¹ • ∑ i, f (ω i) - mvec‖} with hE
  set A : Fin k → Set (Fin n → 𝓧) := fun j =>
    {ω | (n : ℝ) * t ≤ ∑ i, (f (ω i) j - ∫ x, f x j ∂P)} with hA
  set B : Fin k → Set (Fin n → 𝓧) := fun j =>
    {ω | (n : ℝ) * t ≤ ∑ i, (-f (ω i) j - ∫ x, -f x j ∂P)} with hB
  have hincl : E ⊆ ⋃ j : Fin k, (A j ∪ B j) := by
    intro ω hω
    -- some coordinate exceeds `t` in absolute value
    have hex : ∃ j : Fin k, t ≤ |((n : ℝ)⁻¹ • ∑ i, f (ω i) - mvec) j| := by
      by_contra hcon
      push_neg at hcon
      have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
        ⟨⟨0, hkpos⟩, Finset.mem_univ _⟩
      have hlt : ‖(n : ℝ)⁻¹ • ∑ i, f (ω i) - mvec‖ ^ 2 < s ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        calc ∑ j, ‖((n : ℝ)⁻¹ • ∑ i, f (ω i) - mvec) j‖ ^ 2
            < ∑ _j : Fin k, t ^ 2 := by
              refine Finset.sum_lt_sum_of_nonempty hne fun j _ => ?_
              rw [Real.norm_eq_abs]
              exact pow_lt_pow_left₀ (hcon j) (abs_nonneg _) two_ne_zero
          _ = (k : ℝ) * t ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
          _ = s ^ 2 := by rw [ht_sq]; field_simp
      have hn0 : (0 : ℝ) ≤ ‖(n : ℝ)⁻¹ • ∑ i, f (ω i) - mvec‖ := norm_nonneg _
      have := hω
      rw [hE] at this
      simp only [Set.mem_setOf_eq] at this
      nlinarith
    obtain ⟨j, hj⟩ := hex
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    rw [hVj ω j] at hj
    have hsumA : ∑ i, (f (ω i) j - ∫ x, f x j ∂P)
        = (n : ℝ) * ((n : ℝ)⁻¹ * (∑ i, f (ω i) j) - mvec j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← hprojm j]
      field_simp
    rcases le_abs.1 hj with h | h
    · exact Or.inl (by rw [hA]; simp only [Set.mem_setOf_eq, hsumA]; nlinarith)
    · refine Or.inr ?_
      rw [hB]
      simp only [Set.mem_setOf_eq]
      have hsumB : ∑ i, (-f (ω i) j - ∫ x, -f x j ∂P)
          = -((n : ℝ) * ((n : ℝ)⁻¹ * (∑ i, f (ω i) j) - mvec j)) := by
        rw [integral_neg, ← hsumA, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsumB]; nlinarith
  -- the per-coordinate bound
  have hexp : (-(n : ℝ) * t ^ 2 / (2 * L ^ 2))
      = -(n : ℝ) * s ^ 2 / (2 * (k : ℝ) * L ^ 2) := by
    rw [ht_sq]; field_simp
  have hAb : ∀ j : Fin k, Pn.real (A j)
      ≤ Real.exp (-(n : ℝ) * s ^ 2 / (2 * (k : ℝ) * L ^ 2)) := by
    intro j
    have := coord_hoeffding (P := P) hn (fun x => f x j)
      ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable.comp hfm) hL
      (fun x => hfb x j) htpos.le
    rw [hexp] at this
    exact this
  have hBb : ∀ j : Fin k, Pn.real (B j)
      ≤ Real.exp (-(n : ℝ) * s ^ 2 / (2 * (k : ℝ) * L ^ 2)) := by
    intro j
    have hnegb : ∀ x, -f x j ∈ Set.Icc (-L) L := by
      intro x
      have := hfb x j
      rw [Set.mem_Icc] at this ⊢
      constructor <;> linarith [this.1, this.2]
    have := coord_hoeffding (P := P) hn (fun x => -f x j)
      (((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable.comp hfm).neg) hL
      hnegb htpos.le
    rw [hexp] at this
    exact this
  calc Pn.real E
      ≤ Pn.real (⋃ j : Fin k, (A j ∪ B j)) := measureReal_mono hincl (measure_ne_top _ _)
    _ ≤ ∑ j : Fin k, Pn.real (A j ∪ B j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ j : Fin k, (Pn.real (A j) + Pn.real (B j)) :=
        Finset.sum_le_sum fun j _ => measureReal_union_le _ _
    _ ≤ ∑ _j : Fin k, (2 * Real.exp (-(n : ℝ) * s ^ 2 / (2 * (k : ℝ) * L ^ 2))) :=
        Finset.sum_le_sum fun j _ => by linarith [hAb j, hBb j]
    _ = 2 * (k : ℝ) * Real.exp (-(n : ℝ) * s ^ 2 / (2 * (k : ℝ) * L ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Hoeffding tail for the empirical truncated-score mean** under any `P^n_θ`: for bounded
coordinates (`|sc^L_j| ≤ L`), the deviation of the empirical mean from its `P_θ`-mean
exceeds `s` with probability at most `2k · exp(−n s² / (2 k L²))` (coordinatewise Hoeffding
+ union bound over the `2k` one-sided events). -/
theorem truncScore_empirical_dev_tail
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc) {L : ℝ}
    -- LEAN-ONLY: positive truncation level
    (hL : 0 < L) (θ : EuclideanSpace ℝ (Fin k)) {n : ℕ}
    -- LEAN-ONLY: at least one observation
    (hn : 1 ≤ n) {s : ℝ}
    -- LEAN-ONLY: positive threshold
    (hs : 0 < s) :
    (productMeasure M μ θ n).real
        {ω | s ≤ ‖(n : ℝ)⁻¹ • ∑ i, bvmTruncScore sc L (ω i)
          - ∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ)‖}
      ≤ 2 * k * Real.exp (-(n : ℝ) * s ^ 2 / (2 * k * L ^ 2)) := by
  haveI : IsProbabilityMeasure (bvmOneObs M μ θ) := bvmOneObs_isProbabilityMeasure hPDF θ
  have hfb : ∀ (x : 𝓧) (j : Fin k), bvmTruncScore sc L x j ∈ Set.Icc (-L) L := by
    intro x j
    have hval : bvmTruncScore sc L x j
        = max (-L) (min L ((WithLp.equiv 2 (Fin k → ℝ)) (sc x) j)) := rfl
    rw [hval, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  exact vector_hoeffding (P := bvmOneObs M μ θ) hn (bvmTruncScore sc L)
    (measurable_bvmTruncScore hsc L) hL hfb hs

/-- The empirical mean `n⁻¹ ∑ᵢ sc^L(ωᵢ)` of the truncated score. -/
private noncomputable def bvmEmpTrunc (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (L : ℝ) (n : ℕ)
    (ω : Fin n → 𝓧) : EuclideanSpace ℝ (Fin k) :=
  (n : ℝ)⁻¹ • ∑ i, bvmTruncScore sc L (ω i)

/-- The `P_θ`-mean `P_θ sc^L` of the truncated score. -/
private noncomputable def bvmTruncMean (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝓧) (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (L : ℝ)
    (θ : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k) :=
  ∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ)

/-- `truncScore_empirical_dev_tail` restated with the private abbreviations. -/
private lemma truncScore_tail' (hPDF : IsPDFOf M μ) (hsc : Measurable sc) {L : ℝ}
    (hL : 0 < L) (θ : EuclideanSpace ℝ (Fin k)) {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    (productMeasure M μ θ n).real
        {ω | s ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ‖}
      ≤ 2 * k * Real.exp (-(n : ℝ) * s ^ 2 / (2 * k * L ^ 2)) :=
  truncScore_empirical_dev_tail hPDF hsc hL θ hn hs

/-- Measurability of the empirical truncated-score mean. -/
private lemma measurable_bvmEmpTrunc (hsc : Measurable sc) (L : ℝ) (n : ℕ) :
    Measurable (bvmEmpTrunc sc L n) := by
  have hb : Measurable (bvmTruncScore sc L) := measurable_bvmTruncScore hsc L
  have hsum : Measurable fun ω : Fin n → 𝓧 => ∑ i, bvmTruncScore sc L (ω i) := by
    simpa using
      (Finset.measurable_sum (Finset.univ : Finset (Fin n))
        (fun i _ => hb.comp (measurable_pi_apply (X := fun _ : Fin n => 𝓧) i)))
  unfold bvmEmpTrunc
  exact ((continuous_const_smul ((n : ℝ)⁻¹)).measurable).comp hsum

/-! ### Elementary real-arithmetic bricks for the moderate-range assembly -/

/-- If `Mₙ ≥ 4/c²` then the threshold `√(Mₙ/n)` is at most half of `c·(Mₙ/√n) ≤ c·d`. -/
private lemma moderate_arith {c d Mn nR : ℝ} (hc : 0 < c) (hnR : 0 < nR)
    (hMn : 0 < Mn) (h4 : 4 / c ^ 2 ≤ Mn) (hd : Mn / Real.sqrt nR ≤ d) :
    Real.sqrt (Mn / nR) ≤ c * d / 2 := by
  have hsqn : 0 < Real.sqrt nR := Real.sqrt_pos.2 hnR
  have hu : Real.sqrt Mn ^ 2 = Mn := Real.sq_sqrt hMn.le
  have hupos : 0 < Real.sqrt Mn := Real.sqrt_pos.2 hMn
  have h4' : 4 ≤ Mn * c ^ 2 := by
    rw [div_le_iff₀ (pow_pos hc 2)] at h4; linarith only [h4]
  have huc : 2 ≤ Real.sqrt Mn * c := by
    nlinarith only [hu, hupos, hc, h4', mul_pos hupos hc]
  have hA : Real.sqrt (Mn / nR) ≤ c * (Mn / Real.sqrt nR) / 2 := by
    rw [Real.sqrt_div hMn.le, div_le_iff₀ hsqn]
    have heq : c * (Mn / Real.sqrt nR) / 2 * Real.sqrt nR = c * Mn / 2 := by
      field_simp
    rw [heq]
    nlinarith only [hu, hupos, huc, hc]
  have hB : c * (Mn / Real.sqrt nR) / 2 ≤ c * d / 2 := by
    nlinarith only [hd, hc, mul_nonneg hc.le (sub_nonneg.2 hd)]
  linarith only [hA, hB]

/-- `d ≥ Mₙ/√n` upgrades to `n d² ≥ Mₙ²`. -/
private lemma moderate_arith2 {Mn nR d : ℝ} (hnR : 0 < nR) (hMn : 0 < Mn)
    (hd : Mn / Real.sqrt nR ≤ d) : Mn ^ 2 ≤ nR * d ^ 2 := by
  have hsqn : 0 < Real.sqrt nR := Real.sqrt_pos.2 hnR
  have hv : Real.sqrt nR ^ 2 = nR := Real.sq_sqrt hnR.le
  have h1 : Mn ≤ Real.sqrt nR * d := by
    rw [div_le_iff₀ hsqn] at hd; linarith only [hd]
  nlinarith only [h1, hMn, hsqn, hv]

/-- `√y ≤ M` upgrades to `y ≤ M²` for `y ≥ 0`. -/
private lemma moderate_thresh {y Mv : ℝ} (hy : 0 ≤ y) (hMB : Real.sqrt y ≤ Mv) :
    y ≤ Mv ^ 2 := by
  nlinarith only [Real.sq_sqrt hy, Real.sqrt_nonneg y, hMB]

/-- A constant factor `K` is absorbed into `exp(−a x)` once `x ≥ 2 log K / a`. -/
private lemma moderate_absorb {K a x : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hx : 2 * Real.log K / a ≤ x) :
    K * Real.exp (-a * x) ≤ Real.exp (-(a / 2) * x) := by
  have hlog : Real.log K ≤ a * x / 2 := by
    rw [div_le_iff₀ ha] at hx; linarith only [hx]
  have hKle : K ≤ Real.exp (a * x / 2) := by
    calc K = Real.exp (Real.log K) := (Real.exp_log hK).symm
      _ ≤ _ := Real.exp_le_exp.2 hlog
  calc K * Real.exp (-a * x) ≤ Real.exp (a * x / 2) * Real.exp (-a * x) :=
        mul_le_mul_of_nonneg_right hKle (Real.exp_nonneg _)
    _ = Real.exp (-(a / 2) * x) := by rw [← Real.exp_add]; congr 1; ring

/-- Bookkeeping of the type-II exponent. -/
private lemma moderate_exp_eq {nv c d kv Lv a : ℝ} (hk : 0 < kv) (hL : 0 < Lv)
    (ha : a = c ^ 2 / (8 * kv * Lv ^ 2)) :
    -nv * (c * d / 2) ^ 2 / (2 * kv * Lv ^ 2) = -a * (nv * d ^ 2) := by
  subst ha
  have h1 : Lv ^ 2 ≠ 0 := by positivity
  have h2 : kv ≠ 0 := ne_of_gt hk
  field_simp
  ring

/-- Bookkeeping of the type-I exponent. -/
private lemma moderate_expI {Mn nR kv Lv : ℝ} (hn : 0 < nR) (hk : 0 < kv) (hL : 0 < Lv)
    (hMn : 0 ≤ Mn / nR) :
    -nR * Real.sqrt (Mn / nR) ^ 2 / (2 * kv * Lv ^ 2) = -Mn / (2 * kv * Lv ^ 2) := by
  rw [Real.sq_sqrt hMn]
  have h1 : Lv ^ 2 ≠ 0 := by positivity
  have h2 : kv ≠ 0 := ne_of_gt hk
  have h3 : nR ≠ 0 := ne_of_gt hn
  field_simp

/-- **The moderate-range tests** (vdV Lemma 10.3, first test sequence): measurable
`[0,1]`-valued tests `φₙ` with `P^n_{θ₀} φₙ → 0` and, for all large `n`,
`P^n_θ(1 − φₙ) ≤ exp(−c n ‖θ−θ₀‖²)` whenever `Mₙ/√n ≤ ‖θ − θ₀‖ ≤ ε`. -/
theorem exists_moderate_tests
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV Thm 10.1
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV Thm 10.1
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    {Mseq : ℕ → ℝ}
    -- USER-INPUT: the localization radii diverge; vdV Lemma 10.3 (`Mₙ → ∞`)
    (hM : Tendsto Mseq atTop atTop) :
    ∃ (φ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
      (∀ n, Measurable (φ n)) ∧ (∀ n ω, φ n ω ∈ Set.Icc (0 : ℝ) 1) ∧
      Tendsto (fun n => ∫ ω, φ n ω ∂(productMeasure M μ θ₀ n)) atTop (𝓝 0) ∧
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ θ, Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖ → ‖θ - θ₀‖ ≤ ε →
        ∫ ω, (1 - φ n ω) ∂(productMeasure M μ θ n)
          ≤ Real.exp (-c * n * ‖θ - θ₀‖ ^ 2) := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- degenerate parameter space: `θ = θ₀` always, so the alternative range is empty
    subst hk0
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hM.eventually_gt_atTop 0)
    refine ⟨fun _ _ => 0, 1, 1, one_pos, one_pos, fun _ => measurable_const,
      fun _ _ => by norm_num, ?_, max N₁ 1, ?_⟩
    · have hz : (fun n : ℕ => ∫ _ω : Fin n → 𝓧, (0 : ℝ) ∂(productMeasure M μ θ₀ n))
          = fun _ => 0 := by funext n; simp
      rw [hz]; exact tendsto_const_nhds
    · intro n hn θ hθ1 _
      exfalso
      have hd : ‖θ - θ₀‖ = 0 := by rw [EuclideanSpace.norm_eq]; simp
      have hMn : 0 < Mseq n := hN₁ n (le_trans (le_max_left _ _) hn)
      have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
      have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
      rw [hd] at hθ1
      exact absurd hθ1 (not_le.2 (div_pos hMn hsq))
  -- the nondegenerate case
  obtain ⟨L, ε, c, hL, hε, hc, hsep⟩ := truncScore_separation hPDF hsc hDQM hJ_pd hJ
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
  have hLsq : (0 : ℝ) < L ^ 2 := pow_pos hL 2
  have h8k : (0 : ℝ) < 8 * (k : ℝ) * L ^ 2 := by nlinarith
  have h2k : (0 : ℝ) < 2 * (k : ℝ) * L ^ 2 := by nlinarith
  obtain ⟨a, hadef, hapos⟩ : ∃ a : ℝ, a = c ^ 2 / (8 * (k : ℝ) * L ^ 2) ∧ 0 < a :=
    ⟨_, rfl, div_pos (pow_pos hc 2) h8k⟩
  -- measurability of the rejection region
  have hregmeas : ∀ n : ℕ, MeasurableSet {ω : Fin n → 𝓧 | Real.sqrt (Mseq n / n)
      ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ₀‖} := fun n =>
    measurableSet_le measurable_const
      (((measurable_bvmEmpTrunc hsc L n).sub measurable_const).norm)
  -- integrals of the indicator test
  have hindint : ∀ (n : ℕ) (θ : EuclideanSpace ℝ (Fin k)),
      ∫ ω, Set.indicator {ω : Fin n → 𝓧 | Real.sqrt (Mseq n / n)
          ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ₀‖} (fun _ => (1 : ℝ)) ω
        ∂(productMeasure M μ θ n)
      = (productMeasure M μ θ n).real {ω : Fin n → 𝓧 | Real.sqrt (Mseq n / n)
          ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ₀‖} := by
    intro n θ
    rw [integral_indicator_const (1 : ℝ) (hregmeas n), smul_eq_mul, mul_one]
  have hcomplint : ∀ (n : ℕ) (θ : EuclideanSpace ℝ (Fin k)),
      ∫ ω, (1 - Set.indicator {ω : Fin n → 𝓧 | Real.sqrt (Mseq n / n)
          ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ₀‖} (fun _ => (1 : ℝ)) ω)
        ∂(productMeasure M μ θ n)
      = (productMeasure M μ θ n).real {ω : Fin n → 𝓧 | Real.sqrt (Mseq n / n)
          ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ₀‖}ᶜ := by
    intro n θ
    have hpt : ∀ ω : Fin n → 𝓧, (1 : ℝ) - Set.indicator {ω : Fin n → 𝓧 |
          Real.sqrt (Mseq n / n) ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ₀‖}
            (fun _ => (1 : ℝ)) ω
        = Set.indicator {ω : Fin n → 𝓧 | Real.sqrt (Mseq n / n)
            ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ₀‖}ᶜ (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases h : ω ∈ {ω : Fin n → 𝓧 | Real.sqrt (Mseq n / n)
          ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ₀‖}
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_notMem ((Set.mem_compl_iff _ ω).not.2 (not_not_intro h))]
        norm_num
      · rw [Set.indicator_of_notMem h, Set.indicator_of_mem ((Set.mem_compl_iff _ ω).2 h)]
        norm_num
    simp only [hpt]
    rw [integral_indicator_const (1 : ℝ) (hregmeas n).compl, smul_eq_mul, mul_one]
  -- the threshold for `Mseq` beyond which everything is in force
  have hlog : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = max (4 / c ^ 2) (Real.sqrt (2 * Real.log (2 * (k : ℝ)) / a)) :=
    ⟨_, rfl⟩
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (hM.eventually_ge_atTop B)
  refine ⟨fun n => Set.indicator {ω : Fin n → 𝓧 | Real.sqrt (Mseq n / n)
      ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ₀‖} (fun _ => (1 : ℝ)),
    ε / 2, a / 2, by linarith, by linarith,
    fun n => measurable_const.indicator (hregmeas n), fun n ω => ?_, ?_, max N₁ 1, ?_⟩
  · simp only [Set.indicator_apply, Set.mem_Icc]
    split_ifs <;> norm_num
  · -- Type I error at `θ₀`
    refine squeeze_zero'
      (g := fun n => 2 * (k : ℝ) * Real.exp (-Mseq n / (2 * (k : ℝ) * L ^ 2)))
      (Filter.Eventually.of_forall fun n => ?_) ?_ ?_
    · rw [hindint n θ₀]; exact measureReal_nonneg
    · filter_upwards [hM.eventually_gt_atTop 0, Filter.eventually_ge_atTop 1] with n hMn hn1
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hrpos : 0 < Real.sqrt (Mseq n / n) := Real.sqrt_pos.2 (div_pos hMn hnR)
      have htail := truncScore_tail' hPDF hsc hL θ₀ hn1 hrpos
      rw [hindint n θ₀]
      refine htail.trans_eq ?_
      rw [moderate_expI hnR hkR hL (div_pos hMn hnR).le]
    · -- `2k exp(−Mₙ/(2kL²)) → 0`
      have hdiv : Tendsto (fun n => -Mseq n / (2 * (k : ℝ) * L ^ 2)) atTop atBot := by
        have h1 : Tendsto (fun n => Mseq n / (2 * (k : ℝ) * L ^ 2)) atTop atTop :=
          Filter.Tendsto.atTop_div_const h2k hM
        have h2 : (fun n => -Mseq n / (2 * (k : ℝ) * L ^ 2))
            = fun n => -(Mseq n / (2 * (k : ℝ) * L ^ 2)) := funext fun n => neg_div _ _
        rw [h2]
        exact tendsto_neg_atTop_atBot.comp h1
      have hex0 : Tendsto (fun n => Real.exp (-Mseq n / (2 * (k : ℝ) * L ^ 2))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hdiv
      simpa using Filter.Tendsto.const_mul (2 * (k : ℝ)) hex0
  · -- Type II error on the moderate range
    intro n hn θ hθlow hθhigh
    haveI : IsProbabilityMeasure (productMeasure M μ θ n) :=
      AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
        M μ hPDF θ n
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hsqn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnR
    have hBM : B ≤ Mseq n := hN₁ n (le_trans (le_max_left _ _) hn)
    have hB1 : 4 / c ^ 2 ≤ Mseq n := le_trans (by rw [hBdef]; exact le_max_left _ _) hBM
    have hB2 : Real.sqrt (2 * Real.log (2 * (k : ℝ)) / a) ≤ Mseq n :=
      le_trans (by rw [hBdef]; exact le_max_right _ _) hBM
    have hMpos : 0 < Mseq n :=
      lt_of_lt_of_le (div_pos (by norm_num) (pow_pos hc 2)) hB1
    have hd : 0 < ‖θ - θ₀‖ := lt_of_lt_of_le (div_pos hMpos hsqn) hθlow
    have hsep' : c * ‖θ - θ₀‖ ≤ ‖bvmTruncMean M μ sc L θ - bvmTruncMean M μ sc L θ₀‖ :=
      hsep θ (by linarith only [hθhigh, hε])
    have hthr : Real.sqrt (Mseq n / n) ≤ c * ‖θ - θ₀‖ / 2 :=
      moderate_arith hc hnR hMpos hB1 hθlow
    -- on the acceptance region the empirical mean is far from `P_θ sc^L`
    have hincl : {ω : Fin n → 𝓧 | Real.sqrt (Mseq n / n)
          ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ₀‖}ᶜ
        ⊆ {ω | c * ‖θ - θ₀‖ / 2 ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ‖} := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
      simp only [Set.mem_setOf_eq]
      have htri : ‖bvmTruncMean M μ sc L θ - bvmTruncMean M μ sc L θ₀‖
          ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ‖
            + ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ₀‖ := by
        have htmp := norm_sub_le_norm_sub_add_norm_sub
          (bvmTruncMean M μ sc L θ) (bvmEmpTrunc sc L n ω) (bvmTruncMean M μ sc L θ₀)
        rwa [norm_sub_rev (bvmTruncMean M μ sc L θ) (bvmEmpTrunc sc L n ω)] at htmp
      linarith only [htri, hω, hsep', hthr]
    have hspos : 0 < c * ‖θ - θ₀‖ / 2 := by
      have := mul_pos hc hd; linarith only [this]
    have htail := truncScore_tail' hPDF hsc hL θ hn1 hspos
    rw [hcomplint n θ]
    have hmono : (productMeasure M μ θ n).real
        {ω : Fin n → 𝓧 | Real.sqrt (Mseq n / n)
          ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ₀‖}ᶜ
        ≤ (productMeasure M μ θ n).real
          {ω | c * ‖θ - θ₀‖ / 2 ≤ ‖bvmEmpTrunc sc L n ω - bvmTruncMean M μ sc L θ‖} :=
      measureReal_mono hincl (measure_ne_top _ _)
    refine (hmono.trans htail).trans ?_
    rw [moderate_exp_eq (d := ‖θ - θ₀‖) hkR hL hadef]
    -- `n‖θ−θ₀‖² ≥ Mₙ²` and `Mₙ² ≥ 2 log(2k)/a`
    have hnd : Mseq n ^ 2 ≤ (n : ℝ) * ‖θ - θ₀‖ ^ 2 := moderate_arith2 hnR hMpos hθlow
    have hnn : (0 : ℝ) ≤ 2 * Real.log (2 * (k : ℝ)) / a := by
      have hl : (0 : ℝ) ≤ Real.log (2 * (k : ℝ)) :=
        Real.log_nonneg (by linarith only [hk1] : (1 : ℝ) ≤ 2 * (k : ℝ))
      positivity
    have hMB2 : 2 * Real.log (2 * (k : ℝ)) / a ≤ Mseq n ^ 2 := moderate_thresh hnn hB2
    have hfin : 2 * Real.log (2 * (k : ℝ)) / a ≤ (n : ℝ) * ‖θ - θ₀‖ ^ 2 :=
      le_trans hMB2 hnd
    have := moderate_absorb (K := 2 * (k : ℝ)) (a := a) (x := (n : ℝ) * ‖θ - θ₀‖ ^ 2)
      hlog hapos hfin
    refine this.trans_eq ?_
    congr 1
    ring

end StatLean.Bayesian
