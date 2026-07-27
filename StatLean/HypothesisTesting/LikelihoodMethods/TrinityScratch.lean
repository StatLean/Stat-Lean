import StatLean.HypothesisTesting.LikelihoodMethods.TrinityChiSquared

/-!
# Scratch: bricks for the affine composite likelihood-ratio reduction

Development file for `logLR_affine_sub_scoreDiff_tendstoInMeasure`.  Everything proved here
is merged into `TrinityChiSquared.lean`; this file is deleted afterwards.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open AsymptoticStatistics AsymptoticStatistics.AsymptoticRepresentation
open scoped RealInnerProductSpace ENNReal Matrix BoundedContinuousFunction MatrixOrder

namespace StatLean.HypothesisTesting.Scratch

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {k : ℕ}

/-! ### Brick 1: the restricted model at the chart point is the full model at `θ₀` -/

lemma productMeasure_restrictFamily {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k))
    (hθ₀ : θ₀ = a + B β₀) (n : ℕ) :
    productMeasure (restrictFamily M a B) μ β₀ n = productMeasure M μ θ₀ n := by
  rw [hθ₀]; rfl

lemma isPDFOf_restrictFamily {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hPDF : IsPDFOf M μ) :
    IsPDFOf (restrictFamily M a B) μ :=
  ⟨fun β => hPDF.density_integral_eq_one _, fun β => hPDF.density_integrable _⟩

/-! ### Brick 2: positive definiteness of the pulled-back information matrix -/

lemma posDef_pullback {m : ℕ}
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hB : Function.Injective B)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (hJBrel : ∀ u v : EuclideanSpace ℝ (Fin m),
      ⟪u, mulVecE JB v⟫ = ⟪B u, mulVecE J (B v)⟫) :
    JB.PosDef := by
  classical
  have hcomm : ∀ x y : EuclideanSpace ℝ (Fin k),
      ⟪mulVecE J x, y⟫ = ⟪x, mulVecE J y⟫ := by
    intro x y
    rw [real_inner_comm, mulVecE_apply_clm, mulVecE_apply_clm,
      Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
    have hAt : Jᵀ = J := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hJ_pd.isHermitian
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hAt, dotProduct_comm]
  have hsymm : ∀ u v : EuclideanSpace ℝ (Fin m),
      ⟪u, mulVecE JB v⟫ = ⟪v, mulVecE JB u⟫ := by
    intro u v
    rw [hJBrel u v, hJBrel v u, ← hcomm (B u) (B v), real_inner_comm]
  have hpos : ∀ u : EuclideanSpace ℝ (Fin m), u ≠ 0 → 0 < ⟪u, mulVecE JB u⟫ := by
    intro u hu
    rw [hJBrel u u, mulVecE_apply_clm, Matrix.inner_toEuclideanCLM]
    have hBu : B u ≠ 0 := fun h => hu (hB (by rw [h, map_zero]))
    have hne : (B u).ofLp ≠ 0 := by
      intro h
      exact hBu (by ext i; simpa using congrFun h i)
    simpa using hJ_pd.dotProduct_mulVec_pos hne
  -- Transport to plain vectors.
  have hsymm' : ∀ x y : Fin m → ℝ,
      dotProduct x (JB.mulVec y) = dotProduct y (JB.mulVec x) := by
    intro x y
    have h := hsymm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simp only [mulVecE_apply_clm, Matrix.inner_toEuclideanCLM] at h
    simpa using h
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    have h := hsymm' (Pi.single j (1 : ℝ)) (Pi.single i (1 : ℝ))
    simpa [Matrix.conjTranspose_apply, Matrix.mulVec_single, single_dotProduct] using h
  · have hx' : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m)) ≠ 0 := by
      intro h
      exact hx (by ext i; simpa using congrFun (congrArg WithLp.ofLp h) i)
    have h := hpos (WithLp.toLp 2 x) hx'
    simp only [mulVecE_apply_clm, Matrix.inner_toEuclideanCLM] at h
    simpa using h

/-! ### Brick 3: a.e. non-vanishing of the base density along the sample -/

lemma ae_forall_density_ne_zero
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k)) (n : ℕ) :
    ∀ᵐ ω ∂(productMeasure M μ θ₀ n), ∀ i, M.density θ₀ (ω i) ≠ 0 := by
  classical
  set ν : Measure 𝓧 := μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x) with hν
  haveI hνprob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [hν, MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hPDF.density_integrable θ₀)
        (Filter.Eventually.of_forall (M.density_nonneg θ₀)),
      hPDF.density_integral_eq_one θ₀, ENNReal.ofReal_one]
  set S : Set 𝓧 := {x | M.density θ₀ x = 0} with hS
  have hSmeas : MeasurableSet S := (M.density_meas θ₀) (measurableSet_singleton 0)
  have hS0 : ν S = 0 := by
    rw [hν, MeasureTheory.withDensity_apply _ hSmeas]
    refine le_antisymm ?_ (zero_le _)
    refine le_of_eq ?_
    rw [MeasureTheory.setLIntegral_congr_fun hSmeas (g := fun _ => (0 : ℝ≥0∞))
      (fun x hx => by simp [hS, Set.mem_setOf_eq.mp hx])]
    simp
  rw [MeasureTheory.ae_all_iff]
  intro i
  rw [MeasureTheory.ae_iff]
  have hset : {ω : Fin n → 𝓧 | ¬ M.density θ₀ (ω i) ≠ 0}
      = Set.univ.pi (fun j => if j = i then S else Set.univ) := by
    ext ω
    simp only [Set.mem_setOf_eq, not_not, Set.mem_univ_pi]
    constructor
    · intro h j
      by_cases hj : j = i
      · subst hj; simpa [hS] using h
      · simp [hj]
    · intro h
      simpa [hS] using h i
  rw [hset, productMeasure, MeasureTheory.Measure.pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simpa using hS0

/-! ### Brick 4: splitting the affine log-likelihood ratio at `θ₀` -/

lemma logLRStatistic_affine_split {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k))
    (hθ₀ : θ₀ = a + B β₀)
    (hsupp : ∀ (θ : EuclideanSpace ℝ (Fin k)) (x : 𝓧),
      M.density θ₀ x ≠ 0 → M.density θ x ≠ 0)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin m))
    (n : ℕ) (ω : Fin n → 𝓧) (hω : ∀ i, M.density θ₀ (ω i) ≠ 0) :
    logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω
      = logLRStatistic M est (fun _ _ => θ₀) n ω
        - logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω := by
  have hden : ∀ (β : EuclideanSpace ℝ (Fin m)) (x : 𝓧),
      (restrictFamily M a B).density β x = M.density (a + B β) x := fun _ _ => rfl
  have key : ∀ i : Fin n,
      Real.log (M.density (est n ω) (ω i) / M.density (a + B (est₀ n ω)) (ω i))
        = Real.log (M.density (est n ω) (ω i) / M.density θ₀ (ω i))
          - Real.log (M.density (a + B (est₀ n ω)) (ω i) / M.density θ₀ (ω i)) := by
    intro i
    have hD := hω i
    have hA := hsupp (est n ω) (ω i) hD
    have hC := hsupp (a + B (est₀ n ω)) (ω i) hD
    rw [Real.log_div hA hC, Real.log_div hA hD, Real.log_div hC hD]
    ring
  simp only [logLRStatistic, hden, ← hθ₀]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => key i)

/-! ### Brick 5: the two-point envelope transports to the restricted chart -/

lemma henv_restrict {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k))
    (hθ₀ : θ₀ = a + B β₀)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (hℓB : ℓB = fun x => ContinuousLinearMap.adjoint B (ℓ x))
    (Menv : 𝓧 → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (henv : ∀ θ θ' : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ‖θ' - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x / M.density θ₀ x)
          - Real.log (M.density θ' x / M.density θ₀ x) - ⟪θ - θ', ℓ x⟫|
        ≤ Menv x * (‖θ - θ₀‖ + ‖θ' - θ₀‖) * ‖θ - θ'‖) :
    ∀ β β' : EuclideanSpace ℝ (Fin m), ‖β - β₀‖ ≤ δ / (‖B‖ + 1) →
      ‖β' - β₀‖ ≤ δ / (‖B‖ + 1) → ∀ x : 𝓧,
      |Real.log ((restrictFamily M a B).density β x / (restrictFamily M a B).density β₀ x)
          - Real.log ((restrictFamily M a B).density β' x
              / (restrictFamily M a B).density β₀ x)
          - ⟪β - β', ℓB x⟫|
        ≤ |Menv x| * ‖B‖ ^ 2 * (‖β - β₀‖ + ‖β' - β₀‖) * ‖β - β'‖ := by
  intro β β' hβ hβ' x
  have hden : ∀ (γ : EuclideanSpace ℝ (Fin m)) (y : 𝓧),
      (restrictFamily M a B).density γ y = M.density (a + B γ) y := fun _ _ => rfl
  have hb0 : (0 : ℝ) ≤ ‖B‖ := norm_nonneg _
  -- the two parameters in the full space
  have hsub : ∀ γ γ' : EuclideanSpace ℝ (Fin m),
      (a + B γ) - (a + B γ') = B (γ - γ') := by
    intro γ γ'
    rw [map_sub]
    abel
  have hbound : ∀ γ : EuclideanSpace ℝ (Fin m), ‖γ - β₀‖ ≤ δ / (‖B‖ + 1) →
      ‖(a + B γ) - θ₀‖ ≤ δ := by
    intro γ hγ
    have h1 : (a + B γ) - θ₀ = B (γ - β₀) := by rw [hθ₀]; exact hsub γ β₀
    have h2 : ‖B (γ - β₀)‖ ≤ ‖B‖ * ‖γ - β₀‖ := B.le_opNorm _
    have h3 : ‖B‖ * ‖γ - β₀‖ ≤ ‖B‖ * (δ / (‖B‖ + 1)) :=
      mul_le_mul_of_nonneg_left hγ hb0
    have h4 : ‖B‖ * (δ / (‖B‖ + 1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    rw [h1]; linarith
  have h1 := hbound β hβ
  have h2 := hbound β' hβ'
  have hinner : ⟪β - β', ℓB x⟫ = ⟪(a + B β) - (a + B β'), ℓ x⟫ := by
    rw [hsub β β', hℓB, real_inner_comm, ContinuousLinearMap.adjoint_inner_left,
      real_inner_comm]
  have hkey := henv (a + B β) (a + B β') h1 h2 x
  simp only [hden, ← hθ₀, hinner]
  refine hkey.trans ?_
  -- transport the right-hand side to the chart
  have hnb : ‖(a + B β) - θ₀‖ ≤ ‖B‖ * ‖β - β₀‖ := by
    have h : (a + B β) - θ₀ = B (β - β₀) := by rw [hθ₀]; exact hsub β β₀
    rw [h]; exact B.le_opNorm _
  have hnb' : ‖(a + B β') - θ₀‖ ≤ ‖B‖ * ‖β' - β₀‖ := by
    have h : (a + B β') - θ₀ = B (β' - β₀) := by rw [hθ₀]; exact hsub β' β₀
    rw [h]; exact B.le_opNorm _
  have hnd : ‖(a + B β) - (a + B β')‖ ≤ ‖B‖ * ‖β - β'‖ := by
    rw [hsub β β']; exact B.le_opNorm _
  have hMle : Menv x ≤ |Menv x| := le_abs_self _
  have hM0 : (0 : ℝ) ≤ |Menv x| := abs_nonneg _
  have hp : (0 : ℝ) ≤ ‖β - β₀‖ := norm_nonneg _
  have hq : (0 : ℝ) ≤ ‖β' - β₀‖ := norm_nonneg _
  have hr : (0 : ℝ) ≤ ‖β - β'‖ := norm_nonneg _
  have hX : (0 : ℝ) ≤ ‖(a + B β) - θ₀‖ + ‖(a + B β') - θ₀‖ := by positivity
  have hY : (0 : ℝ) ≤ ‖(a + B β) - (a + B β')‖ := norm_nonneg _
  calc Menv x * (‖(a + B β) - θ₀‖ + ‖(a + B β') - θ₀‖) * ‖(a + B β) - (a + B β')‖
      ≤ |Menv x| * (‖B‖ * ‖β - β₀‖ + ‖B‖ * ‖β' - β₀‖) * (‖B‖ * ‖β - β'‖) := by
        have hstep1 : Menv x * (‖(a + B β) - θ₀‖ + ‖(a + B β') - θ₀‖)
            ≤ |Menv x| * (‖B‖ * ‖β - β₀‖ + ‖B‖ * ‖β' - β₀‖) := by
          nlinarith
        have hstep2 : (0 : ℝ) ≤ |Menv x| * (‖B‖ * ‖β - β₀‖ + ‖B‖ * ‖β' - β₀‖) := by
          positivity
        nlinarith
    _ = |Menv x| * ‖B‖ ^ 2 * (‖β - β₀‖ + ‖β' - β₀‖) * ‖β - β'‖ := by ring

/-! ### Brick 6: assembly (the two simple-null conclusions as hypotheses) -/

lemma assemble {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (β₀ : EuclideanSpace ℝ (Fin m)) (hθ₀ : θ₀ = a + B β₀)
    (hsupp : ∀ (θ : EuclideanSpace ℝ (Fin k)) (x : 𝓧),
      M.density θ₀ x ≠ 0 → M.density θ x ≠ 0)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (J : Matrix (Fin k) (Fin k) ℝ)
    (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m)) (JB : Matrix (Fin m) (Fin m) ℝ)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin m))
    (h1 : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 |
          ε ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|})
        atTop (𝓝 0))
    (h2 : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure (restrictFamily M a B) μ β₀ n).real
        {ω : Fin n → 𝓧 |
          ε ≤ |logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
            - scoreStatistic JB ℓB n ω|})
        atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω
          - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)|})
        atTop (𝓝 0) := by
  intro ε hε
  have hprod := fun n : ℕ => productMeasure_restrictFamily M μ a B β₀ θ₀ hθ₀ n
  have h2' : Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
      {ω : Fin n → 𝓧 |
        ε / 2 ≤ |logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
          - scoreStatistic JB ℓB n ω|}) atTop (𝓝 0) := by
    have := h2 (ε / 2) (by positivity)
    simpa only [hprod] using this
  refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_)
    (by simpa using (h1 (ε / 2) (by positivity)).add h2')
  -- the bad event is contained in the two half-events together with the null set where the
  -- base density vanishes somewhere along the sample
  set A1 : Set (Fin n → 𝓧) := {ω : Fin n → 𝓧 |
    ε / 2 ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|} with hA1
  set A2 : Set (Fin n → 𝓧) := {ω : Fin n → 𝓧 |
    ε / 2 ≤ |logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
      - scoreStatistic JB ℓB n ω|} with hA2
  set G : Set (Fin n → 𝓧) := {ω : Fin n → 𝓧 | ∀ i, M.density θ₀ (ω i) ≠ 0} with hG
  have hGnull : (productMeasure M μ θ₀ n).real Gᶜ = 0 := by
    have hae := ae_forall_density_ne_zero M μ hPDF θ₀ n
    rw [MeasureTheory.ae_iff] at hae
    simp only [measureReal_def]
    rw [show Gᶜ = {ω : Fin n → 𝓧 | ¬ ∀ i, M.density θ₀ (ω i) ≠ 0} from rfl, hae]
    simp
  have hincl : {ω : Fin n → 𝓧 | ε ≤ |logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω
      - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)|} ⊆ A1 ∪ A2 ∪ Gᶜ := by
    intro ω hω
    by_cases hg : ω ∈ G
    · have hsplit := logLRStatistic_affine_split M a B β₀ θ₀ hθ₀ hsupp est est₀ n ω hg
      simp only [Set.mem_setOf_eq, hsplit] at hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_compl_iff, hA1, hA2, Set.mem_setOf_eq, not_or,
        not_le] at hcon
      obtain ⟨⟨hc1, hc2⟩, -⟩ := hcon
      have : |logLRStatistic M est (fun _ _ => θ₀) n ω
            - logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
            - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)|
          ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|
            + |logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
              - scoreStatistic JB ℓB n ω| := by
        have heq : logLRStatistic M est (fun _ _ => θ₀) n ω
              - logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
              - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)
            = (logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω)
              - (logLRStatistic (restrictFamily M a B) est₀ (fun _ _ => β₀) n ω
                - scoreStatistic JB ℓB n ω) := by ring
        rw [heq]
        exact abs_sub _ _
      linarith
    · exact Or.inr hg
  have hmono := measureReal_mono (μ := productMeasure M μ θ₀ n) hincl (measure_ne_top _ _)
  have hu1 := measureReal_union_le (μ := productMeasure M μ θ₀ n) (A1 ∪ A2) Gᶜ
  have hu2 := measureReal_union_le (μ := productMeasure M μ θ₀ n) A1 A2
  linarith

end StatLean.HypothesisTesting.Scratch
