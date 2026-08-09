import StatLean.TimeSeries.Threshold.TAR
import StatLean.TimeSeries.ForMathlib.Markov.TwoSidedChain

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

set_option linter.unusedSectionVars false

namespace StatLean.TimeSeries

example {P : ℕ} : StandardBorelSpace (Fin (P + 1) → ℝ) := by infer_instance
example {P : ℕ} : Nonempty (Fin (P + 1) → ℝ) := by infer_instance

/-- The nonlinear-AR kernel as a pushforward of the innovation law. -/
lemma nlARKernel_apply {P : ℕ} {f : (Fin (P + 1) → ℝ) → ℝ} (hf : Measurable f)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : Fin (P + 1) → ℝ) :
    nlARKernel f ν x
      = ν.map (fun e => (Fin.cons (f x + e) (fun i => x i.castSucc) : Fin (P + 1) → ℝ)) := by
  have hmeas : Measurable fun xe : (Fin (P + 1) → ℝ) × ℝ =>
      (Fin.cons (f xe.1 + xe.2) (fun i => xe.1 i.castSucc) : Fin (P + 1) → ℝ) := by
    rw [measurable_pi_iff]
    refine Fin.cases ?_ ?_
    · simpa using (hf.comp measurable_fst).add measurable_snd
    · exact fun i => by simpa using (measurable_pi_apply i.castSucc).comp measurable_fst
  rw [nlARKernel, Kernel.map_apply _ hmeas, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hmeas measurable_prodMk_left]
  rfl

lemma compProd_map_left' {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) [SFinite μ] {g : α → β} (hg : Measurable g)
    (η : Kernel β γ) [IsSFiniteKernel η] :
    (μ.map g) ⊗ₘ η = (μ ⊗ₘ (η.comap g hg)).map (Prod.map g id) := by
  have hmap : Measurable (Prod.map g (id : γ → γ)) := hg.prodMap measurable_id
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hmap hs,
    Measure.compProd_apply (hs.preimage hmap),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hg]
  rfl

/-- The set of state pairs `(x, y)` in which `y` is `x` shifted by one coordinate. -/
def shiftSet (P : ℕ) : Set ((Fin (P + 1) → ℝ) × (Fin (P + 1) → ℝ)) :=
  {p | ∀ j : Fin P, p.2 j.succ = p.1 j.castSucc}

lemma measurableSet_shiftSet (P : ℕ) : MeasurableSet (shiftSet P) := by
  have h : shiftSet P = ⋂ j : Fin P, {p : (Fin (P + 1) → ℝ) × (Fin (P + 1) → ℝ) |
      p.2 j.succ = p.1 j.castSucc} := by
    ext p; simp [shiftSet]
  rw [h]
  refine MeasurableSet.iInter fun j => ?_
  exact measurableSet_eq_fun ((measurable_pi_apply _).comp measurable_snd)
    ((measurable_pi_apply _).comp measurable_fst)

/-- The one-step shift structure of the nonlinear-AR kernel, as a null set. -/
lemma nlAR_pair_shift {P : ℕ} {f : (Fin (P + 1) → ℝ) → ℝ} (hf : Measurable f)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (F : Measure (Fin (P + 1) → ℝ))
    [IsProbabilityMeasure F] :
    (F ⊗ₘ nlARKernel f ν) (shiftSet P)ᶜ = 0 := by
  haveI := isMarkovKernel_nlARKernel hf ν
  have hA : MeasurableSet (shiftSet P) := measurableSet_shiftSet P
  rw [Measure.compProd_apply hA.compl]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards with x
  have hm : Measurable fun e : ℝ =>
      (Fin.cons (f x + e) (fun i => x i.castSucc) : Fin (P + 1) → ℝ) := by
    rw [measurable_pi_iff]
    refine Fin.cases ?_ ?_
    · simpa using measurable_const.add measurable_id
    · exact fun i => by simp
  rw [nlARKernel_apply hf ν x,
    Measure.map_apply hm (measurable_prodMk_left hA.compl)]
  convert measure_empty (μ := ν)
  ext e
  simp only [Set.mem_preimage, Set.mem_compl_iff, shiftSet, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false, not_not]
  intro j
  simp

/-- The two-coordinate window law is the one-step pair law. -/
lemma chainWindowLaw_one {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) [IsProbabilityMeasure π] :
    (chainWindowLaw κ π 1).map (fun w : Fin 2 → S => (w 0, w 1)) = π ⊗ₘ κ := by
  have hc : Measurable (fun (x : S) (_ : Fin 1) => x) :=
    measurable_pi_lambda _ fun _ => measurable_id
  have hsnoc : Measurable fun wx : (Fin 1 → S) × S => (Fin.snoc wx.1 wx.2 : Fin 2 → S) := by
    rw [measurable_pi_iff]
    refine Fin.lastCases ?_ ?_
    · simpa using measurable_snd
    · exact fun i => by simpa using (measurable_pi_apply i).comp measurable_fst
  have hsel : Measurable fun w : Fin 2 → S => (w 0, w 1) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hstep : chainWindowLaw κ π 1
      = ((π.map (fun (x : S) (_ : Fin 1) => x)) ⊗ₘ
          (κ.comap (fun w : Fin 1 → S => w (Fin.last 0)) (measurable_pi_apply _))).map
        (fun wx => (Fin.snoc wx.1 wx.2 : Fin 2 → S)) := rfl
  rw [hstep, compProd_map_left' _ hc,
    Measure.map_map hsnoc (hc.prodMap measurable_id),
    Measure.map_map hsel ((hsnoc.comp (hc.prodMap measurable_id)))]
  have hid : ((fun w : Fin 2 → S => (w 0, w 1)) ∘
      ((fun wx : (Fin 1 → S) × S => (Fin.snoc wx.1 wx.2 : Fin 2 → S)) ∘
        Prod.map (fun (x : S) (_ : Fin 1) => x) id)) = id := by
    funext p
    simp [Fin.snoc]
  rw [hid, Measure.map_id]
  rfl

/-- **Kernel → two-sided process** for the nonlinear autoregression. -/
theorem tar_stationary {P : ℕ}
    {f : (Fin (P + 1) → ℝ) → ℝ} (hf : Measurable f)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν2 : MemLp id 2 ν) (hνmean : ∫ e, e ∂ν = 0)
    {σ0 : ℝ} (hσ : 0 < σ0) (hνvar : variance id ν = σ0 ^ 2)
    {F : Measure (Fin (P + 1) → ℝ)} [IsProbabilityMeasure F]
    (hinv : (nlARKernel f ν).Invariant F) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' ε' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧ (∀ t, Measurable (X' t)) ∧ IsIIDNoise ε' 1 μ' ∧
        (∀ t : ℤ, Indep (MeasurableSpace.comap (ε' t) inferInstance) (sigmaLT X' t) μ') ∧
        (∀ t : ℤ, X' t =ᵐ[μ']
          fun ω => f (fun j : Fin (P + 1) => X' (t - 1 - (j : ℕ)) ω) + σ0 * ε' t ω) ∧
        IsStrictlyStationary X' μ' := by
  haveI := isMarkovKernel_nlARKernel hf ν
  obtain ⟨Ω', mΩ', μ', Y, hprob, hYmeas, hwin⟩ :=
    exists_twoSided_stationary_chain (nlARKernel f ν) F hinv
  have hX'meas : ∀ t : ℤ, Measurable fun ω => Y t ω 0 :=
    fun t => (measurable_pi_apply 0).comp (hYmeas t)
  -- the one-step pair law
  have hsel : Measurable fun w : Fin 2 → (Fin (P + 1) → ℝ) => (w 0, w 1) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hpair : ∀ t : ℤ, μ'.map (fun ω => (Y (t - 1) ω, Y t ω)) = F ⊗ₘ nlARKernel f ν := by
    intro t
    have hbig : Measurable fun ω (i : Fin 2) => Y (t - 1 + (i : ℕ)) ω :=
      measurable_pi_lambda _ fun _ => hYmeas _
    have h2 := congrArg
      (fun μ => Measure.map (fun w : Fin 2 → (Fin (P + 1) → ℝ) => (w 0, w 1)) μ)
      (hwin (t - 1) 1)
    simp only at h2
    rw [Measure.map_map hsel hbig, chainWindowLaw_one] at h2
    rw [← h2]
    congr 1
    funext ω
    simp
  -- one-step coordinate shift, almost surely
  have hshift : ∀ t : ℤ, ∀ᵐ ω ∂μ', ∀ j : Fin P,
      Y t ω j.succ = Y (t - 1) ω j.castSucc := by
    intro t
    have hpm : Measurable fun ω => (Y (t - 1) ω, Y t ω) := (hYmeas _).prodMk (hYmeas _)
    have hnull := nlAR_pair_shift (ν := ν) hf F
    rw [← hpair t, Measure.map_apply hpm (measurableSet_shiftSet P).compl] at hnull
    have hae : ∀ᵐ ω ∂μ', (Y (t - 1) ω, Y t ω) ∈ shiftSet P := by
      rw [ae_iff]; exact hnull
    filter_upwards [hae] with ω hω
    simpa [shiftSet] using hω
  have hshiftAll : ∀ᵐ ω ∂μ', ∀ (t : ℤ) (j : Fin P),
      Y t ω j.succ = Y (t - 1) ω j.castSucc := ae_all_iff.mpr hshift
  -- the state vector is the past of its own first coordinate
  have hcons : ∀ᵐ ω ∂μ', ∀ (t : ℤ) (j : Fin (P + 1)), Y t ω j = Y (t - (j : ℕ)) ω 0 := by
    filter_upwards [hshiftAll] with ω hω
    have key : ∀ (j : ℕ) (hj : j < P + 1) (t : ℤ),
        Y t ω ⟨j, hj⟩ = Y (t - (j : ℤ)) ω 0 := by
      intro j
      induction j with
      | zero => intro hj t; simp
      | succ j ih =>
        intro hj t
        have hjP : j < P := by omega
        have h1 : (⟨j + 1, hj⟩ : Fin (P + 1)) = (⟨j, hjP⟩ : Fin P).succ := by
          apply Fin.ext; simp
        have h2 : ((⟨j, hjP⟩ : Fin P).castSucc : Fin (P + 1)) = ⟨j, by omega⟩ := by
          apply Fin.ext; simp
        rw [h1, hω t ⟨j, hjP⟩, h2, ih (by omega) (t - 1)]
        congr 1
        push_cast
        ring
    intro t j
    have := key (j : ℕ) j.isLt t
    simpa using this
  refine ⟨Ω', mΩ', μ', (fun t ω => Y t ω 0),
    (fun t ω => (Y t ω 0 - f (Y (t - 1) ω)) / σ0), hprob, hX'meas, ?_, ?_, ?_, ?_⟩
  · sorry
  · sorry
  · -- the recursion
    intro t
    filter_upwards [hcons] with ω hω
    have hv : (fun j : Fin (P + 1) => Y (t - 1 - (j : ℕ)) ω 0) = Y (t - 1) ω := by
      funext j
      have := hω (t - 1) j
      rw [← this]
    simp only [hv]
    field_simp
    ring
  · -- strict stationarity
    rw [isStrictlyStationary_iff_window hX'meas]
    intro n k
    cases n with
    | zero =>
      congr 1
      funext ω i
      exact i.elim0
    | succ n =>
      have hsel2 : Measurable fun w : Fin (n + 1) → (Fin (P + 1) → ℝ) =>
          fun i : Fin (n + 1) => w i 0 :=
        measurable_pi_lambda _ fun _ => (measurable_pi_apply 0).comp (measurable_pi_apply _)
      have hstep : ∀ c : ℤ,
          (μ'.map fun ω (i : Fin (n + 1)) => Y ((i : ℕ) + 1 + c) ω 0)
            = (chainWindowLaw (nlARKernel f ν) F n).map
              (fun w : Fin (n + 1) → (Fin (P + 1) → ℝ) => fun i : Fin (n + 1) => w i 0) := by
        intro c
        have hbig : Measurable fun ω (i : Fin (n + 1)) => Y (1 + c + (i : ℕ)) ω :=
          measurable_pi_lambda _ fun _ => hYmeas _
        have h2 := congrArg
          (fun μ => Measure.map (fun w : Fin (n + 1) → (Fin (P + 1) → ℝ) =>
            fun i : Fin (n + 1) => w i 0) μ) (hwin (1 + c) n)
        simp only at h2
        rw [Measure.map_map hsel2 hbig] at h2
        rw [← h2]
        congr 1
        funext ω
        funext i
        show Y (((i : ℕ) : ℤ) + 1 + c) ω 0 = Y (1 + c + ((i : ℕ) : ℤ)) ω 0
        rw [show ((i : ℕ) : ℤ) + 1 + c = 1 + c + ((i : ℕ) : ℤ) from by ring]
      rw [hstep k, ← hstep 0]
      congr 1

end StatLean.TimeSeries
