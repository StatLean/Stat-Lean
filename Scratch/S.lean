import StatLean.TimeSeries.ForMathlib.Markov.TwoSidedChain

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

set_option linter.unusedSectionVars false

namespace StatLean.TimeSeries

instance instMarkovReverseKernel {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [Nonempty S] (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) [IsProbabilityMeasure π] :
    IsMarkovKernel (reverseKernel κ π) := by
  unfold reverseKernel; infer_instance

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]

/-- `μ.map g ⊗ₘ η` seen on the source space. -/
lemma compProd_map_left {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) [SFinite μ] {g : α → β} (hg : Measurable g)
    (η : Kernel β γ) [IsSFiniteKernel η] :
    (μ.map g) ⊗ₘ η = (μ ⊗ₘ (η.comap g hg)).map (Prod.map g id) := by
  have hmap : Measurable (Prod.map g (id : γ → γ)) := hg.prodMap measurable_id
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hmap hs,
    Measure.compProd_apply (hs.preimage hmap),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hg]
  rfl

-- the coordinate of `Fin.cons x w` at the last index
lemma measurable_consLast (k : ℕ) :
    Measurable fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S) (Fin.last k) := by
  cases k with
  | zero => simpa using measurable_fst
  | succ k => simpa using (measurable_pi_apply (Fin.last k)).comp measurable_snd

lemma measurable_finCons (k : ℕ) :
    Measurable fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S) := by
  rw [measurable_pi_iff]
  refine Fin.cases ?_ ?_
  · simpa using measurable_fst
  · exact fun i => by simpa using (measurable_pi_apply i).comp measurable_snd

lemma measurable_finSnoc' (k : ℕ) :
    Measurable fun p : (Fin k → S) × S => (Fin.snoc p.1 p.2 : Fin (k + 1) → S) := by
  rw [measurable_pi_iff]
  refine Fin.lastCases ?_ ?_
  · simpa using measurable_snd
  · exact fun i => by simpa using (measurable_pi_apply i).comp measurable_fst

/-- The strict-future window kernel: `chainWindowKernel κ k x` is the law of
`(X₁, …, X_k)` for the chain started at `x`. -/
noncomputable def chainWindowKernel (κ : Kernel S S) : (k : ℕ) → Kernel S (Fin k → S)
  | 0 => Kernel.deterministic (fun _ => Fin.elim0) measurable_const
  | (k + 1) =>
      ((chainWindowKernel κ k) ⊗ₖ
        (κ.comap (fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S) (Fin.last k))
          (measurable_consLast k))).map (fun p => Fin.snoc p.1 p.2)

instance instMarkovChainWindowKernel (κ : Kernel S S) [IsMarkovKernel κ] (k : ℕ) :
    IsMarkovKernel (chainWindowKernel κ k) := by
  induction k with
  | zero => rw [chainWindowKernel]; infer_instance
  | succ k ih =>
      rw [chainWindowKernel]
      exact Kernel.IsMarkovKernel.map _ (measurable_finSnoc' k)



section K1
variable (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) [IsProbabilityMeasure π]

/-- (K1) The window law is the start law composed with the strict-future window kernel. -/
theorem chainWindowLaw_eq_compProd (k : ℕ) :
    chainWindowLaw κ π k
      = (π ⊗ₘ chainWindowKernel κ k).map (fun p => (Fin.cons p.1 p.2 : Fin (k + 1) → S)) := by
  induction k with
  | zero =>
    rw [chainWindowLaw, chainWindowKernel, Measure.compProd_deterministic,
      Measure.map_map (measurable_finCons 0) (by fun_prop)]
    refine congrArg (fun f => Measure.map f π) (funext fun x => funext fun i => ?_)
    refine Fin.cases ?_ (fun j => j.elim0) i
    simp
  | succ k ih =>
    haveI := isProbabilityMeasure_chainWindowLaw κ π k
    set η : Kernel (S × (Fin k → S)) S :=
      κ.comap (fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S) (Fin.last k))
        (measurable_consLast k) with hη
    have hcomap : (κ.comap (fun w : Fin (k + 1) → S => w (Fin.last k))
        (measurable_pi_apply _)).comap (fun p : S × (Fin k → S) =>
          (Fin.cons p.1 p.2 : Fin (k + 1) → S)) (measurable_finCons k) = η := by
      rw [hη]; rfl
    have hG : Measurable fun p : (S × (Fin k → S)) × S =>
        (Fin.cons p.1.1 (Fin.snoc p.1.2 p.2) : Fin (k + 1 + 1) → S) :=
      (measurable_finCons (k + 1)).comp
        (measurable_fst.fst.prodMk ((measurable_finSnoc' k).comp (measurable_fst.snd.prodMk
          measurable_snd)))
    calc chainWindowLaw κ π (k + 1)
        = ((chainWindowLaw κ π k) ⊗ₘ (κ.comap (fun w => w (Fin.last k))
            (measurable_pi_apply _))).map (fun wx => Fin.snoc wx.1 wx.2) := rfl
      _ = (((π ⊗ₘ chainWindowKernel κ k) ⊗ₘ η).map
            (Prod.map (fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S)) id)).map
            (fun wx => Fin.snoc wx.1 wx.2) := by
            rw [ih, compProd_map_left _ (measurable_finCons k), hcomap]
      _ = ((π ⊗ₘ chainWindowKernel κ k) ⊗ₘ η).map
            (fun p => (Fin.cons p.1.1 (Fin.snoc p.1.2 p.2) : Fin (k + 1 + 1) → S)) := by
            rw [Measure.map_map (measurable_finSnoc' (k + 1))
              ((measurable_finCons k).prodMap measurable_id)]
            refine congrArg (fun f => Measure.map f ((π ⊗ₘ chainWindowKernel κ k) ⊗ₘ η))
              (funext fun p => ?_)
            simp only [Function.comp_apply]
            exact (Fin.cons_snoc_eq_snoc_cons p.1.1 p.1.2 p.2).symm
      _ = ((π ⊗ₘ (chainWindowKernel κ k ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm).map
            (fun p => (Fin.cons p.1.1 (Fin.snoc p.1.2 p.2) : Fin (k + 1 + 1) → S)) := by
            rw [Measure.compProd_assoc]
      _ = (π ⊗ₘ (chainWindowKernel κ k ⊗ₖ η)).map
            (fun q => (Fin.cons q.1 (Fin.snoc q.2.1 q.2.2) : Fin (k + 1 + 1) → S)) := by
            rw [Measure.map_map hG MeasurableEquiv.prodAssoc.symm.measurable]; rfl
      _ = ((π ⊗ₘ (chainWindowKernel κ k ⊗ₖ η)).map
            (Prod.map id (fun p : (Fin k → S) × S => (Fin.snoc p.1 p.2 : Fin (k + 1) → S)))).map
            (fun p => (Fin.cons p.1 p.2 : Fin (k + 1 + 1) → S)) := by
            rw [Measure.map_map (measurable_finCons (k + 1))
              (measurable_id.prodMap (measurable_finSnoc' k))]; rfl
      _ = (π ⊗ₘ chainWindowKernel κ (k + 1)).map
            (fun p => (Fin.cons p.1 p.2 : Fin (k + 1 + 1) → S)) := by
            rw [chainWindowKernel, ← Measure.compProd_map (measurable_finSnoc' k)]

end K1

section Front
variable (κ : Kernel S S) [IsMarkovKernel κ]

lemma kernel_compProd_apply {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (κ' : Kernel α β) [IsSFiniteKernel κ']
    (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) :
    (κ' ⊗ₖ η) a = (κ' a) ⊗ₘ (η.comap (Prod.mk a) measurable_prodMk_left) := by
  ext s hs
  rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
  rfl

/-- (K3′) The strict future of the chain started at `x` is the chain started from `κ x`. -/
theorem chainWindowKernel_succ_apply (k : ℕ) (x : S) :
    chainWindowKernel κ (k + 1) x = chainWindowLaw κ (κ x) k := by
  induction k with
  | zero =>
    have hc : (κ.comap (fun p : S × (Fin 0 → S) =>
        (Fin.cons p.1 p.2 : Fin 1 → S) (Fin.last 0)) (measurable_consLast 0)).comap
        (Prod.mk x) measurable_prodMk_left = Kernel.const (Fin 0 → S) (κ x) := rfl
    rw [chainWindowKernel, Kernel.map_apply _ (measurable_finSnoc' 0), kernel_compProd_apply,
      chainWindowKernel, Kernel.deterministic_apply, hc, Measure.compProd_const,
      Measure.dirac_prod, Measure.map_map (measurable_finSnoc' 0) measurable_prodMk_left,
      chainWindowLaw]
    refine congrArg (fun f => Measure.map f (κ x)) (funext fun y => funext fun i => ?_)
    refine Fin.cases ?_ (fun j => j.elim0) i
    simp [Fin.snoc]
  | succ k ih =>
    have hfin : ∀ w : Fin (k + 1) → S,
        (Fin.cons x w : Fin (k + 1 + 1) → S) (Fin.last (k + 1)) = w (Fin.last k) := by
      intro w; rw [← Fin.succ_last, Fin.cons_succ]
    have hc : (κ.comap (fun p : S × (Fin (k + 1) → S) =>
        (Fin.cons p.1 p.2 : Fin (k + 1 + 1) → S) (Fin.last (k + 1)))
        (measurable_consLast (k + 1))).comap (Prod.mk x) measurable_prodMk_left
          = κ.comap (fun w : Fin (k + 1) → S => w (Fin.last k)) (measurable_pi_apply _) :=
      Kernel.ext fun w => by
        rw [Kernel.comap_apply, Kernel.comap_apply, Kernel.comap_apply, hfin w]
    rw [chainWindowKernel, Kernel.map_apply _ (measurable_finSnoc' (k + 1)),
      kernel_compProd_apply, hc, ih, chainWindowLaw]

/-- (K3) Front recursion of the window kernel. -/
theorem chainWindowKernel_succ (k : ℕ) :
    chainWindowKernel κ (k + 1)
      = (κ ⊗ₖ (chainWindowKernel κ k).comap Prod.snd measurable_snd).map
        (fun p => (Fin.cons p.1 p.2 : Fin (k + 1) → S)) := by
  refine Kernel.ext fun x => ?_
  rw [Kernel.map_apply _ (measurable_finCons k), kernel_compProd_apply,
    chainWindowKernel_succ_apply κ k x, chainWindowLaw_eq_compProd κ (κ x) k]
  rfl

/-- (P) Front extension of the window law: peel off the first coordinate. -/
theorem chainWindowLaw_succ_front (π : Measure S) [IsProbabilityMeasure π] (k : ℕ) :
    chainWindowLaw κ π (k + 1)
      = ((π ⊗ₘ κ) ⊗ₘ (chainWindowKernel κ k).comap Prod.snd measurable_snd).map
        (fun p => (Fin.cons p.1.1 (Fin.cons p.1.2 p.2) : Fin (k + 1 + 1) → S)) := by
  have hG : Measurable fun p : (S × S) × (Fin k → S) =>
      (Fin.cons p.1.1 (Fin.cons p.1.2 p.2) : Fin (k + 1 + 1) → S) :=
    (measurable_finCons (k + 1)).comp
      (measurable_fst.fst.prodMk ((measurable_finCons k).comp
        (measurable_fst.snd.prodMk measurable_snd)))
  rw [chainWindowLaw_eq_compProd κ π (k + 1), chainWindowKernel_succ κ k,
    Measure.compProd_map (measurable_finCons k),
    Measure.map_map (measurable_finCons (k + 1)) (measurable_id.prodMap (measurable_finCons k)),
    ← Measure.compProd_assoc,
    Measure.map_map hG MeasurableEquiv.prodAssoc.symm.measurable]
  rfl

end Front

section Backward
variable (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) [IsProbabilityMeasure π]

lemma compProd_comap_fst_swap {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (κ₁ : Kernel α β) [IsMarkovKernel κ₁]
    (κ₂ : Kernel α γ) [IsMarkovKernel κ₂] :
    (κ₁ ⊗ₖ (κ₂.comap Prod.fst measurable_fst)).map Prod.swap
      = κ₂ ⊗ₖ (κ₁.comap Prod.fst measurable_fst) := by
  refine Kernel.ext fun x => ?_
  have h1 : (κ₂.comap Prod.fst measurable_fst).comap (Prod.mk x) measurable_prodMk_left
      = Kernel.const β (κ₂ x) := rfl
  have h2 : (κ₁.comap Prod.fst measurable_fst).comap (Prod.mk x) measurable_prodMk_left
      = Kernel.const γ (κ₁ x) := rfl
  rw [Kernel.map_apply _ measurable_swap, kernel_compProd_apply, kernel_compProd_apply, h1, h2,
    Measure.compProd_const, Measure.compProd_const, Measure.prod_swap]

/-- (II) **Backward extension**: prepending one `reverseKernel` step to the stationary window
law gives the window law one step longer. -/
theorem chainWindowLaw_cons_reverseKernel (hinv : Kernel.Invariant κ π) (k : ℕ) :
    ((chainWindowLaw κ π k) ⊗ₘ
        ((reverseKernel κ π).comap (fun w : Fin (k + 1) → S => w 0)
          (measurable_pi_apply 0))).map
      (fun p => (Fin.cons p.2 p.1 : Fin (k + 1 + 1) → S)) = chainWindowLaw κ π (k + 1) := by
  set ρ := reverseKernel κ π with hρ
  set W := chainWindowKernel κ k with hW
  have hcons : ∀ p : S × (Fin k → S), (Fin.cons p.1 p.2 : Fin (k + 1) → S) 0 = p.1 :=
    fun p => Fin.cons_zero _ _
  have hc1 : (ρ.comap (fun w : Fin (k + 1) → S => w 0) (measurable_pi_apply 0)).comap
      (fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S)) (measurable_finCons k)
      = ρ.comap Prod.fst measurable_fst :=
    Kernel.ext fun p => by
      rw [Kernel.comap_apply, Kernel.comap_apply, Kernel.comap_apply, hcons p]
  have hSC : Measurable fun p : (Fin (k + 1) → S) × S =>
      (Fin.cons p.2 p.1 : Fin (k + 1 + 1) → S) :=
    (measurable_finCons (k + 1)).comp (measurable_snd.prodMk measurable_fst)
  have hG1 : Measurable fun p : (S × (Fin k → S)) × S =>
      (Fin.cons p.2 (Fin.cons p.1.1 p.1.2) : Fin (k + 1 + 1) → S) :=
    (measurable_finCons (k + 1)).comp (measurable_snd.prodMk
      ((measurable_finCons k).comp (measurable_fst.fst.prodMk measurable_fst.snd)))
  have hG2 : Measurable fun q : S × ((Fin k → S) × S) =>
      (Fin.cons q.2.2 (Fin.cons q.1 q.2.1) : Fin (k + 1 + 1) → S) :=
    (measurable_finCons (k + 1)).comp (measurable_snd.snd.prodMk
      ((measurable_finCons k).comp (measurable_fst.prodMk measurable_snd.fst)))
  have hG3 : Measurable fun r : S × (S × (Fin k → S)) =>
      (Fin.cons r.2.1 (Fin.cons r.1 r.2.2) : Fin (k + 1 + 1) → S) :=
    (measurable_finCons (k + 1)).comp (measurable_snd.fst.prodMk
      ((measurable_finCons k).comp (measurable_fst.prodMk measurable_snd.snd)))
  have hG4 : Measurable fun p : (S × S) × (Fin k → S) =>
      (Fin.cons p.1.2 (Fin.cons p.1.1 p.2) : Fin (k + 1 + 1) → S) :=
    (measurable_finCons (k + 1)).comp (measurable_fst.snd.prodMk
      ((measurable_finCons k).comp (measurable_fst.fst.prodMk measurable_snd)))
  calc ((chainWindowLaw κ π k) ⊗ₘ (ρ.comap (fun w : Fin (k + 1) → S => w 0)
          (measurable_pi_apply 0))).map (fun p => (Fin.cons p.2 p.1 : Fin (k + 1 + 1) → S))
      = (((π ⊗ₘ W) ⊗ₘ (ρ.comap Prod.fst measurable_fst)).map
          (Prod.map (fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S)) id)).map
          (fun p => (Fin.cons p.2 p.1 : Fin (k + 1 + 1) → S)) := by
          rw [hW, chainWindowLaw_eq_compProd κ π k, compProd_map_left _ (measurable_finCons k),
            hc1]
    _ = ((π ⊗ₘ W) ⊗ₘ (ρ.comap Prod.fst measurable_fst)).map
          (fun p => (Fin.cons p.2 (Fin.cons p.1.1 p.1.2) : Fin (k + 1 + 1) → S)) := by
          rw [Measure.map_map hSC ((measurable_finCons k).prodMap measurable_id)]; rfl
    _ = ((π ⊗ₘ (W ⊗ₖ (ρ.comap Prod.fst measurable_fst))).map
          MeasurableEquiv.prodAssoc.symm).map
          (fun p => (Fin.cons p.2 (Fin.cons p.1.1 p.1.2) : Fin (k + 1 + 1) → S)) := by
          rw [Measure.compProd_assoc]
    _ = (π ⊗ₘ (W ⊗ₖ (ρ.comap Prod.fst measurable_fst))).map
          (fun q => (Fin.cons q.2.2 (Fin.cons q.1 q.2.1) : Fin (k + 1 + 1) → S)) := by
          rw [Measure.map_map hG1 MeasurableEquiv.prodAssoc.symm.measurable]; rfl
    _ = (π ⊗ₘ (ρ ⊗ₖ (W.comap Prod.fst measurable_fst))).map
          (fun r => (Fin.cons r.2.1 (Fin.cons r.1 r.2.2) : Fin (k + 1 + 1) → S)) := by
          rw [← compProd_comap_fst_swap W ρ, Measure.compProd_map measurable_swap,
            Measure.map_map hG3 (measurable_id.prodMap measurable_swap)]
          rfl
    _ = (((π ⊗ₘ ρ) ⊗ₘ (W.comap Prod.fst measurable_fst)).map MeasurableEquiv.prodAssoc).map
          (fun r => (Fin.cons r.2.1 (Fin.cons r.1 r.2.2) : Fin (k + 1 + 1) → S)) := by
          rw [← Measure.compProd_assoc, Measure.map_map MeasurableEquiv.prodAssoc.measurable
            MeasurableEquiv.prodAssoc.symm.measurable]
          simp
    _ = ((π ⊗ₘ ρ) ⊗ₘ (W.comap Prod.fst measurable_fst)).map
          (fun p => (Fin.cons p.1.2 (Fin.cons p.1.1 p.2) : Fin (k + 1 + 1) → S)) := by
          rw [Measure.map_map hG3 MeasurableEquiv.prodAssoc.measurable]; rfl
    _ = (((π ⊗ₘ κ) ⊗ₘ (W.comap Prod.snd measurable_snd)).map (Prod.map Prod.swap id)).map
          (fun p => (Fin.cons p.1.2 (Fin.cons p.1.1 p.2) : Fin (k + 1 + 1) → S)) := by
          rw [hρ, ← pairLaw_swap_eq_compProd_reverseKernel κ π hinv]
          show ((pairLaw κ π).map Prod.swap ⊗ₘ _).map _ = _
          rw [compProd_map_left _ measurable_swap]
          rfl
    _ = ((π ⊗ₘ κ) ⊗ₘ (W.comap Prod.snd measurable_snd)).map
          (fun p => (Fin.cons p.1.1 (Fin.cons p.1.2 p.2) : Fin (k + 1 + 1) → S)) := by
          rw [Measure.map_map hG4 (measurable_swap.prodMap measurable_id)]; rfl
    _ = chainWindowLaw κ π (k + 1) := (chainWindowLaw_succ_front κ π k).symm

end Backward

section Traj
open Preorder
variable (κ : Kernel S S) [IsMarkovKernel κ]

/-- The constant kernel family fed to Ionescu–Tulcea. -/
noncomputable def stepFam (n : ℕ) : Kernel ((i : ↥(Finset.Iic n)) → S) S :=
  κ.comap (fun w => w ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance (n : ℕ) : IsMarkovKernel (stepFam κ n) := by unfold stepFam; infer_instance

/-- Reindexing `Iic n` as `Fin (n+1)`. -/
def iicToFin (n : ℕ) (w : (i : ↥(Finset.Iic n)) → S) : Fin (n + 1) → S :=
  fun i => w ⟨(i : ℕ), Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp i.isLt)⟩

lemma measurable_iicToFin (n : ℕ) : Measurable (iicToFin (S := S) n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- The Ionescu–Tulcea trajectory law of the chain started from `π`. -/
noncomputable def trajLaw (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) :
    Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ => S) π (stepFam κ)

/-- (T1) The `Iic n` window of the Ionescu–Tulcea trajectory measure is the chain window law. -/
theorem trajMeasure_map_window (π : Measure S) [IsProbabilityMeasure π] (n : ℕ) :
    (trajLaw κ π).map (fun ω (i : Fin (n + 1)) => ω (i : ℕ))
      = chainWindowLaw κ π n := by
  haveI hprob : IsProbabilityMeasure (trajLaw κ π) := by rw [trajLaw]; infer_instance
  induction n with
  | zero =>
    have h1 : (trajLaw κ π).map (frestrictLe 0)
        = π.map (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S)).symm := by
      rw [trajLaw, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
        Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
    have h2 : (fun (ω : ℕ → S) (i : Fin 1) => ω (i : ℕ))
        = (iicToFin (S := S) 0) ∘ (frestrictLe 0) := rfl
    rw [h2, ← Measure.map_map (measurable_iicToFin 0) (measurable_frestrictLe 0), h1,
      Measure.map_map (measurable_iicToFin 0)
        (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S)).symm.measurable,
      chainWindowLaw]
    refine congrArg (fun f => Measure.map f π) (funext fun x => funext fun i => ?_)
    simp [iicToFin, MeasurableEquiv.piUnique]
  | succ n ih =>
    have hsnoc : Measurable fun p : ((i : ↥(Finset.Iic n)) → S) × S =>
        (Fin.snoc (iicToFin n p.1) p.2 : Fin (n + 1 + 1) → S) :=
      (measurable_finSnoc' (n + 1)).comp
        (((measurable_iicToFin n).comp measurable_fst).prodMk measurable_snd)
    have hpair : Measurable fun ω : ℕ → S => (frestrictLe n ω, ω (n + 1)) :=
      (measurable_frestrictLe n).prodMk (measurable_pi_apply _)
    have hfac : (fun (ω : ℕ → S) (i : Fin (n + 1 + 1)) => ω (i : ℕ))
        = (fun p : ((i : ↥(Finset.Iic n)) → S) × S =>
            (Fin.snoc (iicToFin n p.1) p.2 : Fin (n + 1 + 1) → S))
          ∘ (fun ω => (frestrictLe n ω, ω (n + 1))) := by
      funext ω i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp [iicToFin]
    have hih : ((trajLaw κ π).map (frestrictLe n)).map (iicToFin n)
        = chainWindowLaw κ π n := by
      rw [Measure.map_map (measurable_iicToFin n) (measurable_frestrictLe n)]; exact ih
    haveI : IsProbabilityMeasure ((trajLaw κ π).map (frestrictLe n)) :=
      Measure.isProbabilityMeasure_map (measurable_frestrictLe n).aemeasurable
    have key : ((trajLaw κ π).map (frestrictLe n)) ⊗ₘ stepFam κ n
        = (trajLaw κ π).map (fun ω => (frestrictLe n ω, ω (n + 1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    haveI : IsProbabilityMeasure ((trajLaw κ π).map (frestrictLe n)) :=
      Measure.isProbabilityMeasure_map (measurable_frestrictLe n).aemeasurable
    have key : ((trajLaw κ π).map (frestrictLe n)) ⊗ₘ stepFam κ n
        = (trajLaw κ π).map (fun ω => (frestrictLe n ω, ω (n + 1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have hcomap : (κ.comap (fun w : Fin (n + 1) → S => w (Fin.last n))
        (measurable_pi_apply _)).comap (iicToFin n) (measurable_iicToFin n) = stepFam κ n := rfl
    calc (trajLaw κ π).map (fun ω (i : Fin (n + 1 + 1)) => ω (i : ℕ))
        = ((trajLaw κ π).map (fun ω => (frestrictLe n ω, ω (n + 1)))).map
            (fun p => (Fin.snoc (iicToFin n p.1) p.2 : Fin (n + 1 + 1) → S)) := by
            rw [hfac, ← Measure.map_map hsnoc hpair]
      _ = (((trajLaw κ π).map (frestrictLe n)) ⊗ₘ stepFam κ n).map
            (fun p => (Fin.snoc (iicToFin n p.1) p.2 : Fin (n + 1 + 1) → S)) := by
            rw [key]
      _ = ((chainWindowLaw κ π n) ⊗ₘ (κ.comap (fun w : Fin (n + 1) → S => w (Fin.last n))
            (measurable_pi_apply _))).map (fun p => (Fin.snoc p.1 p.2 : Fin (n + 1 + 1) → S)) := by
            rw [← hih, compProd_map_left _ (measurable_iicToFin n), hcomap,
              Measure.map_map (measurable_finSnoc' (n + 1))
                ((measurable_iicToFin n).prodMap measurable_id)]
            rfl
      _ = chainWindowLaw κ π (n + 1) := rfl

/-- The Ionescu–Tulcea trajectory kernel of `κ` (index `0` carries the starting point). -/
noncomputable def trajKernel (κ : Kernel S S) [IsMarkovKernel κ] : Kernel S (ℕ → S) :=
  (Kernel.traj (X := fun _ => S) (stepFam κ) 0).comap
    (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S)).symm
    (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S)).symm.measurable

instance : IsMarkovKernel (trajKernel κ) := by unfold trajKernel; infer_instance

lemma trajLaw_eq (π : Measure S) : trajLaw κ π = (trajKernel κ) ∘ₘ π := by
  rw [trajLaw, Kernel.trajMeasure, trajKernel, ← Kernel.comp_deterministic_eq_comap,
    ← Measure.comp_assoc, Measure.deterministic_comp_eq_map]

lemma trajLaw_dirac (x : S) : trajLaw κ (Measure.dirac x) = trajKernel κ x := by
  rw [trajLaw_eq]
  exact Measure.dirac_bind (Kernel.measurable _) x

lemma measurable_finTail (n : ℕ) :
    Measurable (Fin.tail : (Fin (n + 1) → S) → (Fin n → S)) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- (T2) The strict future of the trajectory kernel is the chain window kernel. -/
theorem trajKernel_map_window (n : ℕ) :
    (trajKernel κ).map (fun ω (i : Fin n) => ω ((i : ℕ) + 1)) = chainWindowKernel κ n := by
  have hidx : Measurable fun ω : ℕ → S => fun i : Fin n => ω ((i : ℕ) + 1) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hwin : Measurable fun ω : ℕ → S => fun i : Fin (n + 1) => ω (i : ℕ) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  refine Kernel.ext fun x => ?_
  have hcx : Measurable fun w : Fin n → S => (Fin.cons x w : Fin (n + 1) → S) :=
    (measurable_finCons n).comp (measurable_const.prodMk measurable_id)
  rw [Kernel.map_apply _ hidx]
  have h1 : (trajKernel κ x).map (fun ω (i : Fin (n + 1)) => ω (i : ℕ))
      = chainWindowLaw κ (Measure.dirac x) n := by
    rw [← trajLaw_dirac κ x]; exact trajMeasure_map_window κ (Measure.dirac x) n
  have hd : (Measure.dirac x ⊗ₘ chainWindowKernel κ n)
      = (chainWindowKernel κ n x).map (Prod.mk x) := by
    ext s hs
    rw [Measure.dirac_compProd_apply hs, Measure.map_apply measurable_prodMk_left hs]
  have h2 : chainWindowLaw κ (Measure.dirac x) n
      = (chainWindowKernel κ n x).map (fun w => (Fin.cons x w : Fin (n + 1) → S)) := by
    rw [chainWindowLaw_eq_compProd, hd,
      Measure.map_map (measurable_finCons n) measurable_prodMk_left]
    rfl
  have h3 := congrArg (fun μ : Measure (Fin (n + 1) → S) => μ.map Fin.tail) (h1.trans h2)
  simp only at h3
  rw [Measure.map_map (measurable_finTail n) hwin,
    Measure.map_map (measurable_finTail n) hcx] at h3
  have h4 : (Fin.tail ∘ fun w : Fin n → S => (Fin.cons x w : Fin (n + 1) → S)) = id :=
    funext fun w => by simp [Fin.tail_cons]
  rw [h4, Measure.map_id] at h3
  rw [← h3]
  rfl

end Traj

end StatLean.TimeSeries
