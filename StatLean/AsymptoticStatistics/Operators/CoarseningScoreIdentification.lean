import StatLean.AsymptoticStatistics.Operators.CARScores
import StatLean.AsymptoticStatistics.Operators.CAR
import StatLean.AsymptoticStatistics.Operators.InformationLoss
import StatLean.AsymptoticStatistics.ForMathlib.CondExpCompProd
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# CAR coarsening-score identification: `(observedTangent fullQTangent)ᗮ = concrete` (vdV thm:25.40)

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.5.3,
thm:25.40 (book p.380).

The abstract layer `Operators/CARScores.lean` gives the Hilbert splitting
`H = S̄ ⊕ Sᗮ` with `coarseningScores := (observedTangent …)ᗮ`. The substantive
CAR content of thm:25.40 is the concrete
identification of that orthogonal complement: over the coarsening model
`P_full = Q ⊗ₘ r` on `𝓨 × 𝓓` with observation map `M : 𝓨 × 𝓓 → 𝓧`, the coarsening
scores are exactly the observed functions `b(x)` whose fibrewise `r`-average
vanishes,
  `Ṙ_{Q,R} = { b ∈ L²₀(P_obs) : ∀ᵐ y ∂Q, ∫ δ, b (M (y, δ)) ∂(r y) = 0 }`,
which is vdV's `E_R(b(X) | Y = y) = 0` condition.

This file uses the encoding `P_full = Q ⊗ₘ r`, `M : 𝓨 × 𝓓 → 𝓧`,
the *full* `Q`-tangent `fullQTangent` (all mean-zero functions of the first
coordinate `Y` — "`Q` completely unspecified", vdV p.380), the concrete coarsening
scores `concreteCoarseningScores`, the identification
`coarseningScores … fullQTangent = concreteCoarseningScores`, and the
CAR-carrying decomposition `car_observed_tangent_decomposition`.

Headline declarations: `fullQTangent`, `concreteCoarseningScores`,
`mem_concreteCoarseningScores_iff`, `coarseningScores_eq_concrete`,
`car_observed_tangent_decomposition`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped InnerProductSpace ENNReal

set_option linter.dupNamespace false

namespace AsymptoticStatistics.Operators.CoarseningScoreIdentification

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Operators.InformationLoss
open AsymptoticStatistics.Operators.CAR
open AsymptoticStatistics.Operators.CARScores
open AsymptoticStatistics.ForMathlib.CondExpL2
open AsymptoticStatistics.ForMathlib.CondExpCompProd

variable {𝓨 𝓓 𝓧 : Type*}
  [MeasurableSpace 𝓨] [MeasurableSpace 𝓓] [MeasurableSpace 𝓧]
  (Q : Measure 𝓨) [IsProbabilityMeasure Q]
  (r : Kernel 𝓨 𝓓) [IsMarkovKernel r]
  {M : 𝓨 × 𝓓 → 𝓧} (hM : Measurable M)

/-! ### The full `Q`-tangent -/

/-- *The full `Q`-tangent space* `Ṗ_Q` (vdV thm:25.40, book p.380 — "`Q` is
completely unspecified").

Constitutive (vdV §25.5.3 p.380): the tangent set of the *full-data* model when the
marginal law `Q` of `Y` ranges over **all** probability measures is the space of
all mean-zero functions of `Y` alone. Under the `P_full = Q ⊗ₘ r` encoding, `Y` is
the first coordinate `Prod.fst : 𝓨 × 𝓓 → 𝓨`, so this is the mean-zero `L²`
functions that are `comap Prod.fst`-measurable, realized as the pullback along the
`L²₀`-inclusion of Mathlib's `comap Prod.fst`-measurable submodule `lpMeas`. Removing
the "all `Q`" maximality would make this a proper subspace and break the density
half of the identification. -/
noncomputable def fullQTangent :
    Submodule ℝ ↥(L2ZeroMean (Q ⊗ₘ r)) :=
  Submodule.comap (L2ZeroMean (Q ⊗ₘ r)).subtype
    (lpMeas ℝ ℝ (MeasurableSpace.comap Prod.fst ‹MeasurableSpace 𝓨›) 2 (Q ⊗ₘ r))

/-! ### The concrete coarsening scores -/

/-- *The concrete coarsening-score space* `Ṙ_{Q,R}` (vdV thm:25.40, book p.380),
condExp-kernel form.

Constitutive (vdV §25.5.3 p.380): the coarsening scores are the observed scores `b`
with `E_R(b(X) | Y) = 0` a.s. In `L²` terms this is the kernel of the linear map
`b ↦ E[b ∘ M | comap Prod.fst]`: pull the observed score `b` back to `𝓨 × 𝓓` along
`M` via the Doob isometry `(doobL2Equiv hM).symm`, then take the conditional
expectation under the `Y`-coordinate σ-algebra `comap Prod.fst`. Realizing it as a
`LinearMap.ker` makes it manifestly a submodule; the equivalence with vdV's verbatim
fibre condition `∫ δ, b (M (y, δ)) ∂(r y) = 0` is `mem_concreteCoarseningScores_iff`. -/
noncomputable def concreteCoarseningScores :
    Submodule ℝ ↥(L2ZeroMean ((Q ⊗ₘ r).map M)) :=
  LinearMap.ker
    (((condExpL2 ℝ ℝ (measurable_fst.comap_le)).comp
      (((lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)).subtypeL).comp
        (((doobL2Equiv hM).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
          (L2ZeroMean ((Q ⊗ₘ r).map M)).subtypeL))).toLinearMap)

omit [IsProbabilityMeasure Q] [IsMarkovKernel r] in
/-- The Doob pullback `↑((doobL2Equiv hM).symm b)` of an observed function `b`
agrees `Q ⊗ₘ r`-a.e. with `b ∘ M` (behavioral identity for the Doob isometry). -/
private theorem obsPullback_ae_eq
    (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
    ((((doobL2Equiv hM).symm b :
        lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
        Lp ℝ 2 (Q ⊗ₘ r)) : 𝓨 × 𝓓 → ℝ)
      =ᵐ[Q ⊗ₘ r] fun p => (b : 𝓧 → ℝ) (M p) := by
  have h := doobL2Equiv_comp_apply hM ((doobL2Equiv hM).symm b)
  rw [(doobL2Equiv hM).apply_symm_apply] at h
  exact h.symm

/-- Membership in `concreteCoarseningScores` is exactly vanishing of the
`comap Prod.fst` conditional expectation of the Doob pullback (unfolds the
`LinearMap.ker` definition). -/
private theorem mem_concrete_iff
    (b : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))) :
    b ∈ concreteCoarseningScores Q r hM ↔
      ((condExpL2 ℝ ℝ measurable_fst.comap_le
          (((doobL2Equiv hM).symm (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
              lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
              Lp ℝ 2 (Q ⊗ₘ r)) : Lp ℝ 2 (Q ⊗ₘ r))) = 0 := by
  unfold concreteCoarseningScores
  rw [LinearMap.mem_ker, ← Submodule.coe_eq_zero]
  rfl

/-- *Verbatim fibre characterization of the concrete coarsening scores* (vdV
thm:25.40, book p.380).

Membership in `concreteCoarseningScores` is exactly vdV's per-fibre mean-zero
condition `E_R(b(X) | Y = y) = ∫ δ, b (M (y, δ)) ∂(r y) = 0` for `Q`-a.e. `y`. -/
theorem mem_concreteCoarseningScores_iff
    (b : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))) :
    b ∈ concreteCoarseningScores Q r hM ↔
      ∀ᵐ y ∂Q, ∫ δ, ((b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M (y, δ)) ∂(r y) = 0 := by
  rw [mem_concrete_iff Q r hM b, Lp.eq_zero_iff_ae_eq_zero]
  -- `b ∘ M` is integrable (a.e. equal to the L² Doob pullback).
  have hbM_int :
      Integrable (fun p => ((b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M p)) (Q ⊗ₘ r) :=
    ((Lp.memLp (((doobL2Equiv hM).symm (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
        lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
        Lp ℝ 2 (Q ⊗ₘ r))).integrable one_le_two).congr
      (obsPullback_ae_eq Q r hM (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)))
  -- The conditional expectation of the pullback is a.e. the fibre integral.
  have hcond_ae :
      (((condExpL2 ℝ ℝ measurable_fst.comap_le
          (((doobL2Equiv hM).symm (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
              lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
              Lp ℝ 2 (Q ⊗ₘ r)) : Lp ℝ 2 (Q ⊗ₘ r))) : 𝓨 × 𝓓 → ℝ)
        =ᵐ[Q ⊗ₘ r]
          fun p => ∫ δ, ((b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M (p.1, δ)) ∂(r p.1) := by
    have h1 := MemLp.condExpL2_ae_eq_condExp (𝕜 := ℝ) measurable_fst.comap_le
      (Lp.memLp (((doobL2Equiv hM).symm (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
        lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
        Lp ℝ 2 (Q ⊗ₘ r)))
    rw [Lp.toLp_coeFn] at h1
    have h2 := condExp_congr_ae (m := MeasurableSpace.comap Prod.fst ‹MeasurableSpace 𝓨›)
      (obsPullback_ae_eq Q r hM (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)))
    have h3 := condExp_compProd_fst Q r
      (fun p => ((b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M p)) hbM_int
    exact (h1.trans h2).trans h3
  constructor
  · intro hh
    have hh' :
        (fun p => ∫ δ, ((b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M (p.1, δ)) ∂(r p.1))
          =ᵐ[Q ⊗ₘ r] 0 := hcond_ae.symm.trans hh
    have h4 := Measure.ae_ae_of_ae_compProd hh'
    filter_upwards [h4] with y hy
    obtain ⟨_, hδ₀⟩ := hy.exists
    simpa using hδ₀
  · intro hh
    refine hcond_ae.trans ?_
    have hmp : MeasurePreserving (Prod.fst : 𝓨 × 𝓓 → 𝓨) (Q ⊗ₘ r) Q :=
      ⟨measurable_fst, Measure.fst_compProd Q r⟩
    have hcomp := hmp.quasiMeasurePreserving.ae_eq_comp
      (g := fun y => ∫ δ, ((b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M (y, δ)) ∂(r y))
      (g' := 0) hh
    filter_upwards [hcomp] with p hp
    simpa using hp

/-! ### Orthogonality: concrete scores are abstract scores -/

/-- *Concrete coarsening scores lie in the abstract complement* (vdV thm:25.40,
book p.380, orthogonality half).

Every `b` with `E_R(b | Y) = 0` a.s. is orthogonal to the whole observed `Q`-score
image `observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)`. This is the tower identity
`⟪Π a, b⟫ = ⟪a, b ∘ M⟫ = E[a(Y) · E_R(b | Y)] = 0` via
`Operators.CAR.inner_observedTangent_piece` and `condExp_compProd_fst`. -/
theorem concreteCoarseningScores_le :
    concreteCoarseningScores Q r hM
      ≤ coarseningScores hM (Q ⊗ₘ r) (fullQTangent Q r) := by
  intro b hb
  have hpull0 := (mem_concrete_iff Q r hM b).mp hb
  simp only [coarseningScores, Submodule.mem_orthogonal]
  intro u hu
  rw [mem_observedTangent_iff] at hu
  obtain ⟨a, ha, rfl⟩ := hu
  have ha_meas :
      AEStronglyMeasurable[MeasurableSpace.comap Prod.fst ‹MeasurableSpace 𝓨›]
        ((a : Lp ℝ 2 (Q ⊗ₘ r))) (Q ⊗ₘ r) :=
    mem_lpMeas_iff_aestronglyMeasurable.mp (Submodule.mem_comap.mp ha)
  rw [Submodule.coe_inner,
    inner_observedTangent_piece hM (Q ⊗ₘ r) a (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)),
    real_inner_comm,
    ← inner_condExpL2_eq_inner_fun measurable_fst.comap_le _ _ ha_meas,
    hpull0, inner_zero_left]

/-! ### Density: abstract scores are concrete scores -/

/-- *The abstract complement lies in the concrete coarsening scores* (vdV thm:25.40,
book p.380, density half).

Any observed score `b` orthogonal to the whole observed `Q`-score image satisfies
`E_R(b | Y) = 0` a.s. Set `h := E[b ∘ M | comap Prod.fst]`, a member of
`fullQTangent` (uses the FULL `Q`-tangent = "`Q` completely unspecified", vdV p.380);
orthogonality gives `⟪Π h, b⟫ = 0`, whence `‖h‖² = 0`, `h = 0`, i.e.
`E(b(X) | Y) = 0`. -/
theorem le_concreteCoarseningScores :
    coarseningScores hM (Q ⊗ₘ r) (fullQTangent Q r)
      ≤ concreteCoarseningScores Q r hM := by
  intro g hg
  refine (mem_concrete_iff Q r hM g).mpr ?_
  refine (inner_self_eq_zero (𝕜 := ℝ)).mp ?_
  set pb : Lp ℝ 2 (Q ⊗ₘ r) :=
    (((doobL2Equiv hM).symm (g : Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
        lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
        Lp ℝ 2 (Q ⊗ₘ r)) with hpb_def
  set hc : Lp ℝ 2 (Q ⊗ₘ r) :=
    ((condExpL2 ℝ ℝ measurable_fst.comap_le pb : Lp ℝ 2 (Q ⊗ₘ r))) with hc_def
  -- `pb` integrates to `0` (Doob-transport of `g ∈ L²₀`).
  have hpb_int : ∫ p, (pb : 𝓨 × 𝓓 → ℝ) p ∂(Q ⊗ₘ r) = 0 := by
    rw [hpb_def, integral_congr_ae (obsPullback_ae_eq Q r hM (g : Lp ℝ 2 ((Q ⊗ₘ r).map M))),
      ← integral_map hM.aemeasurable (Lp.aestronglyMeasurable (g : Lp ℝ 2 ((Q ⊗ₘ r).map M)))]
    exact (mem_L2ZeroMean_iff _ _).mp g.2
  -- hence `hc = E[pb | comap fst]` also integrates to `0`.
  have hc_int : ∫ p, (hc : 𝓨 × 𝓓 → ℝ) p ∂(Q ⊗ₘ r) = 0 := by
    have h := integral_condExpL2_eq (𝕜 := ℝ) measurable_fst.comap_le pb
      MeasurableSet.univ (measure_ne_top (Q ⊗ₘ r) _)
    rw [setIntegral_univ, setIntegral_univ] at h
    rw [hc_def, h]; exact hpb_int
  have hc_mem : (hc : Lp ℝ 2 (Q ⊗ₘ r)) ∈ L2ZeroMean (Q ⊗ₘ r) :=
    (mem_L2ZeroMean_iff _ _).mpr hc_int
  have hc_meas :
      AEStronglyMeasurable[MeasurableSpace.comap Prod.fst ‹MeasurableSpace 𝓨›]
        (hc : 𝓨 × 𝓓 → ℝ) (Q ⊗ₘ r) := by
    rw [hc_def]; exact aestronglyMeasurable_condExpL2 measurable_fst.comap_le pb
  have ha_full : (⟨hc, hc_mem⟩ : ↥(L2ZeroMean (Q ⊗ₘ r))) ∈ fullQTangent Q r := by
    simp only [fullQTangent, Submodule.mem_comap]
    exact Submodule.coe_mem (condExpL2 ℝ ℝ measurable_fst.comap_le pb)
  -- Orthogonality of the observed image against the coarsening score `g`.
  have h_orth' : ⟪(hc : Lp ℝ 2 (Q ⊗ₘ r)), (pb : Lp ℝ 2 (Q ⊗ₘ r))⟫_ℝ = 0 := by
    have key := inner_observedTangent_coarseningScore_eq_zero hM (Q ⊗ₘ r)
      (fullQTangent Q r) (a := ⟨hc, hc_mem⟩) ha_full hg
    rw [inner_observedTangent_piece hM (Q ⊗ₘ r) ⟨hc, hc_mem⟩
      (g : Lp ℝ 2 ((Q ⊗ₘ r).map M))] at key
    exact key
  calc ⟪(hc : Lp ℝ 2 (Q ⊗ₘ r)), (hc : Lp ℝ 2 (Q ⊗ₘ r))⟫_ℝ
      = ⟪(pb : Lp ℝ 2 (Q ⊗ₘ r)), (hc : Lp ℝ 2 (Q ⊗ₘ r))⟫_ℝ :=
        inner_condExpL2_eq_inner_fun measurable_fst.comap_le pb hc hc_meas
    _ = ⟪(hc : Lp ℝ 2 (Q ⊗ₘ r)), (pb : Lp ℝ 2 (Q ⊗ₘ r))⟫_ℝ := real_inner_comm _ _
    _ = 0 := h_orth'

/-! ### Identification -/

/-- *Coarsening-score identification* (vdV thm:25.40, book p.380): the abstract
orthogonal complement of the observed `Q`-score image equals the concrete
`E_R(b | Y) = 0` coarsening scores. -/
theorem coarseningScores_eq_concrete :
    coarseningScores hM (Q ⊗ₘ r) (fullQTangent Q r) = concreteCoarseningScores Q r hM :=
  le_antisymm (le_concreteCoarseningScores Q r hM) (concreteCoarseningScores_le Q r hM)

/-! ### CAR observed-tangent decomposition -/

/-- *vdV thm:25.40 — the CAR observed-tangent decomposition* (book p.380).

Every mean-zero observed score `g ∈ L²₀(P_obs)` splits orthogonally as `g = p + b`,
where:
  * `p ∈ (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)).topologicalClosure` — a
    limit of conditional-expectation images `E_{Q,R}(a(Y) | X)` of full `Q`-scores
    `a` (the closure is genuine: the tangent set need not be closed), and
  * `b ∈ concreteCoarseningScores Q r hM` — a *concrete* coarsening score, i.e. an
    observed function with `E_R(b(X) | Y) = 0` a.s.,

with `p ⊥ b`. Unlike the abstract `observedTangent_orthogonal_decomposition` (whose
`b` sits in the opaque complement `(observedTangent …)ᗮ`), here `b` carries the
book's explicit `E_R(b | Y) = 0` CAR content via `coarseningScores_eq_concrete`. -/
theorem car_observed_tangent_decomposition
    (g : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))) :
    ∃ p ∈ (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)).topologicalClosure,
      ∃ b ∈ concreteCoarseningScores Q r hM,
        g = p + b ∧
        ⟪(p : Lp ℝ 2 ((Q ⊗ₘ r).map M)), (b : Lp ℝ 2 ((Q ⊗ₘ r).map M))⟫_ℝ = 0 := by
  obtain ⟨p, hp, b, hb, hgpb, hpb⟩ :=
    observedTangent_orthogonal_decomposition hM (Q ⊗ₘ r) (fullQTangent Q r) g
  refine ⟨p, hp, b, ?_, hgpb, hpb⟩
  rwa [← coarseningScores_eq_concrete Q r hM]

/-! ### vdV lem:25.41: IPW influence-function characterization -/

open AsymptoticStatistics.Core.Pathwise in
/-- *vdV lem:25.41 — IPW characterization of observed influence functions* (book
p.381-382).

With the censoring mechanism `R` known, the model `P_{Q,R}` (`Q ∈ 𝒬`, `R` fixed) has
observed tangent `observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)` — the `Π`-images
of the full `Q`-scores — since the coarsening directions are *not* tangent (`R` is
fixed). Influence functions for `χ(Q)` therefore form the affine space
`Π φ_full + (observedTangent)ᗮ`, and `(observedTangent)ᗮ = concreteCoarseningScores`
by `coarseningScores_eq_concrete`. This is vdV's statement that any influence
function is `1{δ∈C}/R(C|y)·χ_Q(Y) + b(x)`, with `b` ranging over the scores
satisfying `E_R(b | Y) = 0`, uniquely.

The IPW representer `φ_full` (vdV's `1{δ∈C}/R(C|y)·χ_Q(Y)`, requiring `R` known and
`R(C|y)` bounded away from `0`) and the fact that its `Π`-image is an influence
function for `χ(Q)` are explicit hypotheses: the concrete reweight
`1{δ∈C}/R(C|y)` needs the `𝓨 × 𝓓` product structure and the complete-case set `C`,
which the abstract IF layer does not carry. -/
theorem ipw_influence_characterization
    -- The observed pathwise derivative `χ̇_Q`.
    (dψ_obs : (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)) →L[ℝ] ℝ)
    -- The IPW-reweighted full-data representer `1{δ∈C}/R(C|y)·χ_Q(Y)`.
    (φ_full : ↥(L2ZeroMean (Q ⊗ₘ r)))
    -- `Π φ_full` is an influence function for `χ(Q)`.
    (h_ipw : letI : IsProbabilityMeasure ((Q ⊗ₘ r).map M) :=
          Measure.isProbabilityMeasure_map hM.aemeasurable
        IsInfluenceFunction ((Q ⊗ₘ r).map M)
          (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)) dψ_obs
          (informationLossOperator hM (Q ⊗ₘ r) φ_full))
    (φ_obs : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))) :
    letI : IsProbabilityMeasure ((Q ⊗ₘ r).map M) :=
      Measure.isProbabilityMeasure_map hM.aemeasurable
    IsInfluenceFunction ((Q ⊗ₘ r).map M)
        (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)) dψ_obs φ_obs
      ↔ ∃ b ∈ concreteCoarseningScores Q r hM,
          φ_obs = informationLossOperator hM (Q ⊗ₘ r) φ_full + b := by
  haveI hpm : IsProbabilityMeasure ((Q ⊗ₘ r).map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  -- `b ∈ concreteCoarseningScores ↔ b ∈ (observedTangent)ᗮ`.
  have hb_orth_iff : ∀ b : ↥(L2ZeroMean ((Q ⊗ₘ r).map M)),
      b ∈ concreteCoarseningScores Q r hM ↔
        b ∈ (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r))ᗮ := by
    intro b
    rw [← coarseningScores_eq_concrete Q r hM]; rfl
  constructor
  · -- ⟹ : any influence function differs from `Π φ_full` by a coarsening score.
    intro h
    refine ⟨φ_obs - informationLossOperator hM (Q ⊗ₘ r) φ_full, ?_, by abel⟩
    rw [hb_orth_iff, Submodule.mem_orthogonal]
    intro u hu
    have e1 : ⟪(u : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))), φ_obs⟫_ℝ = dψ_obs ⟨u, hu⟩ := by
      rw [real_inner_comm]; exact h ⟨u, hu⟩
    have e2 : ⟪(u : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))),
        informationLossOperator hM (Q ⊗ₘ r) φ_full⟫_ℝ = dψ_obs ⟨u, hu⟩ := by
      rw [real_inner_comm]; exact h_ipw ⟨u, hu⟩
    rw [inner_sub_right, e1, e2, sub_self]
  · -- ⟸ : `Π φ_full + b` (with `b` a coarsening score) is an influence function.
    rintro ⟨b, hb, rfl⟩
    have hb_orth := (hb_orth_iff b).mp hb
    intro g
    rw [inner_add_left, h_ipw g,
      Submodule.inner_left_of_mem_orthogonal g.2 hb_orth, add_zero]

end AsymptoticStatistics.Operators.CoarseningScoreIdentification
