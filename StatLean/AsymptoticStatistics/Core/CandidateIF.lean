import StatLean.AsymptoticStatistics.Core.Hilbert

/-!
# Candidate influence function

A model-agnostic raw-`Ω→ℝ` wrapper that packages measurability,
square-integrability, and mean-zero into a single object that lifts
cleanly into `L2ZeroMean P`. Concrete examples specify the influence
function pointwise as a raw function on the observation space; comparing
two such formulas as *almost-everywhere* equalities is much easier than
comparing them as elements of the quotient `Lp ℝ 2 P`. The
`CandidateIF.toL2ZeroMean` constructor turns a candidate into an element
of the target Hilbert space, and `CandidateIF.toL2ZeroMean_eq_of_aeEq`
says two candidates that agree a.e. land at the same L²₀(P) element.

Reference: van der Vaart, *Asymptotic Statistics* §25.3 — the working
definition of an influence function as an a.e. defined real function on
`Ω` with mean zero and finite second moment.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core

open AsymptoticStatistics.Core.Hilbert

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A *candidate influence function* on `(Ω, P)` is a raw `Ω → ℝ`
function packaged with the data needed to lift it into `L2ZeroMean P`.

Fields, in order:

- `raw` — the raw measurable representative; without it, the object
  is not a candidate function.
- `memLp2` — square-integrability under `P`. Bundles
  `AEStronglyMeasurable` via `MemLp.aestronglyMeasurable`, so a separate
  measurability field is unnecessary and is intentionally absent.
- `mean_zero` — mean-zero, required to land in `L2ZeroMean P`
  (the kernel of `integralL2 P`).

Reference: vdV §25.3 (definition of influence function). -/
structure CandidateIF (P : Measure Ω) [IsFiniteMeasure P] where
  raw : Ω → ℝ
  memLp2 : MemLp raw 2 P
  mean_zero : ∫ ω, raw ω ∂P = 0

namespace CandidateIF

variable {P : Measure Ω} [IsFiniteMeasure P]

/-- The integral functional `integralL2 P` evaluated on the L² lift of
a `MemLp raw 2 P` function equals the ordinary integral.

Proof: unfold `integralL2 P` to `⟪oneL2 P, ·⟫`, then `L2.inner_def` to
the integral of the pointwise inner product, then identify `oneL2 P`
with `1` and `(hf.toLp).val` with `f` on the AE side. The real inner
product `⟪a, b⟫_ℝ` reduces to `b * a`. -/
private lemma integralL2_toLp_eq_integral
    {f : Ω → ℝ} (hf : MemLp f 2 P) :
    integralL2 P (hf.toLp f) = ∫ ω, f ω ∂P := by
  change ⟪oneL2 P, hf.toLp f⟫_ℝ = _
  rw [MeasureTheory.L2.inner_def]
  have h_one_ae : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  have h_f_ae : ((hf.toLp f : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] f :=
    MemLp.coeFn_toLp hf
  apply integral_congr_ae
  filter_upwards [h_one_ae, h_f_ae] with a ha hb
  -- ⟪oneL2 P a, (hf.toLp f) a⟫_ℝ reduces by defeq to (hf.toLp f) a * oneL2 P a
  have hcomm :
      ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a,
        ((hf.toLp f : Lp ℝ 2 P) : Ω → ℝ) a⟫_ℝ
        = ((hf.toLp f : Lp ℝ 2 P) : Ω → ℝ) a
            * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
  rw [hcomm, ha, hb]
  ring

/-- Lift a candidate into the mean-zero L² subspace `L2ZeroMean P`. -/
noncomputable def toL2ZeroMean (φ : CandidateIF P) : ↥(L2ZeroMean P) :=
  ⟨φ.memLp2.toLp φ.raw, by
    -- L2ZeroMean P = ker (integralL2 P).toLinearMap
    change φ.memLp2.toLp φ.raw ∈ LinearMap.ker (integralL2 P).toLinearMap
    rw [LinearMap.mem_ker]
    change integralL2 P (φ.memLp2.toLp φ.raw) = 0
    rw [integralL2_toLp_eq_integral]
    exact φ.mean_zero⟩

/-- The underlying `Lp ℝ 2 P` function of `φ.toL2ZeroMean` agrees a.e.
with the raw representative `φ.raw`. -/
@[simp] theorem coeFn_toL2ZeroMean (φ : CandidateIF P) :
    ((φ.toL2ZeroMean : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] φ.raw :=
  MemLp.coeFn_toLp φ.memLp2

/-- Two candidates whose raw representatives agree almost everywhere
land at the same element of `L2ZeroMean P`.

This is the practical interface for concrete examples: the user
supplies a raw formula `φraw`, proves `φraw =ᵐ[P] canonicalFormula`,
and this lemma collapses the comparison to a one-line rewrite at the
L²₀ level. -/
theorem toL2ZeroMean_eq_of_aeEq
    {φ ψ : CandidateIF P} (h : φ.raw =ᵐ[P] ψ.raw) :
    φ.toL2ZeroMean = ψ.toL2ZeroMean := by
  apply Subtype.ext
  -- reduce equality of L²₀ elements to equality of underlying Lp elements
  change φ.memLp2.toLp φ.raw = ψ.memLp2.toLp ψ.raw
  exact MemLp.toLp_congr φ.memLp2 ψ.memLp2 h

end CandidateIF

end AsymptoticStatistics.Core
