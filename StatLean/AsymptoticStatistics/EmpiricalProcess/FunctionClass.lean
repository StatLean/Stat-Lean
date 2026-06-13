import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Function classes for empirical-process theory: envelopes and sup-norm

A function class `F : Set (Ω → ℝ)` is the indexing set for the empirical
process `f ↦ G_n f`. Two basic data attached to such a class:

* an **envelope** `G : Ω → ℝ` dominating every `f ∈ F` pointwise, used
  to control tail behaviour of `G_n` (vdV §19.2 + the envelope-tail term
  in Lem 19.34).
* the **sup-norm** `‖z‖_F = sup_{f ∈ F} |z f|` of an evaluator
  `z : (Ω → ℝ) → ℝ`, used to state Glivenko–Cantelli's `‖P_n − P‖_F → 0`
  and Donsker's tightness in `ℓ^∞(F)`.

Headline declarations: `IsEnvelope`, `supNormOver`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §19.2.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open scoped ENNReal

variable {Ω : Type*}

/-- A function `G : Ω → ℝ` is an **envelope** for a class `F` if
`|f x| ≤ G x` for every `f ∈ F` and every `x ∈ Ω`.

The envelope's role is to control the tail behaviour of the empirical
process: vdV §19.2 + Lem 19.34 use `G ∈ L^2(P)` (or similar) as a
hypothesis for Donsker-class results.

vdV §19.2: `G_n`'s sample paths are uniformly bounded when `F` has an
integrable envelope; envelope-driven tail conditions appear throughout §19. -/
def IsEnvelope (F : Set (Ω → ℝ)) (G : Ω → ℝ) : Prop :=
  ∀ f ∈ F, ∀ x, |f x| ≤ G x

lemma IsEnvelope.nonneg {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hG : IsEnvelope F G) {f : Ω → ℝ} (hf : f ∈ F) (x : Ω) : 0 ≤ G x :=
  (abs_nonneg (f x)).trans (hG f hf x)

lemma IsEnvelope.mono {F F' : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hG : IsEnvelope F G) (hF' : F' ⊆ F) : IsEnvelope F' G :=
  fun f hf x => hG f (hF' hf) x

/-- The **sup-norm** `‖z‖_F = sup_{f ∈ F} |z f|` of an evaluator
`z : (Ω → ℝ) → ℝ` over a class `F`, measured in `ℝ≥0∞` to handle
the unbounded case cleanly.

Edge: `F = ∅ ⇒ 0` (the supremum over an empty index is `⊥ = 0` in
`ℝ≥0∞`).

Used to state the `‖P_n − P‖_F` form of Glivenko–Cantelli conclusions
and the asymptotic-tightness side of Donsker's theorem. -/
noncomputable def supNormOver (F : Set (Ω → ℝ)) (z : (Ω → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ f ∈ F, ENNReal.ofReal |z f|

lemma le_supNormOver {F : Set (Ω → ℝ)} {z : (Ω → ℝ) → ℝ}
    {f : Ω → ℝ} (hf : f ∈ F) :
    ENNReal.ofReal |z f| ≤ supNormOver F z :=
  le_iSup₂ (f := fun f _ => ENNReal.ofReal |z f|) f hf

lemma supNormOver_mono {F F' : Set (Ω → ℝ)} (hF : F ⊆ F') (z : (Ω → ℝ) → ℝ) :
    supNormOver F z ≤ supNormOver F' z :=
  iSup₂_le fun _ hf => le_supNormOver (hF hf)

end AsymptoticStatistics.EmpiricalProcess
