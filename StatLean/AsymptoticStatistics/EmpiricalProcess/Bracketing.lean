import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.ENat.Lattice

/-!
# Brackets and bracketing covers for empirical-process theory

A **bracket** `[l, u]` is a pair of functions `l ≤ u` pointwise. An
**ε-bracket** in `L_r(P)` is one whose `L_r(P)`-size `‖u − l‖_{P,r}`
is less than `ε`. A class `F` of measurable functions admits a
**finite ε-bracketing cover** if there are finitely many ε-brackets
that cover `F`: every `f ∈ F` lies pointwise inside some bracket. This
is the combinatorial input to vdV's bracketing-entropy theorems (vdV
§19.2, Theorems 19.4, 19.5).

Headline declarations: `IsBracket`, `IsEpsBracket`,
`HasFiniteBracketingCover`, `bracketingNumber`, `bracketingEntropyIntegral`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A pair `(l, u)` is a **bracket** if `l ≤ u` pointwise.

vdV §19.2: the underlying combinatorial unit of bracketing entropy. -/
def IsBracket (l u : Ω → ℝ) : Prop := ∀ x, l x ≤ u x

/-- An **ε-bracket** in `L_r(P)`: a bracket `[l, u]` with `l, u` measurable,
both in `L_r(P)`, and `‖u − l‖_{P,r} < ε`.

The integrability conditions on `l` and `u` are bundled here so that the
strong-LLN invocation in the proof of Theorem 19.4 can fire directly on
the bracket bounds: vdV §19.2 requires the bracketing functions `l` and
`u` to have finite `L_r(P)`-norms. Measurability is included so that
`IndepFun.comp` and `IdentDistrib.comp` can post-compose the iid sequence
by `l` / `u`.

vdV §19.2: `‖u − l‖_{P,r} < ε`. -/
def IsEpsBracket (ε : ℝ) (l u : Ω → ℝ) (r : ℝ≥0∞) (P : Measure Ω) : Prop :=
  IsBracket l u ∧ Measurable l ∧ Measurable u ∧ MemLp l r P ∧ MemLp u r P ∧
    eLpNorm (fun x => u x - l x) r P < ENNReal.ofReal ε

namespace IsEpsBracket

variable {ε : ℝ} {l u : Ω → ℝ} {r : ℝ≥0∞} {P : Measure Ω}

lemma isBracket (h : IsEpsBracket ε l u r P) : IsBracket l u := h.1

lemma measurable_lower (h : IsEpsBracket ε l u r P) : Measurable l := h.2.1

lemma measurable_upper (h : IsEpsBracket ε l u r P) : Measurable u := h.2.2.1

lemma memLp_lower (h : IsEpsBracket ε l u r P) : MemLp l r P := h.2.2.2.1

lemma memLp_upper (h : IsEpsBracket ε l u r P) : MemLp u r P := h.2.2.2.2.1

lemma size_lt (h : IsEpsBracket ε l u r P) :
    eLpNorm (fun x => u x - l x) r P < ENNReal.ofReal ε := h.2.2.2.2.2

end IsEpsBracket

/-- `F` admits a **finite ε-bracketing cover** in `L_r(P)`: there are
finitely many ε-brackets `[l_i, u_i]` such that every `f ∈ F` lies
pointwise inside some `[l_i, u_i]`.

vdV §19.2: `N_{[]}(ε, F, L_r(P)) < ∞`. The finite collection is encoded
as `Fin k`-indexed lower- and upper-bound functions; this matches the
proof of Theorem 19.4 where the strong LLN is applied to each `l i` and
`u i`.

Edge case: `F = ∅ ⇒ k = 0` works trivially. -/
def HasFiniteBracketingCover (F : Set (Ω → ℝ)) (ε : ℝ) (r : ℝ≥0∞) (P : Measure Ω) : Prop :=
  ∃ (k : ℕ) (l u : Fin k → Ω → ℝ),
    (∀ i, IsEpsBracket ε (l i) (u i) r P) ∧
    (∀ f ∈ F, ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x)

lemma HasFiniteBracketingCover.empty (ε : ℝ) (r : ℝ≥0∞) (P : Measure Ω) :
    HasFiniteBracketingCover (∅ : Set (Ω → ℝ)) ε r P := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_⟩
  · intro i; exact i.elim0
  · intro f hf; exact absurd hf (Set.notMem_empty f)

lemma HasFiniteBracketingCover.mono {F F' : Set (Ω → ℝ)} {ε : ℝ} {r : ℝ≥0∞} {P : Measure Ω}
    (h : HasFiniteBracketingCover F ε r P) (hF' : F' ⊆ F) :
    HasFiniteBracketingCover F' ε r P := by
  obtain ⟨k, l, u, hbr, hcov⟩ := h
  exact ⟨k, l, u, hbr, fun f hf => hcov f (hF' hf)⟩

/-- The **bracketing number** `N_{[]}(ε, F, L_r(P))` — the minimum size
of an ε-bracketing cover, valued in `ℕ∞`.

`bracketingNumber ε F r P = ⊤` iff no finite ε-bracketing cover exists;
otherwise it returns the smallest cover size as a finite `ℕ`.

vdV §19.2. -/
noncomputable def bracketingNumber
    (ε : ℝ) (F : Set (Ω → ℝ)) (r : ℝ≥0∞) (P : Measure Ω) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : ∃ l u : Fin k → Ω → ℝ,
      (∀ i, IsEpsBracket ε (l i) (u i) r P) ∧
      (∀ f ∈ F, ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x)),
    (k : ℕ∞)

/-- `bracketingNumber ε F r P < ⊤` iff `F` admits a finite ε-bracketing cover. -/
lemma bracketingNumber_lt_top_iff_HasFiniteBracketingCover
    {F : Set (Ω → ℝ)} {ε : ℝ} {r : ℝ≥0∞} {P : Measure Ω} :
    bracketingNumber ε F r P < ⊤ ↔ HasFiniteBracketingCover F ε r P := by
  refine ⟨?_, ?_⟩
  · intro hlt
    by_contra h_no_cover
    have h_all_top : ∀ k : ℕ,
        ¬ (∃ l u : Fin k → Ω → ℝ,
            (∀ i, IsEpsBracket ε (l i) (u i) r P) ∧
            (∀ f ∈ F, ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x)) := by
      intro k ⟨l, u, hbr, hcov⟩
      exact h_no_cover ⟨k, l, u, hbr, hcov⟩
    have h_top : bracketingNumber ε F r P = ⊤ := by
      unfold bracketingNumber
      apply le_antisymm le_top
      refine le_iInf fun k => ?_
      refine le_iInf fun hk => ?_
      exact absurd hk (h_all_top k)
    rw [h_top] at hlt
    exact lt_irrefl _ hlt
  · rintro ⟨k, l, u, hbr, hcov⟩
    refine lt_of_le_of_lt ?_ (ENat.coe_lt_top k)
    refine iInf_le_of_le k ?_
    exact iInf_le_of_le ⟨l, u, hbr, hcov⟩ le_rfl

open Filter

/-- The **bracketing entropy integral** `J_{[]}(δ, F, L_2(P))` —
the cumulative bracketing-entropy "size" of `F` from scale `0` up to `δ`,
weighted by `√(log N_{[]}(ε, F, L_2(P)))`.

vdV §19.2: `J_{[]}(δ, F, L_2(P)) = ∫_0^δ √(log N_{[]}(ε, F, L_2(P))) dε`.

The integrand at scale `ε` is obtained from `bracketingNumber ε F 2 P : ℕ∞`
by `ENat.recTopCoe`:
* if `bracketingNumber ε F 2 P = ⊤` (no finite ε-bracketing cover), the
  integrand value is `⊤ : ℝ≥0∞`;
* otherwise, with `n : ℕ` the underlying count, the integrand is
  `ENNReal.ofReal (√(log n))`.

The integral is taken over `Set.Ioc 0 δ` against Lebesgue `volume`. With
this convention `J_{[]}(δ, F, L_2(P)) = ⊤` whenever `bracketingNumber`
fails to be finite on a positive-measure subset of `(0, δ]`, faithfully
reflecting the textbook content.

vdV §19.2. -/
noncomputable def bracketingEntropyIntegral
    (δ : ℝ) (F : Set (Ω → ℝ)) (P : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ε in Set.Ioc 0 δ,
    ENat.recTopCoe (⊤ : ℝ≥0∞)
      (fun n : ℕ => ENNReal.ofReal (Real.sqrt (Real.log (n : ℝ))))
      (bracketingNumber ε F 2 P)
      ∂volume

end AsymptoticStatistics.EmpiricalProcess
