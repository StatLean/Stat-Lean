import Mathlib.Algebra.Group.Action.Defs
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite group actions: orbit averaging and the invariant σ-algebra — ForMathlib brick

Let a **finite** group `G` act measurably on `𝓧`. Averaging a function along the orbits,
$$ (A_G f)(x) \;=\; \frac{1}{|G|}\sum_{g \in G} f(g\cdot x), $$
produces an invariant function; if the underlying measure is `G`-invariant, this average is
*exactly* the conditional expectation of `f` given the σ-algebra of invariant sets. That
identity is what turns an invariance reduction into a conditioning argument (and, in the other
direction, an averaging argument into a statement about invariant tests).

This file provides:

* `IsInvariantSet G A` and `invariantSets G 𝓧` — the invariant sets, and the closure
  properties that make them a σ-algebra;
* `groupAverage G f` — the orbit average, with its invariance, measurability, and the
  measure-preserving identity `∫ A_G f dμ = ∫ f dμ`;
* `condExp_eq_groupAverage` — the conditional-expectation identity above.

**Carrier note (deliberate fallback).** The invariant sets are packaged as a *set of sets*,
`invariantSets G 𝓧`, together with the three closure lemmas (`empty`, `compl`, `iUnion`) that
would constitute a `MeasurableSpace` instance, rather than as such an instance. The
conditional-expectation statement therefore takes the invariant σ-algebra `m` as a parameter
plus the hypothesis `hm_inv` characterizing its measurable sets, which is exactly what a later
bundling would supply. This keeps the bottom layer free of a data model that the concept layer
may want to shape differently, and costs the consumer one hypothesis: a concept-layer
`MeasurableSpace` whose `MeasurableSet'` field is the conjunction "measurable and fixed by
every group element" discharges `hm_inv` by `fun _ => Iff.rfl`.

**Naming note.** The concept layer of this area already carries the same formula under the name
`orbitAverage` (invariant-test data model). The two live in one namespace, so this brick uses
`groupAverage`; the intended end state is for the concept-layer name to abbreviate this one,
which the bottom layer cannot arrange itself (it must not import the concept layer).

**Reference.** Classical invariance and ergodic-averaging theory; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* Measurability of the action is never an instance here: each statement that needs it takes
  `hmeas : ∀ g : G, Measurable (fun x : 𝓧 => g • x)` explicitly, so the file imposes no
  `MeasurableSMul` requirement on its consumers.
* `groupAverage_smul` is pure reindexing (`g ↦ h * g` is a bijection of `G`) and needs no
  measure-theoretic input; invariance of `μ` enters only in `integral_groupAverage` and
  `condExp_eq_groupAverage`.
* Intended route for `condExp_eq_groupAverage`: `groupAverage G f` is invariant, hence
  `m`-measurable via `hm_inv` and `preimage_mem_invariantSets`; and for `A ∈ m` invariance of
  `A` plus invariance of `μ` gives `∫_A f (g · x) dμ = ∫_A f dμ` for every `g`, so averaging
  over `g` matches the defining property of the conditional expectation. `IsFiniteMeasure μ`
  supplies the σ-finiteness of the trimmed measure that `condExp` requires; `hm ≤ m𝓧` is not a
  hypothesis, being forced by `hm_inv`.

**Bibliographic comments.** Invariance as a reduction principle for testing problems is due to
G. A. Hunt and C. Stein ("Most stringent tests of statistical hypotheses," unpublished, 1946).
The identification of the conditional expectation given the invariant σ-algebra with an orbit
average is the finite-group case of the mean ergodic theorem (J. von Neumann, "Proof of the
quasi-ergodic hypothesis," *Proc. Natl. Acad. Sci. USA* **18** (1932), 70–82;
G. D. Birkhoff, "Proof of the ergodic theorem," *ibid.*, 656–660).
-/

open MeasureTheory

namespace StatLean.HypothesisTesting

variable {G 𝓧 : Type*} [Group G] [m𝓧 : MeasurableSpace 𝓧] [MulAction G 𝓧]

/-- An **invariant set**: fixed by every element of the group. -/
def IsInvariantSet (G : Type*) [Group G] [MulAction G 𝓧] (A : Set 𝓧) : Prop :=
  ∀ g : G, (fun x : 𝓧 => g • x) ⁻¹' A = A

/-- The **invariant sets**: the measurable sets fixed by every element of the group. The
carrier of the invariant σ-algebra (see the carrier note in the file header). -/
def invariantSets (G 𝓧 : Type*) [Group G] [MeasurableSpace 𝓧] [MulAction G 𝓧] :
    Set (Set 𝓧) :=
  {A | MeasurableSet A ∧ IsInvariantSet G A}

/-- The **orbit average** `|G|⁻¹ ∑_{g ∈ G} f(g·x)` of a function along a finite group action. -/
noncomputable def groupAverage (G : Type*) [Group G] [Fintype G] [MulAction G 𝓧] (f : 𝓧 → ℝ)
    (x : 𝓧) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g : G, f (g • x)

/-! ### The invariant sets form a σ-algebra -/

/-- σ-algebra bookkeeping: the empty set is invariant. -/
theorem empty_mem_invariantSets : (∅ : Set 𝓧) ∈ invariantSets G 𝓧 := by
  sorry

/-- σ-algebra bookkeeping: invariant sets are closed under complement. -/
theorem compl_mem_invariantSets {A : Set 𝓧}
    -- USER-INPUT: the set to be complemented is invariant and measurable; classical
    (hA : A ∈ invariantSets G 𝓧) :
    Aᶜ ∈ invariantSets G 𝓧 := by
  sorry

/-- σ-algebra bookkeeping: invariant sets are closed under countable unions. -/
theorem iUnion_mem_invariantSets {A : ℕ → Set 𝓧}
    -- USER-INPUT: each set of the sequence is invariant and measurable; classical
    (hA : ∀ n, A n ∈ invariantSets G 𝓧) :
    (⋃ n, A n) ∈ invariantSets G 𝓧 := by
  sorry

/-- Preimages of measurable sets under an invariant measurable statistic are invariant: this is
how invariant functions are seen to be measurable for the invariant σ-algebra. -/
theorem preimage_mem_invariantSets {𝓘 : Type*} [MeasurableSpace 𝓘] {h : 𝓧 → 𝓘}
    -- LEAN-ONLY: measurability of the statistic; standard regularity
    (hmeas : Measurable h)
    -- USER-INPUT: the statistic is invariant along the orbits; Hunt–Stein (1946)
    (hinv : ∀ (g : G) (x : 𝓧), h (g • x) = h x)
    {B : Set 𝓘}
    -- LEAN-ONLY: measurability of the target set; standard regularity
    (hB : MeasurableSet B) :
    h ⁻¹' B ∈ invariantSets G 𝓧 := by
  sorry

/-! ### The orbit average -/

variable [Fintype G]

/-- The orbit average is invariant along the orbits. -/
theorem groupAverage_smul (f : 𝓧 → ℝ) (g : G) (x : 𝓧) :
    groupAverage G f (g • x) = groupAverage G f x := by
  sorry

/-- The orbit average of a measurable function is measurable. -/
theorem measurable_groupAverage {f : 𝓧 → ℝ}
    -- LEAN-ONLY: measurability of the integrand; standard regularity
    (hf : Measurable f)
    -- LEAN-ONLY: the action is by measurable maps; standard regularity
    (hmeas : ∀ g : G, Measurable (fun x : 𝓧 => g • x)) :
    Measurable (groupAverage G f) := by
  sorry

/-- Averaging an already invariant function changes nothing. -/
theorem groupAverage_of_isInvariant {f : 𝓧 → ℝ}
    -- USER-INPUT: the function is invariant along the orbits; Hunt–Stein (1946)
    (hinv : ∀ (g : G) (x : 𝓧), f (g • x) = f x) :
    groupAverage G f = f := by
  sorry

/-- **Orbit averaging preserves the integral** against an invariant measure. -/
theorem integral_groupAverage (μ : Measure 𝓧) {f : 𝓧 → ℝ}
    -- LEAN-ONLY: the action is by measurable maps; standard regularity
    (hmeas : ∀ g : G, Measurable (fun x : 𝓧 => g • x))
    -- USER-INPUT: the measure is invariant under the group; Hunt–Stein (1946)
    (hμ : ∀ g : G, μ.map (fun x : 𝓧 => g • x) = μ)
    -- LEAN-ONLY: integrability of the integrand; standard regularity
    (hf : Integrable f μ) :
    ∫ x, groupAverage G f x ∂μ = ∫ x, f x ∂μ := by
  sorry

/-- **Conditional expectation given the invariant σ-algebra is the orbit average**, for a
`G`-invariant measure and a finite group.

The invariant σ-algebra enters as a parameter `m` characterized by `hm_inv`; that `m` is a
sub-σ-algebra of the ambient one is forced by `hm_inv` and derived in the proof, not
assumed. -/
theorem condExp_eq_groupAverage (m : MeasurableSpace 𝓧)
    -- USER-INPUT: `m` is the σ-algebra of invariant sets; Hunt–Stein (1946)
    (hm_inv : ∀ s : Set 𝓧, MeasurableSet[m] s ↔ s ∈ invariantSets G 𝓧)
    (μ : Measure 𝓧)
    -- LEAN-ONLY: finiteness gives σ-finiteness of the trimmed measure, required by `condExp`
    [IsFiniteMeasure μ]
    -- LEAN-ONLY: the action is by measurable maps; standard regularity
    (hmeas : ∀ g : G, Measurable (fun x : 𝓧 => g • x))
    -- USER-INPUT: the measure is invariant under the group; Hunt–Stein (1946)
    (hμ : ∀ g : G, μ.map (fun x : 𝓧 => g • x) = μ)
    {f : 𝓧 → ℝ}
    -- LEAN-ONLY: integrability of the integrand; standard regularity
    (hf : Integrable f μ) :
    μ[f | m] =ᵐ[μ] groupAverage G f := by
  sorry

end StatLean.HypothesisTesting
