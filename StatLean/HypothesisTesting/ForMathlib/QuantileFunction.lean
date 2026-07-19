import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Quantile (generalized inverse) of a distribution function — ForMathlib brick

The **quantile function** of a nondecreasing `F : ℝ → ℝ` is
`quantile F p = inf {x | p ≤ F x}`. Three uses drive this file:

* the **Galois property** `quantile F p ≤ x ↔ p ≤ F x` (for right-continuous nondecreasing
  `F`), the workhorse identity behind every quantile computation;
* the **critical constants of a randomized test**: for a law `P` on `ℝ` and a level
  `α ∈ (0,1)` there are `C` and `γ ∈ [0,1]` with `P(C,∞) + γ·P{C} = α`, i.e. the level can
  always be met exactly by randomizing on the boundary atom (`exists_critical_constants`);
* **inverse-transform sampling** `quantile F` pushes the uniform law on `[0,1]` to `P`, and
  the two convergence statements (deterministic, and in probability for random distribution
  functions) that quantile-based calibration arguments consume.

Mathlib-only; nothing here mentions tests or models.

**Reference.** Classical distribution-function theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* `quantile` uses the `Real.sInf` junk conventions: the infimum of an empty or
  unbounded-below set is `0`. Every statement below therefore carries either an explicit
  nonemptiness/bounded-below side condition or a hypothesis (`StrictMono F`, `F` a genuine
  distribution function, `0 < p < 1`) that rules the junk out. `map_quantile_uniform` is the
  one place where junk survives — at the two endpoints `p ∈ {0,1}` — and is harmless there,
  since a pushforward only depends on the map up to a Lebesgue-null set.
* Right continuity is written `ContinuousWithinAt F (Set.Ici y) y`; it is used exactly once,
  in the forward direction of `quantile_le_iff` (to know that the infimum is attained).
* `tendsto_quantile_of_tendsto` needs neither continuity of the limit `F` nor any tail
  behaviour of the approximants: strict monotonicity of `F` at the target point plus
  monotonicity of each approximant already gives the two-sided bracketing. The same
  bracketing, run under the measure, gives `tendstoInMeasure_quantile`; no measurability of
  the random distribution functions is required, because the argument only ever compares
  measures of nested sets.
* The concept layer of this area carries the same formula under the name `cdfPseudoInverse`
  (bootstrap data model). That duplicate predates this brick; the intended end state is for
  the concept-layer name to be an abbreviation of `quantile`, which the bottom layer cannot
  do itself (it must not import the concept layer).

**Bibliographic comments.** The generalized inverse of a distribution function and its Galois
property are classical folklore of measure-theoretic probability, with no single seminal
source; the quantile transform as a construction of a random variable with a prescribed law
goes back to the beginnings of the subject (cf. P. Lévy, *Théorie de l'addition des variables
aléatoires*, Gauthier-Villars, 1937). The existence of the boundary-randomization constants
`(C, γ)` realizing a prescribed level exactly is the device introduced by J. Neyman and
E. S. Pearson ("On the problem of the most efficient tests of statistical hypotheses,"
*Phil. Trans. R. Soc. A* **231** (1933), 289–337).
-/

open Filter MeasureTheory
open scoped ENNReal Topology

namespace StatLean.HypothesisTesting

/-- The **quantile function** (generalized inverse) of `F`: `quantile F p = inf {x | p ≤ F x}`.

Junk conventions: the infimum of the empty set and of a set unbounded below is `0`, so for
`p` outside the range of a genuine distribution function this returns `0`. -/
noncomputable def quantile (F : ℝ → ℝ) (p : ℝ) : ℝ :=
  sInf {x : ℝ | p ≤ F x}

/-- The quantile function is nondecreasing in the level. -/
theorem quantile_mono (F : ℝ → ℝ) {p q : ℝ}
    -- USER-INPUT: the two levels, ordered; classical
    (hpq : p ≤ q)
    -- LEAN-ONLY: excludes the `sInf` junk of an unbounded-below sublevel set
    (hbdd : BddBelow {x : ℝ | p ≤ F x})
    -- LEAN-ONLY: excludes the `sInf ∅ = 0` junk at the upper level
    (hne : {x : ℝ | q ≤ F x}.Nonempty) :
    quantile F p ≤ quantile F q := by
  sorry

/-- **Galois property** of the quantile function: for a nondecreasing, right-continuous `F`,
`quantile F p ≤ x` iff `p ≤ F x`.

(This is the statement listed as `le_quantile_iff` in the area outline; it is named here for
the side of the inequality it decides, following the Mathlib convention.) -/
theorem quantile_le_iff {F : ℝ → ℝ} {p x : ℝ}
    -- USER-INPUT: `F` is a distribution function — nondecreasing; classical
    (hmono : Monotone F)
    -- USER-INPUT: `F` is a distribution function — right-continuous; classical
    (hrc : ∀ y : ℝ, ContinuousWithinAt F (Set.Ici y) y)
    -- LEAN-ONLY: excludes the `sInf ∅ = 0` junk
    (hne : {y : ℝ | p ≤ F y}.Nonempty)
    -- LEAN-ONLY: excludes the `sInf` junk of an unbounded-below sublevel set
    (hbdd : BddBelow {y : ℝ | p ≤ F y}) :
    quantile F p ≤ x ↔ p ≤ F x := by
  sorry

/-- **Critical constants of a randomized test.** For any law `P` on `ℝ` and any level
`α ∈ (0,1)` there are a threshold `C` and a boundary weight `γ ∈ [0,1]` with
`P(C,∞) + γ·P{C} = α`: the level `α` can always be attained *exactly* by rejecting above `C`
and randomizing with probability `γ` on the atom at `C`.

This is the existence statement that every "there is a level-`α` test of the following form"
argument needs; the atom term is what makes it an equality rather than an inequality. -/
theorem exists_critical_constants (P : Measure ℝ) [IsProbabilityMeasure P] {α : ℝ}
    -- USER-INPUT: a nondegenerate level; Neyman–Pearson (1933)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C γ : ℝ, 0 ≤ γ ∧ γ ≤ 1 ∧
      (P {x : ℝ | C < x}).toReal + γ * (P {x : ℝ | x = C}).toReal = α := by
  sorry

/-- **Inverse-transform sampling**: the quantile function of the distribution function of `P`
pushes the uniform law on `[0,1]` forward to `P`.

The junk values of `quantile` at the endpoints `0` and `1` are irrelevant: they affect the
map on a Lebesgue-null set only. -/
theorem map_quantile_uniform (P : Measure ℝ) [IsProbabilityMeasure P] (F : ℝ → ℝ)
    -- USER-INPUT: `F` is the distribution function of `P`; classical
    (hF : ∀ x : ℝ, F x = (P (Set.Iic x)).toReal) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).map (quantile F) = P := by
  sorry

/-- For a strictly increasing `F`, the quantile at an attained level is the attaining point.
The helper that identifies the limit in the two convergence statements below. -/
theorem quantile_eq_of_strictMono {F : ℝ → ℝ} {p q : ℝ}
    -- USER-INPUT: strict monotonicity of the limiting distribution function; classical
    (hF : StrictMono F)
    -- USER-INPUT: the level `p` is attained at `q`; classical
    (hq : F q = p) :
    quantile F p = q := by
  sorry

/-- **Deterministic quantile convergence**: if nondecreasing `Fₙ` converge pointwise to a
strictly increasing `F` and the level `p` is attained by `F`, then the `Fₙ`-quantiles converge
to the `F`-quantile.

Neither continuity of `F` nor any tail behaviour of the `Fₙ` is needed: strict monotonicity of
`F` at the target already provides the two-sided bracketing. -/
theorem tendsto_quantile_of_tendsto {Fn : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {p q : ℝ}
    -- USER-INPUT: each approximant is a distribution function — nondecreasing; classical
    (hmono : ∀ n, Monotone (Fn n))
    -- USER-INPUT: strict monotonicity of the limiting distribution function; classical
    (hF : StrictMono F)
    -- USER-INPUT: the level `p` is attained at `q`; classical
    (hq : F q = p)
    -- USER-INPUT: pointwise convergence of the distribution functions; classical
    (hconv : ∀ x : ℝ, Tendsto (fun n => Fn n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => quantile (Fn n) p) atTop (𝓝 (quantile F p)) := by
  sorry

/-- **Quantile convergence in probability** for random distribution functions: if the random
nondecreasing `Fhat n ω` converge in probability, at every fixed argument, to a strictly
increasing `F`, then their `p`-quantiles converge in probability to the `F`-quantile.

The bracketing argument compares measures of nested sets only, so no measurability of
`ω ↦ Fhat n ω x` is assumed. -/
theorem tendstoInMeasure_quantile {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Fhat : ℕ → Ω → ℝ → ℝ} {F : ℝ → ℝ} {p q : ℝ}
    -- USER-INPUT: each realized approximant is nondecreasing; classical
    (hmono : ∀ (n : ℕ) (ω : Ω), Monotone (Fhat n ω))
    -- USER-INPUT: strict monotonicity of the limiting distribution function; classical
    (hF : StrictMono F)
    -- USER-INPUT: the level `p` is attained at `q`; classical
    (hq : F q = p)
    -- USER-INPUT: pointwise convergence in probability of the random distribution functions
    (hconv : ∀ x : ℝ, TendstoInMeasure μ (fun n ω => Fhat n ω x) atTop (fun _ => F x)) :
    TendstoInMeasure μ (fun n ω => quantile (Fhat n ω) p) atTop (fun _ => quantile F p) := by
  sorry

end StatLean.HypothesisTesting
