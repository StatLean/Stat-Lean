/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StatLean contributors
-/
import Mathlib.Topology.UnitInterval

/-!
# Probabilities in `ℝ≥0` as points of the unit interval

`unitInterval.ofNNReal p h` is a probability `p : ℝ≥0` with `h : p ≤ 1`, viewed as a point of the
unit interval `I`. StatLean's Bernoulli models take their success probabilities in `ℝ≥0`; this is
the parameter they pass to `ProbabilityTheory.bernoulliMeasure`.
-/

open scoped NNReal

namespace unitInterval

/-- A probability `p : ℝ≥0` with `p ≤ 1`, as a point of the unit interval. -/
def ofNNReal (p : ℝ≥0) (h : p ≤ 1) : I := ⟨p, p.2, by exact_mod_cast h⟩

@[simp] lemma coe_ofNNReal (p : ℝ≥0) (h : p ≤ 1) : (ofNNReal p h : ℝ) = p := rfl

@[simp] lemma toNNReal_ofNNReal (p : ℝ≥0) (h : p ≤ 1) : toNNReal (ofNNReal p h) = p := rfl

@[simp] lemma toNNReal_symm_ofNNReal (p : ℝ≥0) (h : p ≤ 1) :
    toNNReal (σ (ofNNReal p h)) = 1 - p := by
  ext
  simp [NNReal.coe_sub h]

end unitInterval
