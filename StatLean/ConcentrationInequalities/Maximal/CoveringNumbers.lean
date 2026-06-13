import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# ε-Nets and covering numbers (Lu-BDA §4.2)

Book-facing definitions for the ε-net and covering-number vocabulary of
Lu, *Big Data Analysis* §4.2.  All non-trivial combinatorial content is
delegated to `Mathlib.Topology.MetricSpace.CoveringNumbers`.

## Main definitions

* `IsEpsilonNet N s ε` — `N ⊆ s` and every point of `s` lies within `dist ≤ ε`
  of some point of `N` (Lu §4.2, Definition of ε-net).
* `coveringNumber s ε` — minimum cardinality (in `ℕ∞`) of a finite internal
  ε-net of `s`; thin alias of `Metric.coveringNumber` (Lu §4.2, `N(s, d, ε)`).
-/

open Set
open scoped NNReal ENNReal

namespace StatLean.ConcentrationInequalities

variable {X : Type*} [PseudoMetricSpace X]

/-! ### ε-Net -/

/-- **ε-Net** (Lu-BDA §4.2 Definition).

A subset `N` of a pseudo-metric space `(X, d)` is an *ε-net* of `s ⊆ X` if:
- `N ⊆ s` (internal: the net lies inside the set), and
- `∀ x ∈ s, ∃ y ∈ N, dist x y ≤ ε` (every point of `s` is ε-close to some net point).

Also called an *internal ε-cover* in the literature (see `Metric.IsCover`).

Edge behaviour: for `ε < 0` the distance condition is impossible (distances are
non-negative), so `IsEpsilonNet N s ε` forces `s = ∅`.  For `ε = 0` in a metric
space, `dist x y ≤ 0 ↔ x = y`, so one needs `N = s`. -/
def IsEpsilonNet (N : Set X) (s : Set X) (ε : ℝ) : Prop :=
  N ⊆ s ∧ ∀ x ∈ s, ∃ y ∈ N, dist x y ≤ ε

/-! ### Covering number -/

/-- **Covering number** `N(s, d, ε)` (Lu-BDA §4.2).

The minimum cardinality (in `ℕ∞`) of a finite internal ε-net of `s ⊆ X`.
Returns `⊤` when no finite ε-net of `s` exists.

Thin alias of `Metric.coveringNumber (Real.toNNReal ε) s`.  The `toNNReal`
coercion clamps `ε ≤ 0` to `0`; for `ε = 0` this equals `s.encard`.

This is Lu-BDA §4.2's `N(s, d, ε)`. -/
noncomputable def coveringNumber (s : Set X) (ε : ℝ) : ℕ∞ :=
  Metric.coveringNumber (Real.toNNReal ε) s

/-! ### Sanity lemmas -/

/-- `s` is an ε-net of itself for any non-negative `ε`
(take `y = x`; then `dist x x = 0 ≤ ε`). -/
lemma isEpsilonNet_self (s : Set X) {ε : ℝ} (hε : 0 ≤ ε) : IsEpsilonNet s s ε :=
  ⟨le_refl s, fun x hx => ⟨x, hx, (dist_self x).le.trans hε⟩⟩

/-- The covering number is anti-monotone in the radius:
a smaller `ε` requires weakly more net points (Lu-BDA §4.2). -/
lemma coveringNumber_anti {s : Set X} {ε δ : ℝ} (h : ε ≤ δ) :
    coveringNumber s δ ≤ coveringNumber s ε :=
  Metric.coveringNumber_anti (Real.toNNReal_le_toNNReal h)

/-- If `N` is an ε-net of `s` (with `ε ≥ 0`), it is also a `Metric.IsCover`. -/
-- LEAN-ONLY: bridge to Mathlib's NNReal / edist API; no book content.
lemma IsEpsilonNet.isCover {N s : Set X} {ε : ℝ} (hε : 0 ≤ ε)
    (h : IsEpsilonNet N s ε) : Metric.IsCover (Real.toNNReal ε) s N := by
  intro x hx
  obtain ⟨y, hy, hd⟩ := h.2 x hx
  -- ↑(Real.toNNReal ε) : ENNReal = ENNReal.ofReal ε (definitionally), so edist_le_ofReal applies.
  exact ⟨y, hy, (edist_le_ofReal hε).mpr hd⟩

end StatLean.ConcentrationInequalities
