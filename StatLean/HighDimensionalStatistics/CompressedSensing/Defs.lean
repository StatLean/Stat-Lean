import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
import StatLean.HighDimensionalStatistics.LinearModel.Defs

/-!
# Compressed sensing — definitions

Book setup (Lu, *Big Data Analysis* ch. 6–7): the noiseless sparse linear model
`Y = X β*` with `X ∈ ℝ^{n×d}`, `n ≪ d`, and `β*` sparse. The recovery method is
**basis pursuit** — the ℓ¹-minimisation `β̂ = argmin ‖β‖₁ s.t. Y = X β` — and the
sufficient condition for exact recovery is the **restricted isometry property**.

This concept-layer file gives the four book-facing predicates:

* `IsSparse s x`        — `x` has at most `s` nonzero coordinates (`‖x‖₀ ≤ s`, Lu §6).
* `IsBasisPursuit`      — `β̂` is feasible and ℓ¹-minimal (the basis-pursuit estimator, Lu §6).
* `IsUniqueBasisPursuit`— `β̂` is the *unique* basis-pursuit minimiser.
* `IsRIP X s δ`         — `X` satisfies the `s`-RIP with constant `δ` (Lu §7, RIP definition).

Reuses `l1Norm` / `EuclideanSpace` from `ForMathlib/VecNorms.lean` and the design
map `designMap X : β ↦ X β` from `LinearModel/Defs.lean`. The cone `C(S)` is the
existing `reCone S 1` (`Lasso/Defs.lean`); the null space is
`LinearMap.ker (designMap X)`.
-/

open Matrix

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **`s`-sparsity** (Lu §6, `‖β‖₀ = ∑ⱼ 𝟙{βⱼ ≠ 0}`): `x` is `s`-sparse when its
support is contained in some index set of cardinality at most `s`. Stated in the
"support fits in a set" form (decidability-free, and the form the recovery proofs
consume) rather than via an `ℓ₀` counting function. -/
def IsSparse (s : ℕ) (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ S : Finset (Fin d), S.card ≤ s ∧ ∀ i ∉ S, x.ofLp i = 0

/-- **Basis-pursuit estimator predicate** (Lu §6): `βhat` is feasible
(`X βhat = Y`) and has minimal ℓ¹ norm among all feasible points. The
optimisation is `β̂ = argmin_β ‖β‖₁  s.t.  Y = X β`. -/
def IsBasisPursuit (X : Matrix (Fin n) (Fin d) ℝ) (Y : EuclideanSpace ℝ (Fin n))
    (βhat : EuclideanSpace ℝ (Fin d)) : Prop :=
  designMap X βhat = Y ∧ ∀ β, designMap X β = Y → l1Norm βhat ≤ l1Norm β

/-- **Unique basis-pursuit solution** (Lu §6, `thm:cone`): `βhat` is a basis-pursuit
minimiser, and every feasible point whose ℓ¹ norm does not exceed `‖βhat‖₁` equals
`βhat`. This is the "`β̂ = β*` is the unique solution" conclusion of the cone theorem. -/
def IsUniqueBasisPursuit (X : Matrix (Fin n) (Fin d) ℝ) (Y : EuclideanSpace ℝ (Fin n))
    (βhat : EuclideanSpace ℝ (Fin d)) : Prop :=
  IsBasisPursuit X Y βhat ∧
    ∀ β, designMap X β = Y → l1Norm β ≤ l1Norm βhat → β = βhat

/-- **Restricted isometry property** (Lu §7, `Restricted isometry property`): `X`
satisfies the `s`-RIP with constant `δ ∈ (0,1)` when, for every `s`-sparse `β`,
`(1 − δ)‖β‖₂² ≤ ‖X β‖₂² ≤ (1 + δ)‖β‖₂²`. The constant `δ` (the restricted isometry
constant `δ_s`) is left as a free parameter; the threshold `δ ∈ (0,1)` is imposed by
the consumers, not here. -/
def IsRIP (X : Matrix (Fin n) (Fin d) ℝ) (s : ℕ) (δ : ℝ) : Prop :=
  ∀ β : EuclideanSpace ℝ (Fin d), IsSparse s β →
    (1 - δ) * ‖β‖ ^ 2 ≤ ‖designMap X β‖ ^ 2 ∧ ‖designMap X β‖ ^ 2 ≤ (1 + δ) * ‖β‖ ^ 2

end StatLean.HighDimensionalStatistics
