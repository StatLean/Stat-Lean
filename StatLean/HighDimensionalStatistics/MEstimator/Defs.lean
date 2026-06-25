import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Regularized M-estimators: decomposable regularizers and restricted strong convexity

Concept-layer definitions for the `MEstimator` milestone (Wainwright, *High-Dimensional
Statistics*, Chapter 9). These formalize the general regularized M-estimator
`θ̂ ∈ argmin_θ { Lₙ(θ) + λₙ·Φ(θ) }` (eq 9.3) and the two structural ingredients of the
estimation-error theory:

* **decomposability** of the regularizer `Φ` with respect to a subspace pair `(M, M̄ᗮ)`
  (Definition 9.9), bundled together with the dual norm `Φ*` in `DecomposableReg`;
* **restricted strong convexity** (RSC, Definition 9.15) and the dual `Φ*`-norm curvature
  condition (Definition 9.22) of the cost `Lₙ`.

The space `E` is a finite-dimensional real inner-product space; `‖·‖` is the inner-product
norm and `Φ` is a *separate* regularizer norm (e.g. `ℓ₁` while `‖·‖ = ℓ₂`). All projections
`Δ_M`, `Δ_{M̄}`, `θ*_{Mᗮ}`, … are **orthogonal** projections w.r.t. `⟨·,·⟩`, realized by
`Submodule.starProjection` (the `E`-valued orthogonal projection).

Laptop-only shared data model: this file fixes the encodings consumed by the deterministic
assembly (`Deviation`, `Bound`, `DualBound`) and the GLM assembly.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open scoped InnerProductSpace

/-- A **decomposable regularizer** together with its dual norm and ambient subspace pair
(Wainwright §9.2). Bundling the dual norm `Φstar` with the Hölder and tightness fields is exactly
"`Φ*` is the dual norm of `Φ`" (eq 9.27, `Φ*(v) = sup_{Φ(u)≤1} ⟨u,v⟩`): `holder` is the
`≥`-direction for every `u`, and `tight` is the variational characterization that pins `Φ*` down
as the *smallest* norm satisfying Hölder. -/
structure DecomposableReg (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- Constitutive (Wainwright §9.2.1): the model subspace `M` (the structure expected of `θ*`). -/
  M : Submodule ℝ E
  /-- Constitutive (Wainwright §9.2.1, eq 9.21): the subspace `M̄ ⊇ M` whose orthogonal complement
  `M̄ᗮ` is the perturbation subspace; in the ideal case `M̄ = M`. -/
  Mbar : Submodule ℝ E
  /-- Constitutive (Wainwright §9.2.1): the subspace pair satisfies `M ⊆ M̄`. -/
  subset_Mbar : M ≤ Mbar
  /-- Constitutive (Wainwright §9.1): the regularizer `Φ`, a norm on `E`. -/
  Φ : Seminorm ℝ E
  /-- Constitutive (Wainwright eq 9.27): the dual norm `Φ*`. -/
  Φstar : Seminorm ℝ E
  /-- Constitutive (Wainwright eq 9.27): generalized Hölder `⟨u,v⟩ ≤ Φ(u)·Φ*(v)`. -/
  holder : ∀ u v : E, ⟪u, v⟫_ℝ ≤ Φ u * Φstar v
  /-- Constitutive (Wainwright eq 9.27): `Φ*` is the *least* norm satisfying Hölder, i.e. the
  variational characterization `Φ*(v) ≤ c` whenever `⟨u,v⟩ ≤ c` for all `Φ(u) ≤ 1`. -/
  tight : ∀ (v : E) (c : ℝ), (∀ u : E, Φ u ≤ 1 → ⟪u, v⟫_ℝ ≤ c) → Φstar v ≤ c
  /-- Constitutive (Wainwright Def 9.9, eq 9.22): decomposability of `Φ` over `(M, M̄ᗮ)`,
  `Φ(α + β) = Φ(α) + Φ(β)` for `α ∈ M`, `β ∈ M̄ᗮ`. -/
  decomp : ∀ α ∈ M, ∀ β ∈ (Mbar)ᗮ, Φ (α + β) = Φ α + Φ β

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The **first-order Taylor-series error** `Eₙ(Δ) = Lₙ(θ + Δ) − Lₙ(θ) − ⟪∇Lₙ(θ), Δ⟫`
(Wainwright eq 9.36). For convex `Lₙ` this is `≥ 0`; restricted strong convexity lower-bounds it
by a quadratic minus a regularizer-slack term. -/
noncomputable def taylorErr (L : E → ℝ) (θ Δ : E) : ℝ :=
  L (θ + Δ) - L θ - ⟪gradient L θ, Δ⟫_ℝ

/-- **Restricted strong convexity** `RSC(κ, R, τ²)` (Wainwright Def 9.15, eq 9.38):
`Eₙ(Δ) ≥ (κ/2)‖Δ‖² − τ²·Φ(Δ)²` for every `Δ` in the ball `‖Δ‖ ≤ R`. Here `τSq = τ_n²` is the
squared tolerance and `κ` the curvature. -/
def RSC (L : E → ℝ) (θ : E) (Φ : Seminorm ℝ E) (κ R τSq : ℝ) : Prop :=
  ∀ Δ : E, ‖Δ‖ ≤ R → taylorErr L θ Δ ≥ κ / 2 * ‖Δ‖ ^ 2 - τSq * (Φ Δ) ^ 2

/-- The **subspace Lipschitz constant** `Ψ(S) = sup_{u ∈ S∖{0}} Φ(u)/‖u‖` (Wainwright Def 9.18,
eq 9.44): the worst-case ratio of the regularizer to the error norm, restricted to `S`. Edge
behavior: `Ψ(0) = sSup ∅ = 0`. -/
noncomputable def subspaceLip (Φ : Seminorm ℝ E) (S : Submodule ℝ E) : ℝ :=
  sSup ((fun u => Φ u / ‖u‖) '' ((S : Set E) \ {0}))

/-- The **good event** `𝔾(λ) = {Φ*(∇Lₙ(θ*)) ≤ λ/2}` (Wainwright eq 9.28/9.46), as a predicate on
the score vector `g = ∇Lₙ(θ*)`: the regularization weight dominates twice the dual norm of the
score. -/
def GoodEvent (Φstar : Seminorm ℝ E) (g : E) (lam : ℝ) : Prop :=
  Φstar g ≤ lam / 2

/-- The **objective increment** `ℱ(Δ) = L(θ*+Δ) − L(θ*) + λ·(Φ(θ*+Δ) − Φ(θ*))` (Wainwright eq 9.31).
By construction `ℱ(0) = 0`; optimality of `θ̂` forces `ℱ(θ̂ − θ*) ≤ 0`. Convex in `Δ` when `L` and `Φ`
are convex and `λ ≥ 0`. -/
noncomputable def Fcal (L : E → ℝ) (Φ : Seminorm ℝ E) (θstar : E) (lam : ℝ) (Δ : E) : ℝ :=
  L (θstar + Δ) - L θstar + lam * (Φ (θstar + Δ) - Φ θstar)

/-- The **error cone** `ℂ(M, M̄ᗮ) = {Δ : Φ(Δ_{M̄ᗮ}) ≤ 3·Φ(Δ_{M̄}) + 4·Φ(θ*_{Mᗮ})}`
(Wainwright eq 9.29): on the good event the error `θ̂ − θ*` is guaranteed to lie here. -/
def errorCone (dr : DecomposableReg E) (θstar : E) : Set E :=
  {Δ : E | dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) ≤
      3 * dr.Φ (dr.Mbar.starProjection Δ) + 4 * dr.Φ ((dr.M)ᗮ.starProjection θstar)}

/-- The error quantity `εₙ²(M̄, Mᗮ)` governing the `ℓ₂` rate in Thm 9.19(b):
`144(λ²/κ²)·Ψ²(M̄) + (32/κ){λ·Φ(θ*_{Mᗮ}) + 16τ²·Φ(θ*_{Mᗮ})²}` — an estimation-error term plus an
approximation-error term. The `θ*` projection is onto `Mᗮ` (the proof projects `θ*` onto the model
subspace `M`, as decomposability requires; the εₙ² argument label `(M̄, M^⊥)` confirms this).

**Book-constant deviation (Wainwright eq 9.47).** The book states leading `9`, slack `(8/κ)`, under
`τ²Ψ² ≤ κ/64`. Those are only achievable as `τ → 0`: the RSC lower bound is
`ℱ(Δ) ≥ (κ/2 − 32τ²Ψ²)‖Δ‖² − (3λ/2)Ψ‖Δ‖ − D`, so the effective curvature `c = κ/2 − 32τ²Ψ² < κ/2`,
and at `‖Δ‖² = 9(λ/κ)²Ψ²` one gets `ℱ < 0` for any `τ > 0` (Lemma 9.21's `ℱ > 0` fails). The provable
bound requires `τ²Ψ² ≤ κ/128` (so `c ≥ κ/4`) and uses the clean nlinarith-friendly threshold
`δ² > (2β/c)² + 2D/c` (`β = (3λ/2)Ψ`, `D = 2λΦ + 32τ²Φ²`), giving leading `144` (`√ = 12`) and slack
`(32/κ)`, with strict margin. Same rate `s·λ²/κ²`; only the constants differ. -/
noncomputable def epsilonSq (dr : DecomposableReg E) (θstar : E) (lam κ τSq : ℝ) : ℝ :=
  144 * (lam ^ 2 / κ ^ 2) * (subspaceLip dr.Φ dr.Mbar) ^ 2 +
    32 / κ * (lam * dr.Φ ((dr.M)ᗮ.starProjection θstar) +
      16 * τSq * (dr.Φ ((dr.M)ᗮ.starProjection θstar)) ^ 2)

/-- The **`Φ*`-norm curvature condition** (Wainwright Def 9.22, eq 9.55):
`Φ*(∇Lₙ(θ + Δ) − ∇Lₙ(θ)) ≥ κ·Φ*(Δ) − τ·Φ(Δ)` for all `Δ` with `Φ*(Δ) ≤ R`. This is the
dual-norm analogue of RSC, underlying the `ℓ∞` bound of Theorem 9.24. -/
def dualCurvature (L : E → ℝ) (θ : E) (Φ Φstar : Seminorm ℝ E) (κ τ R : ℝ) : Prop :=
  ∀ Δ : E, Φstar Δ ≤ R →
    Φstar (gradient L (θ + Δ) - gradient L θ) ≥ κ * Φstar Δ - τ * Φ Δ

end StatLean.HighDimensionalStatistics.MEstimator
