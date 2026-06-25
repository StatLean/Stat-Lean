import Mathlib.Analysis.Calculus.MeanValue

/-!
# Second-order Taylor upper bound for a function with bounded second derivative

`ψ(a+h) − ψ(a) − h·ψ'(a) ≤ (B²/2)·h²` whenever the second derivative satisfies `ψ'' ≤ B²`.
The single analytic brick behind the GLM score's sub-Gaussian MGF (Wainwright, *High-Dimensional
Statistics*, proof of Corollary 9.26, p. 288): `log 𝔼[e^{−tVᵢⱼ}] = ψ(ηᵢ+txᵢⱼ) − ψ(ηᵢ) − txᵢⱼψ'(ηᵢ) ≤ B²t²xᵢⱼ²/2`.

`ForMathlib` layer — Mathlib-only, theorem-agnostic. The bound holds for all `h` (both signs):
`g(h) := ψ(a+h) − ψ(a) − h·ψ'(a)` satisfies `g(0) = 0`, `g'(0) = 0`, and `g'' = ψ''(a+·) ≤ B²`, so
`g(h) − (B²/2)h²` is concave with a maximum (value `0`) at `h = 0`.
-/

namespace StatLean.HighDimensionalStatistics

/-- Second-order Taylor upper bound under `ψ'' ≤ B²`:
`ψ(a + h) − ψ(a) − h·ψ'(a) ≤ (B²/2)·h²` for every `a, h`. Only the upper bound on `ψ''` is needed
(no lower bound): `h ↦ g(h) − (B²/2)h²` is concave with `g(0) = g'(0) = 0`. -/
theorem psi_taylor_upper (ψ ψ' ψ'' : ℝ → ℝ) (B : ℝ)
    -- USER-INPUT: `ψ'` is the derivative of `ψ`; Wainwright §9.1 (partition function, smooth).
    (hψ' : ∀ x, HasDerivAt ψ (ψ' x) x)
    -- USER-INPUT: `ψ''` is the derivative of `ψ'`; Wainwright §9.1.
    (hψ'' : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    -- USER-INPUT: bounded second derivative `ψ'' ≤ B²` (G2); Wainwright §9.5 (G2).
    (hbound : ∀ x, ψ'' x ≤ B ^ 2)
    (a h : ℝ) :
    ψ (a + h) - ψ a - h * ψ' a ≤ B ^ 2 / 2 * h ^ 2 := by
  sorry

end StatLean.HighDimensionalStatistics
