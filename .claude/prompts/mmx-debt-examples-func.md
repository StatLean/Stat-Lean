# Close functional/location example construction debts

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds.

## Touch-set (edit ONLY)
- `Examples/LipschitzDensity.lean` (`lipschitz_pointwise_modulus_bound`, `quadratic_two_point_modulus_bound`)
- `Examples/QuadraticFunctional.lean` (the optimal-rate crux)
- `Examples/GaussianLocation.lean` (two-point Gaussian TV crux)
- `Examples/UniformLocation.lean` (`uniform_two_point_tvDist_bound`)
(paths under `StatLean/Minimaxity/`). Keep public signatures/docstrings UNCHANGED. Helpers `private`.
Black-box the method theorems + `klDiv_gaussianReal`, `lecam_tv_le_hellinger`, `sqHellinger_pi_le_nsmul`,
`pinsker_tv_le_kl`.

## Constructions (Wainwright §15.2)
- GaussianLocation (Ex 15.4): with `θ=2δ=σ/√n`, bound `‖P_θ^n − P_0^n‖_TV` via Pinsker:
  `klDiv (gaussianReal θ σ²)^n (gaussianReal 0 σ²)^n = n·θ²/(2σ²) = ½`, so `TV ≤ √(¼) = ½` ⇒ `1−TV ≥ ½`.
  Use `klDiv_gaussianReal` + `klDiv_pi_eq_nsmul` + `pinsker_tv_le_kl`. Rate `v/(24n)`.
- UniformLocation (Ex 15.5): `θ₁=1/n`; `H²(U_0‖U_{1/n}) = 2/n` (shift overlap), so by `sqHellinger_pi_le_nsmul`
  `H²(U_0^n‖U_{1/n}^n) ≤ n·2/n = 2`?? — recompute: Wainwright takes `|θ'−θ|=1/(4n)`, `H²(U^n) ≤ ½`, then
  `lecam_tv_le_hellinger` ⇒ `1−TV ≥ (1−1/√2)/2`. Establish `H²(Uniform[0,1]‖Uniform[θ,θ+1]) = 2|θ|`
  (volume of symmetric difference / `volume.restrict` overlap) then tensorize. Rate `(1−1/√2)/128·n⁻²`.
- LipschitzDensity (Ex 15.7): hat function `φ(x)=δ−|x|` on `[−δ,δ]`, `f₀≡1`, `g=f₀+φ` with `H²(f₀‖g)=1/(4n)`
  ⇒ `δ ≍ n^{−1/3}`, `|f₀(0)−g(0)|=δ ≍ n^{−1/3}`, so `ω(1/(2√n)) ≳ n^{−1/3}`, rate `n^{−2/3}`. The Hellinger
  Taylor bound: `½H²(f₀‖g) ≤ ⅛∫φ² ` (via `√(1+u)` 2nd-order), `∫φ² = (4/3)δ³`. (Ex 15.8 quadratic similar, n^{−1/2}.)
- QuadraticFunctional (Ex 15.11): the sign-vector family `f_α=1+Σα_jφ_j`, optimal n^{−4/9} via convex-hull.

These are real analysis — `Real.sqrt`/Taylor bounds, `volume.restrict`, `MeasureTheory.lintegral`,
`integral` of polynomials. GOAL: close each; reduce any genuinely-stuck integral to a SMALLER named `private`
sorry + precise `-- TODO(mmx)`. Commit after EACH file builds.
## DONE: build each module green; `git add` only touch-set files. Report per-example closed/residual.
