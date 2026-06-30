Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "..."` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries in the target file. Lift sub-steps to proven `private` helpers IN THIS FILE; NEVER `sorry`/`axiom`. This is the hardest example — work methodically; build helper lemmas bottom-up and `lake build` often.

# CONTEXT
File: `StatLean/Minimaxity/Examples/QuadraticFunctional.lean` (namespace `StatLean.Minimaxity`). The public
`quadratic_functional_optimal_rate` is ALREADY restructured (existential witness, support-restricted
`∀ i, ∀ x ∈ Set.Icc 0 1, 1/2 ≤ f i x`) and fully proven downstream via `minimax_le_cam_convex_hull`
(`LeCam/ConvexHull.lean`). The SOLE remaining `sorry` is the existential crux `quadratic_convex_hull_config`.
READ the current crux signature in the file and match it exactly — produce the `∃ δ, a₀, a₁, …, π₀, π₁, …`
witness it requires (two sub-families + priors, a `2δ`-separation of functional values, and an
`ofReal(c·n^{-4/9}) ≤ Φ(δ)/2·(1 − tvDist(mixture₀, mixture₁))` bound).

# CONSTRUCTION (Wainwright Ex 15.11, sign-vector family on [0,1])
`ι := (Fin m → Bool)` (sign vectors `α`), `m` with `m^9 ≍ n²` (`m := ⌈(4 b₀² n²)^{1/9}⌉₊`, constants loose).
Fixed bump `φ : ℝ → ℝ`, supported in `[0,1]`, `‖φ‖∞ ≤ 1/2`, `∫φ = 0`, `b₀ := ∫φ² > 0`, `b₁ := ∫(φ')² > 0`
(reuse / adapt the hat-style bump; you may pick a concrete smooth/​piecewise φ and prove these by direct
integration or translation-invariance). `φ_j(x) := (C/m²)·φ(m·x − j)` supported on `[j/m,(j+1)/m]` (disjoint).
`f_α := 1 + Σ_{j<m} σ(α j)·φ_j`, `σ b = if b then 1 else -1` (so `f_α ≥ 1/2` for `C` small). Functional
`θ(f) = ∫(f')²`: `θ(f_α) − θ(U) = Σ_j C²/m⁴ ∫(φ')²·m² = C²b₁/m²` (independent of α). Two sub-families: a `2δ`
gap with `δ ≍ C²b₁/m² ≍ n^{-2/9}` (e.g. compare `f_α` vs `U`; encode `a₀ ≡ const U-index`, `a₁ = id`, priors
`π₀ = δ_U`, `π₁ = uniform over α`).

# KEY BOUND (paper-free χ² route — replaces the cited Birgé–Massart 15.28; this is the heart)
Need `tvDist(U^n, Q) ≤ 1/2` where `Q = (uniform over α) ∘ Pⁿ_α` is the sign-vector mixture. Prove it via the
χ²/second-moment bound (cleaner than Hellinger-of-mixture):
1. `tvDist² ≤ ¼ χ²`  and  `H² ≤ χ²`; but most directly: `1 − 2·tvDist(U^n,Q) ≥ ...`. Use:
   `tvDist(U^n, Q) ≤ ½ √(χ²(Q ‖ U^n))` (from `‖P−Q‖_TV = ½∫|dP/dλ − dQ/dλ| ≤ ½√(∫(dQ/dU^n − 1)² dU^n)` by
   Cauchy–Schwarz). So it suffices to show `χ²(Q ‖ U^n) ≤ 1`.
2. **Compute χ²** `χ²(Q‖U^n) + 1 = ∫ (dQ/dU^n)² dU^n = E_{α,α'}[ ∏_{i<n} ∫₀¹ (1+Σⱼσ(αⱼ)φⱼ)(1+Σⱼσ(α'ⱼ)φⱼ) ]`
   `= E_{α,α'}[ (1 + Σⱼ σ(αⱼ)σ(α'ⱼ) bⱼ)^n ]` where `bⱼ = ∫₀¹ φⱼ² = C²b₀/m⁵`
   (uses `∫φⱼ = 0` and disjoint supports ⇒ `∫φⱼφₖ = 0` for `j≠k`). With `α,α'` uniform independent,
   `εⱼ := σ(αⱼ)σ(α'ⱼ)` are i.i.d. uniform `±1`, so `= E_ε[(1 + Σⱼ εⱼ bⱼ)^n]`.
3. **Bound** `E_ε[(1+Σεⱼbⱼ)^n] ≤ E_ε[exp(n Σεⱼbⱼ)] = ∏ⱼ cosh(n bⱼ) ≤ ∏ⱼ exp((n bⱼ)²/2) = exp((n²/2) Σⱼ bⱼ²)`
   (`1+t ≤ eᵗ`; `cosh t ≤ e^{t²/2}`). With `bⱼ = C²b₀/m⁵`, `Σⱼ bⱼ² = m·(C²b₀/m⁵)² = C⁴b₀²/m⁹`, so
   `χ²+1 ≤ exp((n²/2)·C⁴b₀²/m⁹)`. Choosing `m⁹ = 4b₀²n²` (and `C` small) gives `χ² ≤ exp(C⁴/8)−1 ≤ 1`,
   hence `tvDist ≤ ½`. Then `minimax_le_cam_convex_hull` ⇒ `≳ (δ/4)² ≍ n^{-4/9}` (squared).

You may need to BUILD a small `private` χ² lemma (`chiSqDiv`) in-file or bound the affinity directly; either
is fine. The project's `tvDist_eq_half_lintegral` (`ForMathlib/TotalVariation.lean`) gives the `½∫|·|` form;
`Measure.pi` independence + `lintegral_prod`/`rnDeriv` give the product factorization. Search bricks via
`./tools/explore.sh`. If, after genuine effort, ONE deep integral remains, isolate it as a precisely-named,
TRUE `private` lemma and report it (do not fabricate) — but aim for full closure.

# REQUIREMENTS
ZERO sorry (target). Keep the public theorem + the existing restructured statement intact; only fill the
crux + add `private` helpers. Touch ONLY this file. Do NOT touch `StatLean/Minimaxity.lean`, `lakefile`,
`lean-toolchain`, `lake-manifest.json`, `Defs.lean`, `Fano/`, `LeCam/`, other `Examples/`, `GaussianKLMulti`.

# TOUCH-SET: ONLY  StatLean/Minimaxity/Examples/QuadraticFunctional.lean
# BUILD: lake build StatLean.Minimaxity.Examples.QuadraticFunctional
# DONE = build exits 0 AND no sorry in the file.
  Commit: `mmx(#19): close quadratic_convex_hull_config via χ²/second-moment mixture bound (Wainwright Ex 15.11)`.
  Report: build status, sorry count, how the χ² bound was assembled, helpers, constant deviations; if a debt
  remains, its exact named statement.
