Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "..."` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`. Build with plain `lake build`, ITERATE to 0 errors / 0 sorries. Lift sub-steps to proven `private` helpers IN THIS FILE; NEVER fabricate. Build bottom-up, `lake build` often. Hardest example — methodical.

# CONTEXT + AUTHORIZED FAITHFUL RE-FRAMING (user decision)
File: `StatLean/Minimaxity/Examples/QuadraticFunctional.lean` (namespace `StatLean.Minimaxity`). Wainwright
Ex 15.11: estimate the quadratic functional `θ(f) = ∫₀¹ (f'(x))² dx` over a sign-vector density family; the
optimal **absolute-error** rate is `n^{-4/9}`. REWRITE the public theorem to the FAITHFUL form (the prior
`(·²)`/decoupled-θfunc stub was inconsistent — squared loss with the *real* functional gives `n^{-8/9}`, not
`n^{-4/9}`; the book's `n^{-4/9}` is for ABSOLUTE error):

```
theorem quadratic_functional_optimal_rate (n : ℕ) (hn : 1 ≤ n) :
    ∃ (ι : Type) (_ : MeasurableSpace ι) (f : ι → ℝ → ℝ) (θfunc : ι → ℝ)
      (Pn : Kernel ι (Fin n → ℝ)) (_ : IsMarkovKernel Pn),
      (∀ i, ∀ x ∈ Set.Icc (0:ℝ) 1, (1/2:ℝ) ≤ f i x) ∧
      (∀ i, θfunc i = ∫ x in Set.Icc (0:ℝ) 1, (deriv (f i) x)^2) ∧            -- REAL functional ∫(f')²
      (∀ i, Pn i = Measure.pi fun _ : Fin n =>
            (volume.restrict (Set.Icc (0:ℝ) 1)).withDensity fun x => ENNReal.ofReal (f i x)) ∧
      ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal (c * (n:ℝ)^(-(4:ℝ)/9)) ≤ minimaxRiskDist id θfunc Pn
```
Tags: `-- USER-INPUT: absolute-error loss (Φ=id) with the genuine functional θ(f)=∫(f')² and the book rate n^{-4/9} (Wainwright Ex 15.11); squared loss would give n^{-8/9}.`
Use `minimax_le_cam_convex_hull` (`LeCam/ConvexHull.lean`) with `Φ = id` (Monotone): it gives
`minimaxRiskDist id θfunc Pn ≥ id δ / 2 · (1 − tvDist(mixture₀, mixture₁))` with `2δ` the θfunc-separation.

# CONSTRUCTION (Ex 15.11) — `ι := (Fin m → Bool)`, `m^9 ≍ n²`
Fixed bump `φ : ℝ → ℝ`, smooth (so `f` twice-diff), supp `⊆ [0,1]`, `‖φ‖∞ ≤ 1/2`, `∫₀¹φ = 0`,
`b₀ := ∫₀¹φ² > 0`, `b₁ := ∫₀¹(φ')² > 0`. `φ_j(x) := (C/m²)·φ(m·x − j)` (supp `[j/m,(j+1)/m]`, disjoint),
`C` small so `f_α := 1 + Σ_{j<m} σ(α j)·φ_j ≥ 1/2` and twice-smooth. Real functional:
`θfunc(α) = ∫(f_α')² = Σ_j ∫(φ_j')² = m·(C²b₁/m³) = C²b₁/m²` (disjoint supp ⇒ cross terms 0; `∫(φ_j')² = C²b₁/m³`),
**constant over α**; `θfunc(U) = 0`. Two subfamilies `P₀ = {U}` (`a₀ ≡ U`), `P₁ = {f_α}` (`a₁ = id`, `π₁` uniform):
θfunc-separation `= C²b₁/m² =: 2δ ≍ n^{-4/9}` (with `m²≍n^{4/9}`).

# KEY BOUND — mixture `tvDist(U^n, Q) ≤ 1/2` via χ² / second moment (the genuine analytic core)
`Q = (uniform over α) ∘ Pⁿ_α`. Show `tvDist(U^n, Q) ≤ ½√(χ²(Q‖U^n))` (Cauchy–Schwarz on `½∫|dQ/dU^n − 1|`)
and `χ²(Q‖U^n)+1 = E_{α,α'}[∏_{i<n} ∫₀¹(1+Σⱼσ(αⱼ)φⱼ)(1+Σⱼσ(α'ⱼ)φⱼ)] = E_ε[(1+Σⱼ εⱼ bⱼ)^n]`, `bⱼ=∫φⱼ²=C²b₀/m⁵`,
`εⱼ=σ(αⱼ)σ(α'ⱼ)` i.i.d. `±1` (uses `∫φⱼ=0`, disjoint supports). Then
`E_ε[(1+Σεⱼbⱼ)^n] ≤ E_ε[exp(nΣεⱼbⱼ)] = ∏ⱼcosh(nbⱼ) ≤ exp((n²/2)Σbⱼ²) = exp((n²/2)C⁴b₀²/m⁹)`. With `m⁹=4b₀²n²`
and small `C`: `χ² ≤ 1/4 ⇒ tvDist ≤ 1/2`. (You may build a `private chiSqDiv` or bound the affinity directly;
`tvDist_eq_half_lintegral` gives the `½∫|·|` form; `Measure.pi` independence + `rnDeriv` give the product factorization.)
Then convex-hull (Φ=id): `risk ≥ δ/2·(1−TV) ≥ δ/4 ≍ n^{-4/9}`.

# REQUIREMENTS
ZERO sorry (target). Public name `quadratic_functional_optimal_rate` kept; statement = the faithful form above
(tagged). Helpers `private`, THIS file only. May add imports. Do NOT touch `StatLean/Minimaxity.lean`,
`lakefile`, `lean-toolchain`, `lake-manifest.json`, `Defs.lean`, `Fano/`, `LeCam/`, other `Examples/`,
`GaussianKLMulti`. If after genuine effort ONE deep integral resists, isolate it as a precisely-named TRUE
`private` lemma and report it — but aim for full closure.

# TOUCH-SET: ONLY  StatLean/Minimaxity/Examples/QuadraticFunctional.lean
# BUILD: lake build StatLean.Minimaxity.Examples.QuadraticFunctional
# DONE = build exits 0 AND no sorry in the file.
  Commit: `mmx(#19): quadratic_functional_optimal_rate — faithful ∫(f')², absolute loss, χ² mixture (Wainwright Ex 15.11)`.
  Report: build status, sorry count, the construction, how χ² was assembled, helpers, any residual debt's exact statement, deviations.
