Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "..."` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`. Build with plain `lake build`, ITERATE to 0 errors / 0 sorries. `private` helpers IN THIS FILE; NEVER fabricate. Build bottom-up, `lake build` after each helper. This is THE hardest lemma — be patient and rigorous.

# GOAL — close the ONE remaining `sorry` in this file: `private lemma quadratic_signvector_construction`
File: `StatLean/Minimaxity/Examples/QuadraticFunctional.lean` (the public `quadratic_functional_optimal_rate`
and the convex-hull assembly are ALREADY PROVEN against this lemma; do NOT change them). Read the exact
`quadratic_signvector_construction` signature in the file and produce its existential witness. It needs:
`∃ ι f θfunc Pn …, (∀ i, ∀ x∈Icc 0 1, 1/2 ≤ f i x) ∧ (∀ i, θfunc i = ∫ x in Icc 0 1, (deriv (f i) x)^2) ∧
 (∀ i, Pn i = pi (volume.restrict (Icc 0 1)).withDensity (ofReal ∘ f i)) ∧ ∃ a₀ a₁ π₀ π₁ … c₀>0,
 (∀ i₀ i₁, 2·ofReal(c₀·n^{-2/9}) ≤ edist (θfunc(a₀ i₀)) (θfunc(a₁ i₁))) ∧ tvDist(Pn∘a₀∘π₀)(Pn∘a₁∘π₁) ≤ 1/2`.

# CONCRETE CHOICES (avoid abstract existence — pin everything)
* Bump `φ : ℝ → ℝ := fun x => if x ∈ Set.Ico 0 1 then (1/2)*Real.sin (2*π*x) else 0`. On `[0,1]`:
  `∫₀¹ φ = 0` (∫sin(2πx)=0), `b₀ := ∫₀¹ φ² = 1/8` (∫sin²=1/2), `b₁ := ∫₀¹ (φ')² = π²/2` (∫cos²=1/2),
  `|φ| ≤ 1/2`. Prove these with `intervalIntegral`/`integral_sin_sq`-style lemmas (search
  `./tools/explore.sh "integral of sin squared over period"`, `"intervalIntegral sin"`). `deriv φ` on
  `(0,1)` is `π·cos(2πx)`; at kink points `deriv` is `0` (measure-zero, irrelevant to ∫).
* `m := (⌈(4*b₀^2)^(1/9)⌉₊) * (⌈(n:ℝ)^(1/9)⌉₊)` or simply pick `m` with `m^9 ≥ 4 b₀² n²` and `m ≥ 1`
  (a `Nat` with that property; `Nat.exists_pow_ge`-style). `C := 1` (or a small fixed const so `f_α ≥ 1/2`).
  `φ_j x := (C/m^2) * φ (m*x - j)` (support `[j/m,(j+1)/m]`, disjoint). `∫φ_j = 0`, `∫φ_j² = C²b₀/m⁵`,
  `∫(φ_j')² = C²b₁/m³` (change of variables `u = m x − j`).
* `ι := (Fin m → Bool)`; `σ : Bool → ℝ := fun b => if b then 1 else -1`; `f_α := fun x => 1 + ∑ j, σ(α j)*φ_j x`;
  also include the uniform index. `f_α ≥ 1/2` since `|∑ⱼσ(αⱼ)φⱼ| ≤ max|φ_j| ≤ C/(2m²) ≤ 1/2`.
* Functional `θfunc α = ∫_{Icc 0 1}(deriv f_α)² = ∑ⱼ ∫(φ_j')² = m·C²b₁/m³ = C²b₁/m²` (disjoint supports ⇒
  cross terms 0; `deriv f_α = ∑ⱼ σ(αⱼ)φⱼ'`). `θfunc(U)=0`. Separation `2δ = C²b₁/m²`; check `C²b₁/m² ≥ 2c₀n^{-2/9}`
  for a small `c₀` (since `m² ≍ n^{2/9}`... NOTE: with `m⁹≍n²`, `m²≍n^{4/9}` ⇒ `C²b₁/m² ≍ n^{-4/9}`; if the
  signature's exponent `n^{-2/9}` then `2δ` must be `≍ n^{-4/9} ≤ n^{-2/9}`, so pick `c₀` so `2c₀n^{-2/9} ≤ C²b₁/m²`
  — this HOLDS for large n since `n^{-4/9} … ` wait: `n^{-4/9} < n^{-2/9}`, so you need `2c₀ n^{-2/9} ≤ C²b₁/m² ≍ n^{-4/9}`,
  i.e. `c₀ ≤ (C²b₁/2)·n^{-2/9}` — `c₀` may depend on `n` per the `∃ c₀`; just set `c₀ := C²b₁/(4 m² n^{-2/9})`>0).

# THE χ² MIXTURE BOUND (the core; `a₀≡U`, `a₁=id`, `π₁` uniform over `ι`, `π₀=dirac U`)
Goal `tvDist (Pn∘a₁∘π₁) (Pn∘a₀∘π₀) ≤ 1/2`, i.e. `tvDist Q U^n ≤ 1/2` with `Q = π₁`-mixture of `Pₐ^n`.
1. `tvDist Q U^n ≤ ½·√(χ²)` where `χ² := ∫ (dQ/dU^n − 1)² dU^n = (∫ (dQ/dU^n)² dU^n) − 1`
   (from `tvDist_eq_half_lintegral` + Cauchy–Schwarz `∫|h| ≤ √(∫h²)`, `h = dQ/dU^n − 1`, `∫h dU^n = 0`).
2. `∫ (dQ/dU^n)² dU^n = 𝔼_{α,α'}[ ∏_{i<n} ∫₀¹ (1+∑ⱼσ(αⱼ)φⱼ)(1+∑ⱼσ(α'ⱼ)φⱼ) dx ]` (mixture density
   `dQ/dU^n = 𝔼_α ∏ᵢ(1+∑ⱼσ(αⱼ)φⱼ(xᵢ))`; square, swap `∫`/`𝔼` (finite sum over `ι`), Fubini over `Measure.pi`).
3. inner `= 1 + ∑ⱼ σ(αⱼ)σ(α'ⱼ) bⱼ` (`∫φⱼ=0`, disjoint ⇒ `∫φⱼφₖ=0`, `∫φⱼ²=bⱼ=C²b₀/m⁵`). So
   `χ²+1 = 𝔼_{α,α'}[(1+∑ⱼ σ(αⱼ)σ(α'ⱼ)bⱼ)^n]`. With `εⱼ := σ(αⱼ)σ(α'ⱼ)` i.i.d. uniform `±1`:
   `= 𝔼_ε[(1+∑ⱼ εⱼ bⱼ)^n]`.
4. `(1+t) ≤ exp t`, so `≤ 𝔼_ε[exp(n∑ⱼεⱼbⱼ)] = ∏ⱼ 𝔼[exp(n εⱼ bⱼ)] = ∏ⱼ cosh(n bⱼ) ≤ ∏ⱼ exp((n bⱼ)²/2)
   = exp((n²/2)∑ⱼ bⱼ²)`. `∑ⱼbⱼ² = m·(C²b₀/m⁵)² = C⁴b₀²/m⁹ ≤ C⁴b₀²/(4b₀²n²) = C⁴/(4n²)`, so
   `χ²+1 ≤ exp(C⁴/8)`. With `C` small (e.g. `C⁴ ≤ 8·log(5/4)`), `χ² ≤ 1/4`, so `tvDist ≤ ½·√(1/4) = 1/4 ≤ 1/2`. ∎
Build small `private` lemmas: `cosh_le_exp_half_sq` (`Real.cosh t ≤ exp (t²/2)`), the per-coordinate integral
identity, the `𝔼_ε` factorization (`Fintype.sum_prod`/`Finset.prod_univ` over `Fin m → Bool`). The mixture
`dQ/dU^n` / rnDeriv-against-`U^n` step is the fiddliest — use `Measure.pi` + `withDensity` rnDeriv lemmas.

# FALLBACK
If a sub-step genuinely resists after real effort, isolate it as ONE precisely-named TRUE `private` lemma,
commit what compiles, report its exact statement. Aim for full closure.

# REQUIREMENTS / TOUCH-SET / BUILD
ZERO sorry (target). Touch ONLY `StatLean/Minimaxity/Examples/QuadraticFunctional.lean`. Do NOT change the
public theorem or the convex-hull assembly. No edits to umbrella/lakefile/toolchain/manifest/Defs/Fano/LeCam.
BUILD: `lake build StatLean.Minimaxity.Examples.QuadraticFunctional`. DONE = exit 0, no sorry.
Commit: `mmx(#19): close quadratic_signvector_construction — sine bump + χ² mixture (Wainwright Ex 15.11)`.
Report: build status, sorry count, helpers, any residual debt's exact statement, deviations.
