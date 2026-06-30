Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "natural-language query"` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors and 0 sorries in the target file. Lift hard steps to `private` helpers IN THIS FILE (never `sorry`).

# CONTEXT
File: `StatLean/Minimaxity/Examples/UniformLocation.lean` (namespace `StatLean.Minimaxity`).
One `sorry`, in the crux `uniform_two_point_tvDist_bound` (Wainwright Ex 15.5, uniform location, rate n^{-2}):
```
private lemma uniform_two_point_tvDist_bound (n : ℕ) (hn : 1 ≤ n)
    (P : Kernel ℝ (Fin n → ℝ)) [IsMarkovKernel P]
    (hP : ∀ θ : ℝ, P θ = Measure.pi fun _ : Fin n => volume.restrict (Set.Icc θ (θ + 1))) :
    ENNReal.ofReal ((1 - 1 / Real.sqrt 2) / 16) ≤ 1 - tvDist (P 0) (P ((n : ℝ)⁻¹))
```

# STATEMENT REPAIR (REQUIRED — false at n=1)
Change `hn : 1 ≤ n` to `hn : 2 ≤ n` in BOTH `uniform_two_point_tvDist_bound` AND the public
`uniform_location_minimax_rate`, tagged
`-- LEAN-ONLY: n ≥ 2 (at n=1 the shifted unit-uniforms [0,1],[1,2] are a.e. disjoint ⇒ TV=1, so the two-point bound is vacuous); Wainwright Ex 15.5 is an n→∞ rate.`
The public theorem keeps delegating to the crux (pass `hn`). Keep conclusions/constants unchanged.

# MATH (exact n-fold Hellinger, then Le Cam) — the lossy `sqHellinger_pi_le_nsmul` is INSUFFICIENT here
1. **Single-sample squared Hellinger** of the unit-interval shift by `θ₁ = 1/n ∈ (0,1]`:
   `sqHellinger (volume.restrict (Icc 0 1)) (volume.restrict (Icc θ₁ (θ₁+1))) = ENNReal.ofReal (2*θ₁) = ofReal (2/n)`.
   (Densities are indicators; on the symmetric difference `[0,θ₁] ∪ [1,1+θ₁]` (Lebesgue measure `2θ₁`)
   the integrand `(√1-√0)² = 1`; on the overlap it is `0`. Compute via the project's `sqHellinger`
   def — rnDeriv against the sum measure; reduce to a Lebesgue integral over the two intervals.)
2. **Exact n-fold** via the affinity product. For probability measures `sqHellinger μ ν = 2(1 - ρ)`
   with affinity `ρ = ∫ √(dμ/dλ · dν/dλ) dλ`; and the n-fold affinity is `ρ^n`
   (use `StatLean/AsymptoticStatistics/ForMathlib/HellingerProduct.lean`:
   `integral_prod_sqrt_mul_prod_sqrt_eq_pow` / `lintegral_prod_iid_eq_pow` — `api.sh` that file for exact
   names/signatures). So `sqHellinger (P 0) (P θ₁) = 2(1 - ρ₁^n)` with `ρ₁ = 1 - (1/n)`.
   For `n ≥ 2`, `ρ₁^n = (1-1/n)^n ≥ 1/4` (prove: increasing in n, `=1/4` at n=2), hence
   `sqHellinger (P 0) (P θ₁) ≤ 3/2`.
3. **Le Cam**: `lecam_tv_le_hellinger (P 0) (P θ₁)` gives
   `tvDist (P 0)(P θ₁) ≤ (sqH)^(1/2) * (1 - sqH/4)^(1/2)`. The RHS `f(s) = √s·√(1-s/4)` is increasing on
   `[0,2]`, so with `sqH ≤ 3/2`: `tvDist ≤ f(3/2) = √15/4`. Therefore
   `1 - tvDist ≥ 1 - √15/4 = (4-√15)/4 ≥ (1 - 1/√2)/16` (verify the last numeric `≥` with `nlinarith`
   / interval bounds on `√15`, `√2`). Conclude.

If the exact n-fold affinity is hard to assemble, an acceptable alternative: derive
`sqHellinger (P 0)(P θ₁) ≤ 3/2` for `n ≥ 2` by ANY correct route and feed it to `lecam_tv_le_hellinger`.
Prefer exactness; never `sorry`.

# REQUIREMENTS
ZERO sorry. Names unchanged (only `hn : 2 ≤ n` swapped in, tagged). Helpers `private`, in THIS file. May add
imports (e.g. the HellingerProduct module, `Mathlib.Analysis.SpecialFunctions.Pow.NNRpow`). Do NOT touch
`StatLean/Minimaxity.lean`, `lakefile`, `lean-toolchain`, `lake-manifest.json`, `Defs.lean`, `Fano/`, `LeCam/`.

# TOUCH-SET: ONLY  StatLean/Minimaxity/Examples/UniformLocation.lean
# BUILD: lake build StatLean.Minimaxity.Examples.UniformLocation
# DONE = build exits 0 AND no sorry in the file.
  Commit: `mmx(#21): close uniform_two_point_tvDist_bound, exact n-fold Hellinger (Wainwright Ex 15.5; +n≥2)`.
  Report: build status, sorry count, the n≥2 change, helpers added, any constant deviation.
