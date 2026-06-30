Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "..."` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries. Never `sorry`.

# GOAL — add ONE public corollary to an existing file (for the linear-regression example #22).
File: `StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean` (already has the closed
`klDiv_multivariateGaussian_zero` plus several `private` helpers — `multivariateGaussian_diagonal_eq_pi`,
`klDiv_pi_eq_sum`, `klDiv_map_measurableEquiv_eq`, `klDiv_gaussianReal_zero`, `map_multivariateGaussian_clm`,
etc.; `./tools/api.sh` / read the file to see them). Add a PUBLIC lemma giving the KL between two
EQUAL-covariance (scalar `c·I`) multivariate Gaussians differing only in MEAN:

```
/-- KL between two `c·I`-covariance Gaussians differing in mean: `D(𝒩(μ,cI) ‖ 𝒩(ν,cI)) = ‖μ-ν‖²/(2c)`. -/
theorem klDiv_multivariateGaussian_smul_one {d : ℕ} (μ ν : EuclideanSpace ℝ (Fin d)) (c : ℝ≥0) (hc : c ≠ 0) :
    klDiv (multivariateGaussian μ (c • (1 : Matrix (Fin d) (Fin d) ℝ)))
          (multivariateGaussian ν (c • (1 : Matrix (Fin d) (Fin d) ℝ)))
      = ENNReal.ofReal (‖μ - ν‖ ^ 2 / (2 * (c : ℝ)))
```

# PROOF (reuse the file's machinery; promote any `private` helper you need to non-private)
* `c • 1 = Matrix.diagonal (fun _ => (c:ℝ))`; the diagonal bridge in this file
  (`multivariateGaussian_diagonal_eq_pi`, currently mean-0) gives the product structure. Generalize it to
  arbitrary mean — `multivariateGaussian m (diagonal Λ) = (Measure.pi fun i => gaussianReal (m i) (Λ i).toNNReal).map (toLp 2)`
  — OR reduce to mean-0 by translation: `multivariateGaussian m S = (multivariateGaussian 0 S).map (· + m)`
  (search `./tools/explore.sh "multivariate gaussian map add translation"`; or derive from the construction).
* Then KL invariance under `toLp` (`klDiv_map_measurableEquiv_eq`) + non-iid tensorization
  (`klDiv_pi_eq_sum`) + the EQUAL-variance 1-D KL `klDiv_gaussianReal` (project, `ForMathlib/GaussianKL.lean`,
  `klDiv (gaussianReal m₁ v)(gaussianReal m₂ v) = ofReal((m₁-m₂)²/(2v))`) give
  `Σ_i (μ_i-ν_i)²/(2c) = ‖μ-ν‖²/(2c)` (`EuclideanSpace.norm_eq` / `Finset.sum`).
Make public whichever helpers you reuse (delete their `private`) — the regression example imports them.

# REQUIREMENTS
ZERO sorry. Keep `klDiv_multivariateGaussian_zero` and all existing content intact (only ADD the corollary
and de-`private` reused helpers). Touch ONLY this file. Do NOT touch `StatLean/Minimaxity.lean`, `lakefile`,
`lean-toolchain`, `lake-manifest.json`, `Defs.lean`, others.

# TOUCH-SET: ONLY  StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean
# BUILD: lake build StatLean.Minimaxity.ForMathlib.GaussianKLMulti
# DONE = build exits 0 AND no sorry in the file.
  Commit: `mmx(B1b): public mean-shift equal-covariance Gaussian KL corollary (for Ex 15.14)`.
  Report: build status, sorry count, the corollary's exact final signature, which helpers were made public.
