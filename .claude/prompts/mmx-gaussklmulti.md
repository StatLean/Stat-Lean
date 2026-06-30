Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "natural-language query"` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries. Lift sub-steps to named `private` lemmas IN THIS FILE; never leave a `sorry`.

# GOAL — create ONE new file with the multivariate zero-mean Gaussian KL closed form.
Create `StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean` (namespace `StatLean.Minimaxity`,
`open MeasureTheory ProbabilityTheory InformationTheory Matrix`). Prove (0-sorry):

```
/-- KL divergence between two centered multivariate Gaussians (Wainwright Ex 15.13(b), μ=0):
`D(𝒩(0,A) ‖ 𝒩(0,B)) = ½ (log det B − log det A + tr(B⁻¹A) − d)`. -/
theorem klDiv_multivariateGaussian_zero {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) :
    klDiv (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) A)
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) B)
      = ENNReal.ofReal (2⁻¹ * (Real.log B.det - Real.log A.det + (B⁻¹ * A).trace - d))
```

# PROOF CHAIN (each link is standard; build the missing ones as `private` lemmas here)
1. **KL invariance under an invertible linear pushforward.** `klDiv (μ.map T) (ν.map T) = klDiv μ ν`
   for a `MeasurableEquiv` (or continuous linear equiv) `T`. The project already has the one-sided
   `klDiv_map_le` (`ForMathlib/KLDataProcessing.lean`, `klDiv (μ.map f)(ν.map f) ≤ klDiv μ ν`); get
   EQUALITY by applying it to `T` and to `T.symm` plus `Measure.map_map`/`Measure.map_id`. (Mathlib may
   also have `klDiv_map_measurableEquiv` — it is used inside `klDiv_pi_eq_nsmul`; check `KLDivergence.lean`
   and `./tools/explore.sh "Kullback Leibler divergence under measurable equivalence"`.)
2. **Whitening.** Let `C := B.posDef`’s inverse square root applied: reduce
   `D(𝒩(0,A)‖𝒩(0,B))` to `D(𝒩(0, Bⁱ ᐟ² A Bⁱ ᐟ²) ‖ 𝒩(0, I))` by pushing forward under the linear map
   `x ↦ B^{-1/2} x` (use `multivariateGaussian` pushforward under a linear map:
   `(multivariateGaussian 0 S).map (L) = multivariateGaussian 0 (M S Mᵀ)` where `M` is L’s matrix —
   search `./tools/explore.sh "pushforward of multivariate Gaussian under linear map"`; if absent,
   derive from the construction of `multivariateGaussian` as an affine image of `stdGaussian` /
   `map_pi_eq_stdGaussian`). `𝒩(0,I) = stdGaussian` (`multivariateGaussian_zero_one`).
3. **Diagonalize.** `C := B^{-1/2}AB^{-1/2}` is PosDef; spectral theorem
   (`Matrix.IsHermitian.spectral_theorem`) gives `C = U diag(Λ) Uᵀ`, `U` orthogonal. `stdGaussian` is
   orthogonally invariant (its charFun depends only on `‖x‖`; use `charFun`/`map_pi_eq_stdGaussian`), so
   pushing forward by `Uᵀ` keeps `𝒩(0,I)` fixed and turns `𝒩(0,C)` into `𝒩(0,diag Λ)`. Hence
   `D(𝒩(0,A)‖𝒩(0,B)) = D(𝒩(0,diag Λ) ‖ 𝒩(0,I))`.
4. **Tensorize to 1-D.** `𝒩(0, diag Λ)` is the product `Measure.pi (fun i => gaussianReal 0 (Λ i))`
   (push under `toLp`; `map_pi_eq_stdGaussian` is the `Λ=1` case — generalize, or use
   `measurePreserving_eval_multivariateGaussian` + independence of coordinates for diagonal covariance).
   Then KL tensorizes: `D = Σ_i D(gaussianReal 0 (Λ i) ‖ gaussianReal 0 1)` (project `klDiv_prod_eq_add`
   / `klDiv_pi_eq_nsmul`-style; for non-iid product you need the additive chain rule
   `klDiv_pi_eq_sum` — check `KLDivergence.lean`/Mathlib `klDiv_compProd`).
5. **1-D unequal-variance Gaussian KL** (NEW `private` lemma; the project’s `klDiv_gaussianReal` is
   equal-variance only): `klDiv (gaussianReal 0 a) (gaussianReal 0 1) = ENNReal.ofReal (½(a − 1 − log a))`
   for `a > 0`. Prove it the SAME way as `klDiv_gaussianReal` in `ForMathlib/GaussianKL.lean` (rnDeriv via
   `gaussianPDF`, `llr`, integrate; the integral of the quadratic against `gaussianReal 0 a` gives the `a`
   term and `∫ log` gives `−½log a`). Read that file and mirror its structure.
6. **Assemble.** `Σ_i ½(Λ i − 1 − log Λ i) = ½(tr C − d − log det C)` with `tr C = tr(B⁻¹A)` (cyclic) and
   `det C = det(B⁻¹A) = det A / det B`, giving `½(tr(B⁻¹A) − d − log det A + log det B)`. Use
   `Matrix.trace`, `Matrix.det_mul`, `Real.log_div`, spectral `tr = Σ eigval`, `det = ∏ eigval`.

Also export the **equal-covariance corollary** (used by Example 15.14, optional but helpful):
`klDiv_multivariateGaussian_zero_eq_cov : A=B=cov ⇒` trivially 0; and the MEAN-shift version
`klDiv (multivariateGaussian μ (c•1)) (multivariateGaussian ν (c•1)) = ofReal (‖μ-ν‖²/(2c))` if easy.

# REQUIREMENTS
ZERO sorry. NEW file only: `StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean`. Do NOT edit the umbrella
`StatLean/Minimaxity.lean` (the laptop registers it later), `lakefile`, `lean-toolchain`,
`lake-manifest.json`, or any existing file. Import what you need (`...ForMathlib.KLDataProcessing`,
`...ForMathlib.GaussianKL`, `...ForMathlib.KLDivergence`, `Mathlib.Probability.Distributions.Gaussian.Multivariate`,
`Mathlib.LinearAlgebra.Matrix.Spectrum`, `Mathlib.LinearAlgebra.Matrix.PosDef`).

# TOUCH-SET: ONLY (create)  StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean
# BUILD: lake build StatLean.Minimaxity.ForMathlib.GaussianKLMulti
# DONE = build exits 0 AND no sorry in the file.
  Commit: `mmx(B1): multivariate zero-mean Gaussian KL closed form (Wainwright Ex 15.13b)`.
  Report: build status, sorry count, the lemmas proved + their exact signatures (so callers can use them),
  any Mathlib bricks that were missing and how you bridged them.
