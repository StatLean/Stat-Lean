Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "..."` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries in the target file. Lift sub-steps to `private` helpers IN THIS FILE; never `sorry`.

# CONTEXT
File: `StatLean/Minimaxity/ForMathlib/GaussianMaxEntropy.lean` (namespace `StatLean.Minimaxity`,
`open MeasureTheory ProbabilityTheory InformationTheory Matrix`). One `sorry`, the crux
`sum_klDiv_le_logdet`, delegated to by the public `gaussian_mutualInfo_le` (Wainwright Lemma 15.17):
```
private lemma sum_klDiv_le_logdet {M d : ℕ} [NeZero M]
    (Q : Kernel (Fin M) (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel Q]
    (S : Fin M → Matrix (Fin d) (Fin d) ℝ) (covZ : Matrix (Fin d) (Fin d) ℝ)
    (hQ : ∀ j, Q j = multivariateGaussian 0 (S j))
    (hcov : covZ = (M : ℝ)⁻¹ • ∑ j, S j) :
    (M : ℝ≥0∞)⁻¹ * ∑ j, klDiv (Q j) (mixture Q)
      ≤ ENNReal.ofReal (2⁻¹ * (Real.log covZ.det - (M : ℝ)⁻¹ * ∑ j, Real.log (S j).det))
```

# AUTHORIZED EDGE HYPOTHESIS
Add `(hS : ∀ j, (S j).PosDef)` to BOTH `sum_klDiv_le_logdet` AND `gaussian_mutualInfo_le`, tagged
`-- USER-INPUT: each component covariance Σʲ is positive-definite (Wainwright Lemma 15.17 — Σʲ = cov(Z|J=j)).`
Then `covZ = M⁻¹ Σⱼ Σʲ` is PosDef (average of PosDef; `M ≥ 1`). Each `Q j = multivariateGaussian 0 (S j)`
is then a genuine (PosDef) Gaussian, and `G := multivariateGaussian 0 covZ` is a probability measure.

# REUSE — the key reduction (NO differential entropy needed)
* `klDiv_multivariateGaussian_zero (A B) (hA : A.PosDef) (hB : B.PosDef) :`
  `klDiv (multivariateGaussian 0 A) (multivariateGaussian 0 B) = ENNReal.ofReal (½ (log det B − log det A + tr(B⁻¹A) − d))`
  — in `StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean` (just merged). `import` it. (Check its EXACT
  name/signature with `./tools/api.sh StatLean/Minimaxity/ForMathlib/GaussianKLMulti.lean`.)
* `sum_klDiv_mixture_le (P : Fin M → Measure α) (Q : Measure α) [∀ j, IsProbabilityMeasure (P j)] [IsProbabilityMeasure Q] :`
  `∑ j, klDiv (P j) ((M:ℝ≥0∞)⁻¹ • ∑ k, P k) ≤ ∑ j, klDiv (P j) Q` — `ForMathlib/KLDivergence.lean` (CLOSED).
* `mixture_eq_inv_smul_sum (Q) : mixture Q = (M:ℝ≥0∞)⁻¹ • ∑ k, Q k` — `Fano/MutualInformation.lean`.

# PROOF
1. Rewrite `mixture Q = M⁻¹ • ∑ k, Q k` (`mixture_eq_inv_smul_sum`).
2. Apply `sum_klDiv_mixture_le` with `P := Q` (each `Q j` a probability measure via `hQ`+`hS`) and the
   comparison `G := multivariateGaussian 0 covZ` (probability measure, PosDef covZ):
   `∑ j, klDiv (Q j) (mixture Q) ≤ ∑ j, klDiv (Q j) G`.
3. Each `klDiv (Q j) G = klDiv (multivariateGaussian 0 (S j)) (multivariateGaussian 0 covZ)
   = ofReal (½ (log det covZ − log det (S j) + tr(covZ⁻¹ (S j)) − d))` by `klDiv_multivariateGaussian_zero`
   (with `hS j`, covZ PosDef).
4. Average: `M⁻¹ ∑ j (that) = ofReal (½ (log det covZ − M⁻¹ ∑ log det (S j) + M⁻¹ ∑ tr(covZ⁻¹ (S j)) − d))`.
   **Trace identity**: `M⁻¹ ∑ j tr(covZ⁻¹ (S j)) = tr(covZ⁻¹ (M⁻¹ ∑ j S j)) = tr(covZ⁻¹ covZ) = tr(1) = d`
   (linearity of trace + `Matrix.mul_inv_cancel`/`covZ.PosDef.isUnit` ; `hcov`). So the `+d` and `−d`
   cancel, leaving `ofReal (½ (log det covZ − M⁻¹ ∑ log det (S j)))` — the goal. Mind the `ENNReal.ofReal`
   sum/`M⁻¹•` push-through and that the inner reals can be negative (use `ENNReal.ofReal` lemmas carefully;
   the OVERALL bound is what's stated — you have `≤`, so monotonicity of `ofReal` + the `sum_klDiv_mixture_le`
   `≤` suffices; you do NOT need the components individually nonneg).

# REQUIREMENTS
ZERO sorry. Public theorem name/conclusion unchanged (only `hS` added, tagged). Helpers `private`, THIS file
only. Add the `import StatLean.Minimaxity.ForMathlib.GaussianKLMulti` (and matrix imports as needed). Do NOT
touch `StatLean/Minimaxity.lean`, `lakefile`, `lean-toolchain`, `lake-manifest.json`, `Defs.lean`, others.

# TOUCH-SET: ONLY  StatLean/Minimaxity/ForMathlib/GaussianMaxEntropy.lean
# BUILD: lake build StatLean.Minimaxity.ForMathlib.GaussianMaxEntropy
# DONE = build exits 0 AND no sorry in the file.
  Commit: `mmx(#24): close sum_klDiv_le_logdet via matched-Gaussian KL (Wainwright Lemma 15.17; +Σʲ PosDef)`.
  Report: build status, sorry count, the added hS, helpers, how the trace identity was discharged.
