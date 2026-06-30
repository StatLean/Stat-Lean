Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use the search tools (./tools/loogle.sh, check.sh, where.sh, api.sh). Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors and the target sorry is gone.

# CONTEXT
File: `StatLean/Minimaxity/Examples/GaussianLocation.lean` (namespace `StatLean.Minimaxity`;
`open MeasureTheory ProbabilityTheory`; `open scoped ENNReal NNReal`).
The PUBLIC theorem `gaussian_location_minimax_rate` is ALREADY PROVED; it delegates to ONE `private`
crux that is the only `sorry` (around line 34):

```
private lemma gaussian_two_point_tvDist_le (n : ℕ) (hn : 1 ≤ n) (v : ℝ≥0) (hv : v ≠ 0)
    (P : Kernel ℝ (Fin n → ℝ)) [IsMarkovKernel P]
    (hP : ∀ θ : ℝ, P θ = Measure.pi fun _ : Fin n => gaussianReal θ v) :
    tvDist (P 0) (P (Real.sqrt ((v : ℝ) / n))) ≤ 2⁻¹
```

CLOSED bricks already in the project (read the files for the EXACT statements before using):
* `pinsker_tv_le_kl (μ ν) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :`
  `tvDist μ ν ≤ (2⁻¹ * klDiv ν μ) ^ (1/2 : ℝ)` — `StatLean/Minimaxity/ForMathlib/PinskerInequality.lean`.
  ⚠ NOTE THE REVERSED ARGUMENT ORDER: the RHS is `klDiv ν μ`, not `klDiv μ ν`.
* `klDiv_pi_eq_nsmul (n : ℕ) (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :`
  `klDiv (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν) = n • klDiv μ ν`
  — `StatLean/Minimaxity/ForMathlib/KLDivergence.lean`.
* `klDiv_gaussianReal (m₁ m₂ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :`
  `klDiv (gaussianReal m₁ v) (gaussianReal m₂ v) = ENNReal.ofReal ((m₁ - m₂) ^ 2 / (2 * (v : ℝ)))`
  — `StatLean/Minimaxity/ForMathlib/GaussianKL.lean`.
`gaussianReal θ v` is a probability measure (instance available); `Measure.pi` of probability measures
is a probability measure.

# TASK — close `gaussian_two_point_tvDist_le` to 0 sorry.
Let `θ₁ := Real.sqrt ((v:ℝ)/n)`. Rewrite `P 0` and `P θ₁` via `hP`.
1. `pinsker_tv_le_kl (P 0) (P θ₁)` gives `tvDist (P 0) (P θ₁) ≤ (2⁻¹ * klDiv (P θ₁) (P 0)) ^ (1/2)`
   (reversed order ⇒ the KL is `klDiv (P θ₁) (P 0)`).
2. `klDiv (P θ₁) (P 0) = klDiv (pi (gaussianReal θ₁ v)) (pi (gaussianReal 0 v)) = n • klDiv (gaussianReal θ₁ v) (gaussianReal 0 v)`
   via `klDiv_pi_eq_nsmul`.
3. `klDiv (gaussianReal θ₁ v) (gaussianReal 0 v) = ENNReal.ofReal (θ₁^2/(2v))` via `klDiv_gaussianReal`.
   `θ₁^2 = v/n` by `Real.sq_sqrt` (needs `0 ≤ v/n`), so this `= ENNReal.ofReal ((v/n)/(2v)) = ENNReal.ofReal (1/(2n))`
   (simplify with `field_simp`/`ring`; `v ≠ 0`, `n ≠ 0`).
4. `n • ENNReal.ofReal (1/(2n)) = ENNReal.ofReal (n * (1/(2n))) = ENNReal.ofReal (1/2)`
   (`nsmul_eq_mul`, `ENNReal.ofReal` push-through; `n ≥ 1`).
5. Hence `klDiv (P θ₁) (P 0) = ENNReal.ofReal (1/2)`, `2⁻¹ * ENNReal.ofReal (1/2) = ENNReal.ofReal (1/4)`,
   and `(ENNReal.ofReal (1/4)) ^ (1/2 : ℝ) = ENNReal.ofReal ((1/4) ^ (1/2:ℝ)) = ENNReal.ofReal (1/2) = 2⁻¹`.
   Use the ENNReal rpow-of-ofReal lemma (search: `loogle.sh '"ofReal_rpow"'`, `'"rpow"'`); `(1/4)^(1/2:ℝ)=1/2`
   via `Real.rpow_natCast`/`Real.sqrt` or `show (1/4:ℝ)^((1:ℝ)/2) = 1/2 by rw [...]; norm_num`. Conclude `≤ 2⁻¹`.

If a step is fiddly, lift it to a `private` helper lemma IN THIS FILE. Prefer `simp`/`norm_num`/`field_simp`
and the search tools over guessing lemma names.

# REQUIREMENTS
ZERO sorry in the file. Keep ALL theorem/lemma names, signatures, `-- USER-INPUT` and docstring tags
UNCHANGED. Helper lemmas (if any) go in THIS file only, `private`. Do NOT edit any other file. Do NOT
touch `StatLean/Minimaxity.lean`, `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, or any `Defs.lean`.

# TOUCH-SET: ONLY  StatLean/Minimaxity/Examples/GaussianLocation.lean
# BUILD: lake build StatLean.Minimaxity.Examples.GaussianLocation
# DONE = build exits 0 AND `grep -n sorry StatLean/Minimaxity/Examples/GaussianLocation.lean` is empty.
  Commit: `mmx(#20): close gaussian_two_point_tvDist_le (Gaussian location, Wainwright Ex 15.4)`.
  Report: build status, final sorry count, any helper lemmas added.
