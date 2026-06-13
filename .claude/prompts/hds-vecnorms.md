Read CLAUDE.md (repo root) first and obey it — §2 (hypothesis-discipline tags), §6 (search tools),
§7 (Lean gotchas), §9, §10. Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`,
`./tools/check.sh '<fully.qualified.name>'`. Never `lake update`.

# TASK
Create `StatLean/HighDimensionalStatistics/ForMathlib/VecNorms.lean`
(namespace `StatLean.HighDimensionalStatistics`) — the ℓ¹ / ℓ∞ vector-norm bricks that the Lasso
rate proofs (Lu *Big Data Analysis* ch.8) consume. This is a pure-math `ForMathlib`-layer file:
Mathlib only, no statistics. Vectors live in `EuclideanSpace ℝ (Fin d)` (ℓ² + inner product is the
ambient norm); define ℓ¹ and ℓ∞ as **explicit functions**, do NOT stack `PiLp`/`WithLp` instances
on the same carrier type (it creates instance-diamond pain — this is a deliberate design choice).

Provide:

1. `def l1Norm (x : EuclideanSpace ℝ (Fin d)) : ℝ := ∑ i, |x i|`  -- docstring: formalizes ‖x‖₁.
2. `def linfNorm (x : EuclideanSpace ℝ (Fin d)) : ℝ := ⨆ i, |x i|` (or `Finset.univ.sup' …` /
   `Finset.sup` over `|x i|` — pick the form that is easiest to prove the Hölder bound with; a
   `Finset`-max over a nonempty finite index is cleaner than `iSup` here). Docstring: formalizes ‖x‖∞.
3. **Hölder / dual-pairing** (`thm`): `|⟪x, y⟫_ℝ| ≤ l1Norm x * linfNorm y`. (Inner product is the
   real `EuclideanSpace` inner; see CLAUDE.md §7.2 for the `⟪·,·⟫_ℝ` reduction order.) Equivalent
   useful form: `|∑ i, x i * y i| ≤ (∑ i, |x i|) * (⨆ i, |y i|)`.
4. **Support-restriction operator**: for `S : Finset (Fin d)`, `def restrict (S) (x) :
   EuclideanSpace ℝ (Fin d)` zeroing coordinates outside `S` (use `Set.indicator`/`if i ∈ S`).
5. **√s ℓ¹–ℓ² bound on the support** (`thm`): `l1Norm (restrict S x) ≤ Real.sqrt (S.card) * ‖x‖`
   where `‖x‖` is the ambient ℓ² norm. (Cauchy–Schwarz: `∑_{i∈S}|x i| ≤ √|S| · √(∑_{i∈S} x i²)
   ≤ √|S| · ‖x‖`. Mathlib: `Finset.inner_mul_le_norm_mul_norm` / `Finset.sum_div_pow_mul_fract…`
   — more directly `Finset.sum_le_card_nsmul`? No: use `Finset.inner_mul_le_norm_mul_norm` or the
   `Finset.sum_mul_sq_le_sq_mul_sq` Cauchy–Schwarz, applied with the all-ones vector on S.)

Prove **everything** — zero `sorry`. These are standard finite-sum inequalities; expect Cauchy–
Schwarz (`Finset.inner_mul_le_norm_mul_norm` or `Finset.sum_mul_sq_le_sq_mul_sq`), `Finset.abs_sum_le_sum_abs`,
`Finset.sum_le_sum`, and `Finset.le_sup`/`Finset.single_le_sum`. Tag any hypothesis you add with
`-- LEAN-ONLY: …`; there are no book USER-INPUT hypotheses here (pure math). Each `def` gets a
docstring naming the ‖·‖ it formalizes.

# TOUCH-SET
Create/modify ONLY `StatLean/HighDimensionalStatistics/ForMathlib/VecNorms.lean`. Do NOT touch any
umbrella (`StatLean/HighDimensionalStatistics.lean` does not exist yet — do NOT create it),
`StatLean.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `notes/`.

# BUILD (inside the worktree)
  lake build StatLean.HighDimensionalStatistics.ForMathlib.VecNorms

# DONE = build exits 0; ZERO sorries; docstrings on defs; small commits
(`hds(formathlib): ℓ¹/ℓ∞ norms, Hölder, √s support bound (Lu-BDA ch8)`). Finish by printing the
declaration names, build status, and the exact Mathlib Cauchy–Schwarz lemma you used. Independently
re-verified; a weakened statement (e.g. a vacuous `linfNorm` or a √s bound with the wrong constant)
will be rejected.
