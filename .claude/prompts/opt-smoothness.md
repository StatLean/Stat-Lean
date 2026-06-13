Read CLAUDE.md (repo root) first and obey it — especially §2 (hypothesis-discipline tags),
§6 (search tools), §7 (Lean gotchas — esp. §7.2 on real inner product `⟪·,·⟫_ℝ` ordering),
§9, §10. Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`, `./tools/check.sh '<name>'`.

# CONTEXT
The `StatLean/Optimization/` area is scaffolded. Ambient: real inner product space
`{E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`, notation `⟪·,·⟫_ℝ`
(`open scoped InnerProductSpace`), Riesz gradient `gradient`/`∇` (`open scoped Gradient`).
Concept def already exists and is CORRECT — do not change it:
- `IsLSmooth (f : E → ℝ) (L : ℝ) : Prop := ∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + (L/2)*‖x - y‖^2`
  (Smoothness/Defs) — the quadratic upper bound IS the definition (Lu-BDA Def 11.1).
The lemma `inner_gradient_le_sub_of_convexOn` (convex+differentiable gradient inequality:
`f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y`) is being proved on a sibling branch; you may USE it
(it is in `StatLean.Optimization.ForMathlib.FirstOrderConvex`). If it still has a `sorry` when
you build, that is fine — your files build on top; do not edit it.

# TASK — close these `sorry`s (2 files), proofs only, do NOT change any signature:

## 1. `StatLean/Optimization/ForMathlib/GradientCalc.lean`
`gradient_eq_zero_of_forall_le {f : E → ℝ} (hdiff : Differentiable ℝ f) {x : E}
  (hmin : ∀ y, f x ≤ f y) : gradient f x = 0`
Strategy: a global min is a local min, then Fermat. `IsLocalMin f x` from `hmin`
(`isLocalMin_of_..` or build from `Filter.eventually_of_forall`/`IsMinOn.isLocalMin`;
search `./tools/loogle.sh '"IsLocalMin"'`). Then Fermat: `IsLocalMin.fderiv_eq_zero`
(in `Mathlib/Analysis/Calculus/LocalExtr/Basic.lean`) gives `fderiv ℝ f x = 0` (needs
`(hdiff x).differentiableAt`). Convert `fderiv = 0` to `gradient = 0`: `gradient f x`
is `(toDual ℝ E).symm (fderiv ℝ f x)` — use `hasGradientAt_iff_hasFDerivAt` /
`HasGradientAt.gradient`, or find `gradient_eq_zero`/`gradient_eq` lemmas; `map_zero` of the
linear iso closes it. Add `import Mathlib.Analysis.Calculus.LocalExtr.Basic` and
`import Mathlib.Topology.Order.LocalExtr` if needed (these are proof-only; keep
`Gradient.Basic` too).

## 2. `StatLean/Optimization/Smoothness/CoCoercive.lean`
### (a) `cocoercive {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
  {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (x y : E) :
  f x - f y ≤ ⟪gradient f x, x - y⟫_ℝ - (1/(2*L)) * ‖gradient f x - gradient f y‖^2`
This is Lu-BDA Lemma 11.1. Proof (book): set `z := y - (1/L) • (gradient f y - gradient f x)`.
Then:
  * convexity at `x` (use `inner_gradient_le_sub_of_convexOn hf hdiff x z`):
      `f x - f z ≤ ⟪gradient f x, x - z⟫_ℝ`   (i.e. `f z ≥ f x + ⟪∇f x, z-x⟫`, rearrange);
  * `L`-smoothness at `y` (use `hsmooth y z`):
      `f z - f y ≤ ⟪gradient f y, z - y⟫_ℝ + (L/2)*‖y - z‖^2`.
  Add them: `f x - f y ≤ ⟪∇f x, x-z⟫ + ⟪∇f y, z-y⟫ + (L/2)‖y-z‖²`.
  Now substitute `z`. Let `g := gradient f x - gradient f y`. Then `z - y = -(1/L)•(-g) = (1/L)•g`
  is `(1/L)•(∇f x − ∇f y)`; `x - z = (x - y) + (1/L)•(∇f y − ∇f x) = (x-y) - (1/L)•g`.
  Expand the inner products with `real_inner_smul_right`/`real_inner_smul_left`,
  `inner_sub_left`/`inner_sub_right`, `real_inner_self_eq_norm_sq` (or `_eq_norm_mul_norm`),
  and `‖y - z‖^2 = (1/L)^2 * ‖g‖^2` (`norm_smul`, `‖(1/L)‖ = 1/L` since `L>0`).
  The cross terms collapse: `(1/L)(⟪∇f x, ∇f y - ∇f x⟫ + ⟪∇f y, ∇f x - ∇f y⟫) = -(1/L)‖g‖²`,
  and `(L/2)(1/L²)‖g‖² = (1/(2L))‖g‖²`, leaving
  `f x - f y ≤ ⟪∇f x, x-y⟫ - (1/L)‖g‖² + (1/(2L))‖g‖² = ⟪∇f x, x-y⟫ - (1/(2L))‖g‖²`.
  Close the real-scalar algebra with `nlinarith`/`ring_nf` after rewriting inner products to
  real arithmetic; mind §7.2 (`⟪a,b⟫_ℝ` ordering) — prefer `real_inner_comm`/explicit rewrites.
### (b) `inner_gradient_sub_nonneg` (same hypotheses):
  `(1/(2*L)) * ‖gradient f x - gradient f y‖^2 ≤ ⟪gradient f x - gradient f y, x - y⟫_ℝ`
  Add `cocoercive hf hdiff hL hsmooth x y` and `cocoercive hf hdiff hL hsmooth y x`:
  the `f x - f y` and `f y - f x` cancel, giving
  `0 ≤ ⟪∇f x - ∇f y, x - y⟫ - (1/L)‖∇f x - ∇f y‖²`, hence `(1/L)‖·‖² ≤ ⟪·,·⟫`,
  which implies the stated `(1/(2L))‖·‖² ≤ ⟪·,·⟫` (since `‖·‖² ≥ 0`, `L > 0`). Use
  `real_inner_comm`/`inner_sub_left` to combine; finish with `nlinarith [norm_nonneg …]`.

# HYPOTHESIS TAGS
Pure math lemmas; `hf, hdiff, hL, hsmooth` are genuine inputs. The book states Lemma 11.1 for
"`L`-smooth f" but the proof needs convexity too — the `ConvexOn` hypothesis is the deliberate
correction (already documented in the file's module docstring). Do NOT add or drop hypotheses.

# TOUCH-SET — modify ONLY:
`StatLean/Optimization/ForMathlib/GradientCalc.lean`,
`StatLean/Optimization/Smoothness/CoCoercive.lean`.
Do NOT touch any `Defs.lean`, `FirstOrderConvex.lean` (sibling branch owns it), the umbrella,
`StatLean.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `notes/`, or anything
under `StatLean/ConcentrationInequalities/` or `StatLean/AsymptoticStatistics/`. Never `lake update`.

# BUILD (inside the worktree)
  lake build StatLean.Optimization.ForMathlib.GradientCalc StatLean.Optimization.Smoothness.CoCoercive
Goal: zero `sorry` in these two files, no errors.
