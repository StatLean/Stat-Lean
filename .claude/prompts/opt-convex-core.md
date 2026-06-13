Read CLAUDE.md (repo root) first and obey it — especially §2 (hypothesis-discipline tags),
§6 (search tools), §7 (Lean gotchas), §9, §10. Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`,
`./tools/check.sh '<fully.qualified.name>'`, `./tools/explore.sh "..."`.

# CONTEXT
The `StatLean/Optimization/` area (Lu, *Big Data Analysis* ch.10–12) is scaffolded with
statement-first `sorry` stubs. Everything is over a real inner product space
`{E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`, notation `⟪·,·⟫_ℝ`
(`open scoped InnerProductSpace`), Riesz gradient `gradient`/`∇` (`open scoped Gradient`).
Concept defs already exist and are CORRECT — do not change them:
- `IsSubgradient (f : E → ℝ) (x g : E) : Prop := ∀ y, ⟪g, y - x⟫_ℝ ≤ f y - f x`  (Convex/Defs)
- `subdifferential f x : Set E := {g | IsSubgradient f x g}`  (Convex/Defs)

# TASK — close these `sorry`s (3 files), proofs only, do NOT change any signature:

## 1. `StatLean/Optimization/ForMathlib/FirstOrderConvex.lean`
`inner_gradient_le_sub_of_convexOn {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f)
  (hdiff : Differentiable ℝ f) (x y : E) : f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y`
The gradient inequality (convex function lies above its tangent), Lu-BDA §10.2.
Strategy (1-D restriction): let `φ : ℝ → ℝ := fun t => f (x + t • (y - x))`. Then
`φ` is convex on `[0,1]` (compose `hf` with the affine map `t ↦ x + t•(y-x)`), and
`HasDerivAt φ (⟪gradient f x, y - x⟫_ℝ) 0` (chain rule: `(hdiff x).hasGradientAt`
gives `HasFDerivAt f (toDual ℝ E (gradient f x)) x`; the line has derivative `y-x`;
`(fderiv ℝ f x) (y-x) = ⟪gradient f x, y-x⟫_ℝ`). Then apply the 1-D first-order convexity
inequality `φ 1 ≥ φ 0 + deriv φ 0 * (1 - 0)`. Search for the 1-D lemma:
`./tools/loogle.sh '"inner_le_of"'`, `#leansearch "convex differentiable function above tangent line"`,
and inspect `Mathlib/Analysis/Convex/Deriv.lean` and `Mathlib/Analysis/Convex/Slope.lean`
(candidates: `ConvexOn.slope_le_of_lt`, `ConvexOn.le_..._deriv`, `inner_le_..`). If no clean
1-D tangent lemma exists, prove it from `ConvexOn.slope_mono`/`StrictMonoOn` of the slope, or
directly from the limit of difference quotients (`hasDerivAt`+`ConvexOn.slope` monotonicity).
NOTE: `Set.univ` convexity restricted to the line segment is fine; you may need
`ConvexOn.comp_affineMap` or build convexity of `φ` on `Set.Icc 0 1` by hand.

## 2. `StatLean/Optimization/Convex/Subgradient.lean`
`gradient_mem_subdifferential {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f)
  (hdiff : Differentiable ℝ f) (x : E) : gradient f x ∈ subdifferential f x`
Immediate: unfold `mem_subdifferential`/`IsSubgradient`; goal becomes
`∀ y, ⟪gradient f x, y - x⟫_ℝ ≤ f y - f x`, which is `inner_gradient_le_sub_of_convexOn`
rearranged (`le_sub_iff_add_le` / `sub_nonneg`). ~3 lines.

## 3. `StatLean/Optimization/LocalGlobal.lean`
(a) `isGlobalMin_iff_zero_mem_subdifferential (f : E → ℝ) (xstar : E) :
   (∀ y, f xstar ≤ f y) ↔ (0 : E) ∈ subdifferential f xstar`
Definitional: `0 ∈ ∂f xstar` unfolds to `∀ y, ⟪0, y - xstar⟫_ℝ ≤ f y - f xstar`;
`inner_zero_left` gives `⟪0,·⟫_ℝ = 0`; then `0 ≤ f y - f xstar ↔ f xstar ≤ f y` by `sub_nonneg`.
No convexity needed.
(b) `forall_le_of_isLocalMin {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {xstar : E}
   (hloc : IsLocalMin f xstar) (y : E) : f xstar ≤ f y`
Book proof: `IsLocalMin` gives `∀ᶠ z in 𝓝 xstar, f xstar ≤ f z`; along the segment
`z_γ = (1-γ)•xstar + γ•y = xstar + γ•(y-xstar)`, for small `γ>0` we have `f xstar ≤ f z_γ`,
and convexity gives `f z_γ ≤ (1-γ) f xstar + γ f y`. Subtract: `0 ≤ γ (f y - f xstar)`,
divide by `γ>0`. Extract a usable small `γ` from the `𝓝`-eventually statement
(`Metric.eventually_nhds_iff` / `Filter.Eventually.exists`); the path `γ ↦ z_γ` is continuous
so the eventual bound transfers. Use `hf.2` (the `ConvexOn` inequality) with weights `1-γ, γ`.

# HYPOTHESIS TAGS
These are pure math lemmas; hypotheses (`hf`, `hdiff`, `hloc`) are genuine inputs. No new
hypotheses should be added. If you must add one, tag `-- LEAN-ONLY: …` with justification.
Do not weaken or strengthen any stated conclusion.

# TOUCH-SET — modify ONLY these three files:
`StatLean/Optimization/ForMathlib/FirstOrderConvex.lean`,
`StatLean/Optimization/Convex/Subgradient.lean`,
`StatLean/Optimization/LocalGlobal.lean`.
Do NOT touch any `Defs.lean`, the umbrella `StatLean/Optimization.lean`, `StatLean.lean`,
`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `notes/`, or anything under
`StatLean/ConcentrationInequalities/` or `StatLean/AsymptoticStatistics/`. Never `lake update`.

# BUILD (inside the worktree)
  srun -p shared -c 8 --mem=24G -t 0:40:00 lake build StatLean.Optimization.ForMathlib.FirstOrderConvex StatLean.Optimization.Convex.Subgradient StatLean.Optimization.LocalGlobal
Then a final umbrella check:
  srun -p shared -c 8 --mem=24G -t 0:40:00 lake build StatLean.Optimization
Goal: zero `sorry` in these three files, no errors. Leave other files' sorries untouched.
