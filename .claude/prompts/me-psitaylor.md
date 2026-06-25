# Close the 1 sorry in ForMathlib/PsiTaylor.lean (second-order Taylor upper bound)

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. ON the cluster.

## CRITICAL build discipline (do NOT violate)
- To check your work, run **plain foreground** `lake build StatLean.HighDimensionalStatistics.ForMathlib.PsiTaylor`
  and read its output directly. **NEVER** background a build (`&`), **NEVER** write `until pgrep … ; sleep …`
  poll loops, **NEVER** nest `srun`/`sbatch`. You are already inside the allocation. A foreground `lake build`
  returns its result; just read it. (Violating this wastes the whole session.)
- When the build shows **0 errors and 0 sorries**, you are DONE — stop immediately (the wrapper auto-commits).

## Scope
- **Only edit** `StatLean/HighDimensionalStatistics/ForMathlib/PsiTaylor.lean`. Keep the signature, the
  USER-INPUT tags, and the docstring. Lines ≤ 100.

## The lemma
`psi_taylor_upper (ψ ψ' ψ'' : ℝ → ℝ) (B) (hψ' : ∀ x, HasDerivAt ψ (ψ' x) x)
 (hψ'' : ∀ x, HasDerivAt ψ' (ψ'' x) x) (hbound : ∀ x, ψ'' x ≤ B^2) (a h : ℝ) :
 ψ (a + h) - ψ a - h * ψ' a ≤ B^2 / 2 * h^2`.

## Proof approach
Let `G : ℝ → ℝ := fun t => B^2/2 * t^2 - (ψ (a + t) - ψ a - t * ψ' a)`. Then:
- `G 0 = 0` (compute).
- `G` has derivative `G' t = B^2 * t - (ψ' (a + t) - ψ' a)` at every `t` (build via `HasDerivAt`:
  the `ψ (a+t)` piece uses `(hψ' (a+t)).comp t (hasDerivAt_const_add … )` / `hasDerivAt_id`; assemble
  with `.sub`, `.const_mul`, `.const_sub`). Call this `hG' : ∀ t, HasDerivAt G (B^2 * t - (ψ' (a+t) - ψ' a)) t`.
- `G' 0 = 0` (compute).
- `G'` has derivative `G'' t = B^2 - ψ'' (a + t) ≥ 0` (from `hψ''` + `hbound`). So `G'` is monotone
  (`StrictMono`/`Monotone` via `... hasDerivAt ... 0 ≤ deriv`); since `G' 0 = 0`, `G' t ≤ 0` for `t ≤ 0`
  and `G' t ≥ 0` for `t ≥ 0`.
- Hence `G` is minimized at `0`, so `G h ≥ G 0 = 0`, i.e. `ψ(a+h) - ψ a - h*ψ' a ≤ B^2/2 * h^2`.

Implementation hints (pick whichever builds cleanly — try `exact?`/`apply?` for exact names):
- Cleanest: `G` is **convex** because `G'' ≥ 0` — use `convexOn_of_hasDerivWithinAt2_nonneg` or
  `ConvexOn` from monotone derivative (`StrictMonoOn`/`monotoneOn_of_deriv_nonneg` analog with `HasDerivAt`).
  A convex differentiable function lies above its tangent at `0`: `G t ≥ G 0 + G' 0 * (t - 0) = 0`
  (look for `ConvexOn.… tangent` / `inner_smul_le_…`, 1-D first-order convexity).
- Alternative (no convexity): two applications of
  `Convex.image_sub_le_mul_sub_of_deriv_le` / `Convex.inner_le_iff`-style mean-value bounds on `[0,h]`
  (and `[h,0]` for `h<0`), bounding `ψ'(a+t) - ψ' a ≤ B^2 t` then integrating; case-split on `0 ≤ h`.
- `nlinarith`/`linarith` to finish the algebra; `HasDerivAt.deriv` to extract `deriv` if a lemma wants it.

Report the final `lake build` line (must say 0 sorries) — no `#print axioms` needed (it's a pure-Mathlib lemma).
