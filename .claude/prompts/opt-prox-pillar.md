Read CLAUDE.md (repo root) first and obey it — §2, §6, §7 (esp. §7.2 real inner product), §9, §10.

# CONTEXT
`StatLean/Optimization/` over a real inner product space `{E} [NormedAddCommGroup E]
[InnerProductSpace ℝ E] [CompleteSpace E]`, `⟪·,·⟫_ℝ`, gradient `gradient`/`∇`.
CORRECT defs (do not change): `proxObj h x z = (1/2)*‖z-x‖^2 + h z` (noncomputable),
`IsProxMinimizer h x z := ∀ w, proxObj h x z ≤ proxObj h x w` (Prox.Defs);
`IsLSmooth f L := ∀ x y, f y ≤ f x + ⟪∇f x, y-x⟫_ℝ + (L/2)‖x-y‖²` (Smoothness.Defs).
PROVED (use freely): `inner_gradient_le_sub_of_convexOn hf hdiff x y :
  f x + ⟪gradient f x, y-x⟫_ℝ ≤ f y` (ForMathlib.FirstOrderConvex).

# TASK — close both `sorry`s in `StatLean/Optimization/Prox/Pillar.lean`:

## (a) `prox_variational_inequality {h : E → ℝ} (hh : ConvexOn ℝ Set.univ h) {x z : E}
  (hz : IsProxMinimizer h x z) (w : E) : ⟪x - z, w - z⟫_ℝ ≤ h w - h z`
Proof: for `t ∈ (0,1]`, let `wt := z + t • (w - z)`. Convexity of `h` (`hh.2`, weights `1-t,t`,
with `wt = (1-t)•z + t•w`) gives `h wt ≤ (1-t) * h z + t * h w`. Minimality `hz wt`:
`(1/2)‖z-x‖² + h z ≤ (1/2)‖wt-x‖² + h wt ≤ (1/2)‖wt-x‖² + (1-t) h z + t h w`. Since
`wt - x = (z-x) + t•(w-z)`, expand `‖wt-x‖² = ‖z-x‖² + 2t⟪z-x,w-z⟫_ℝ + t²‖w-z‖²`
(`norm_add_sq_real` / `real_inner_smul_right`, `real_inner_self_eq_norm_sq`). Cancel `‖z-x‖²`,
subtract `(1-t)h z`, divide by `t>0`:
  `h z ≤ ⟪z-x, w-z⟫_ℝ + (t/2)‖w-z‖² + h w`   for all `t ∈ (0,1]`.
Rearranged: `(h z - h w - ⟪z-x,w-z⟫_ℝ) ≤ (t/2)‖w-z‖²` for all small `t>0`; LHS is constant, RHS→0,
so LHS ≤ 0, i.e. `h z - h w ≤ ⟪z-x, w-z⟫_ℝ`. Negate (`⟪x-z,w-z⟫_ℝ = -⟪z-x,w-z⟫_ℝ` by
`inner_neg_left`/`neg_sub`): `⟪x-z, w-z⟫_ℝ ≤ h w - h z`. For the "LHS ≤ 0" step use
`le_of_forall_pos_le_add` or `ge_of_tendsto` (RHS `(t/2)‖w-z‖²` tends to 0 as `t→0⁺`); handle the
`w = z` case (goal trivial, both sides 0) and `‖w-z‖=0` directly. NOTE the §7.2 ordering caveat.

## (b) `pillar {f h : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
  {L : ℝ} (hL : 0 < L) (hsmooth : IsLSmooth f L) (hh : ConvexOn ℝ Set.univ h)
  {x y yplus : E}
  (hyplus : IsProxMinimizer ((1/L) • h) (y - (1/L) • gradient f y) yplus) :
  (f yplus + h yplus) - (f x + h x) ≤ (L/2)*‖x - y‖^2 - (L/2)*‖x - yplus‖^2`
(Lu-BDA Lemma 12.1.) Combine three inequalities:
  * **smoothness** `hsmooth y yplus`: `f yplus ≤ f y + ⟪∇f y, yplus-y⟫_ℝ + (L/2)‖y-yplus‖²`;
  * **convexity of f** (`inner_gradient_le_sub_of_convexOn hf hdiff y x`):
    `f y - f x ≤ ⟪∇f y, y-x⟫_ℝ` (rearranged);
  * **prox variational** via (a) applied to `h' := (1/L)•h`, `x' := y - (1/L)•∇f y`, `z := yplus`,
    `w := x`: `⟪(y - (1/L)•∇f y) - yplus, x - yplus⟫_ℝ ≤ ((1/L)•h) x - ((1/L)•h) yplus`,
    i.e. multiply by `L>0`: `⟪L•(y - yplus) - ∇f y, x - yplus⟫_ℝ ≤ h x - h yplus`
    (`Pi.smul_apply`, `smul_eq_mul`; `real_inner_smul_left`). This replaces the book's
    `∂h(yplus)` optimality `0 = ∇f y + L(yplus - y) + ∂h(yplus)`.
Add `f yplus - f x` (smoothness + convexity) to `h yplus - h x` (variational), then use the
polarization identity `‖a‖² - 2⟪a,b⟫_ℝ = ‖a-b‖² - ‖b‖²` (book line 171; in Lean
`norm_sub_sq_real`/`real_inner_…`) with `a = yplus - y`, `b = yplus - x` (or as the algebra
dictates) to convert the gradient/inner terms into `(L/2)‖x-y‖² - (L/2)‖x-yplus‖²`. Finish the
real-scalar algebra with `nlinarith`/`linarith` after rewriting all inner products and norms.
Recommend an intermediate `have` for each of the three inequalities, then one algebra block.

# HYPOTHESIS TAGS — all hypotheses genuine inputs; the `IsProxMinimizer` arg is the oracle
("the algorithm computes the prox step"), tag `-- USER-INPUT: prox step; Lu-BDA §12.1` if you add
any wrapper. Do not change signatures.

# TOUCH-SET — modify ONLY `StatLean/Optimization/Prox/Pillar.lean`. Nothing else. Never `lake update`.

# BUILD (inside the worktree)
  srun -p shared -c 8 --mem=24G -t 0:50:00 lake build StatLean.Optimization.Prox.Pillar
