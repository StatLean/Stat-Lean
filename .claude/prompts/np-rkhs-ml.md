FIRST: read `.claude/prompts/np-rkhs-header.md` in this worktree and obey every rule in
it for the whole session.  It is the contract of this lane.

# Lane: np/rkhs-ml — feature maps, separation, max margin, representer

Touch-set (the ONLY files you may edit):
- StatLean/NonparametricStatistics/RKHS/FeatureMap.lean
- StatLean/NonparametricStatistics/RKHS/Separation.lean
- StatLean/NonparametricStatistics/RKHS/MaxMargin.lean
- StatLean/NonparametricStatistics/RKHS/Representer.lean

Build targets: `lake build StatLean.NonparametricStatistics.RKHS.FeatureMap` (then
Separation, MaxMargin, Representer).

Close every `sorry`.  Statements are frozen (see header rule 5).

## FeatureMap.lean

- `featureKernel_self`: `inner_self_eq_norm_sq_to_K`.
- `IsKernelFun.exists_featureMap`: `IsKernelFun.exists_rkhs` (Moore.lean) + take
  `φ := kernelFun` and `scalarKernel_eq_featureKernel` (KernelFunction.lean).
- `norm_featurePredictor_le`: Cauchy–Schwarz + `featureKernel_self`
  (`Real.sqrt` of the squared norm: `Real.sqrt_sq`, `RCLike.norm_sq...` — the `re` of
  `(‖φ x‖ : 𝕜)^2` is `‖φ x‖²`).

## Separation.lean

- `SeparatesData.ne_zero`: at some `i`, `0 < lab i * (⟪x i, 0⟫ − c) = lab i * (−c)`
  would have to hold with `v = 0`… careful: `v = 0` gives `⟪x i, v⟫ = 0`; the
  hypothesis then says `0 < lab i * (−c)` for ALL `i` — that alone is not a
  contradiction!  Re-read: with a single point it IS satisfiable (hyperplane with
  `v = 0` is degenerate: `hyperplane 0 c` is `∅` (c ≠ 0) or `univ` (c = 0), but
  `SeparatesData` as defined only involves inner products, and `v = 0, c = −(lab i)⁻¹`…
  For a SINGLE label sign this is satisfiable with `v = 0`!  CHECK whether the
  statement is provable: it needs both a `+1`-ish and a `−1`-ish point?  No: hypothesis
  only `Nonempty ι`.  If `v = 0`: `0 < lab i * (−c)` for all `i`.  Choose `i₀`; this is
  consistent (e.g. all `lab i` same sign).  SO THE LEMMA AS STATED IS FALSE unless the
  labels take both signs... WAIT: re-check — is it?  `SeparatesData 0 c x lab` holds
  iff `∀ i, 0 < lab i * (−c)`.  With all labels `+1` and `c = −1`: `0 < 1` ✓.  So
  `SeparatesData 0 (−1) x (fun _ => 1)` holds and `v = 0`.  The lemma is FALSE as
  stated.  → Per header rule 5: do NOT weaken silently; leave the `sorry`, and place a
  comment above it explaining the counterexample (`v = 0, c = −1`, all labels `+1`)
  and that the fix (adding "both labels occur" input) is deferred to the laptop
  session.  Then AVOID using this lemma elsewhere (it is not needed by the other
  files; `infDist_hyperplane` takes `v ≠ 0` as input).
- `infDist_hyperplane`: reduce to the linear hyperplane through 0 by translating by
  `k • v` with `k = c/‖v‖²`; distance to the kernel of a nonzero functional.  Mathlib
  may already have this: search `norm_sub_...` /
  `Metric.infDist` + `SetLike`… candidates: `Submodule.norm_sub_orthogonalProjection`?
  Better: `{y | ⟪y,v⟫ = c}` as a coset of `(𝕜∙v)ᗮ`.  Compute
  `infDist p S = ‖P_{(span v)} (p − k•v)‖ = |⟪p,v⟫ − c|/‖v‖` via
  `Submodule.starProjection_singleton` (projection onto a span of a single vector:
  `⟪v,p⟫/‖v‖² • v` — search `orthogonalProjection_singleton` in
  Projection files) and the distance-minimizing property
  (`Submodule.norm_sub_starProjection_le`? search `dist_starProjection`, 
  `norm_sub_starProjection`… also `Metric.infDist` characterizations
  `Metric.infDist_le_dist_of_mem` + `le_infDist`).
- `inner_starProjection_of_mem`: `starProjection` decomposition:
  `v − P v ∈ Mᗮ` (`Submodule.sub_starProjection_mem_orthogonal`-style name), then
  `⟪m, v − Pv⟫ = 0` for `m ∈ M` (mind slot order: `Mᗮ` members are orthogonal to `M`
  members on either side via `inner_left/right_of_mem_orthogonal`).
- `SeparatesData.starProjection`: rewrite each constraint with the previous lemma.

## MaxMargin.lean

- `convex_marginFeasible`: given `(v₁,c₁),(v₂,c₂)` feasible and `t ∈ [0,1]`, the pair
  `(t v₁ + (1−t) v₂, t c₁ + (1−t) c₂)` is feasible: the constraint function is affine
  in `(v,c)` jointly; `1 = t·1 + (1−t)·1 ≤ ...` by `add_le_add` of scaled constraints
  (needs `0 ≤ t`, `0 ≤ 1−t`).  Expand `inner_add_right`? mind: `⟪x i, t•v₁ + …⟫` —
  `inner_smul_right` with REAL scalars.
- `isClosed_marginFeasible`: eliminate `c`.  For each `i` with `lab i > 0` the
  constraint reads `c ≤ ⟪x i, v⟫ − 1/lab i`; with `lab i < 0`:
  `c ≥ ⟪x i, v⟫ − 1/lab i`; `lab i = 0` ⇒ infeasible.  So
  `marginFeasible = {v | (∀ i, lab i ≠ 0) ∧ sup_{neg} bound ≤ inf_{pos} bound}` …
  formalizing the elimination is fiddly; an alternative robust route: show
  `marginFeasible = ⋂ over pairs/cases` — simplest concrete plan: prove
  `v ∈ marginFeasible ↔ (∀ i, lab i ≠ 0) ∧ (∀ i j, lab i < 0 → 0 < lab j → boundᵢ ≤ boundⱼ) ∧ (edge cases when one side is empty…)`
  Actually cleanest: `∃ c ∈ closed interval [A v, B v]` where
  `A v = max over negative-label i` (a `Finset.sup'` when nonempty),
  `B v = min over positive-label i`.  To dodge the empty-side bookkeeping, use:
  the constraint set in `(v, c)` is closed; feasibility of `v` says the `c`-section is
  nonempty; the `c`-sections are intervals whose endpoints are continuous in `v`.
  Take a convergent sequence `vₙ → v` with witnesses `cₙ`; show `cₙ` is BOUNDED
  (pick any i⁺ with lab > 0 and any i⁻ with lab < 0 to sandwich `cₙ`; if only one sign
  occurs, `cₙ` can be clamped: replace `cₙ` by `max/min` with a fixed continuous bound
  — e.g. when no negative labels exist, `cₙ` can be decreased to
  `min_i (⟪x i, vₙ⟫ − 1/lab i)` which converges), extract a convergent subsequence
  (Bolzano–Weierstrass on ℝ: `tendsto_subseq_of_bounded`), pass to the limit in each
  (closed) constraint.  Commit intermediate lemmas as you go.
- `marginFeasible_nonempty`: from strict separation, `δ := min_i (lab i * (⟪x i,v⟫−c))`
  over the finite nonempty index… careful `n = 0`: then ANY `v` is feasible (empty ∀),
  handle first (`Fin 0` → pick `v = 0, c = 0`).  For `n > 0`: `δ > 0`
  (`Finset.inf'_lt_iff` / `Finset.lt_inf'_iff`), then `(δ⁻¹ • v, δ⁻¹ * c)` satisfies
  `1 ≤ lab i * (⟪x i, δ⁻¹•v⟫ − δ⁻¹ c) = δ⁻¹ * (lab i * (⟪x i,v⟫ − c))` ✓.
- `existsUnique_min_norm_marginFeasible`: `exists_norm_eq_iInf_of_complete_convex`
  (`Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean`) on the nonempty
  closed convex feasible set gives existence of a norm-minimizer; uniqueness via the
  parallelogram law: two minimizers `w₁ ≠ w₂` make `(w₁+w₂)/2` feasible (convexity)
  with strictly smaller norm — `norm_add_sq_real` + `norm_sub_sq_real` algebra
  (`nlinarith` with `sq_nonneg` hints), or search
  `norm_eq_iInf_iff_real_inner_le_zero` for a characterization-based route.
- `min_norm_marginFeasible_mem_span`: let `M := span ℝ (range x)` — it is
  finite-dimensional (`FiniteDimensional.span_of_finite`, `Set.finite_range`), hence
  complete, hence `[M.HasOrthogonalProjection]` available via
  `haveI := FiniteDimensional.complete ℝ M`-style instances (they may fire
  automatically).  `P w` is feasible (`SeparatesData.starProjection`-style
  computation with `inner_starProjection_of_mem`) with `‖P w‖ ≤ ‖w‖`
  (`Submodule.norm_starProjection_apply_le`? search `norm_starProjection`), so by
  minimality `‖w‖ ≤ ‖P w‖`; equality in the Pythagoras split forces `w = P w ∈ M`
  (`Submodule.starProjection_eq_self_iff`; from
  `‖w‖² = ‖Pw‖² + ‖w − Pw‖²` — search `norm_sq_eq_add_norm_sq_projection` /
  `Submodule.norm_sq_eq...`).
- `isMaxMarginHyperplane_of_min_norm`: take the witness `c` from `hw` (choice).
  (a) `(w, c)` separates: `1 ≤ lab i (⟪x i,w⟫ − c)` and `lab i = ±1` ⇒ the product is
  `≥ 1 > 0`.
  (b) margin of `(w,c)` is `≥ 1/‖w‖`: `infDist_hyperplane` gives
  `d(x i, V) = |⟪x i,w⟫ − c|/‖w‖ ≥ 1/‖w‖` since `|⟪x i,w⟫ − c| ≥ 1` (from the
  constraint with `|lab i| = 1`; `abs_le`… note `lab i * t ≥ 1` with `lab i = ±1` ⇒
  `|t| ≥ 1`).
  (c) any separating `(v', c')` has margin `≤ 1/‖w‖`: let `m := dataMargin x v' c'`.
  If `m ≤ 0` trivial (`1/‖w‖ > 0`; `w ≠ 0` because `‖w‖ ≥ ... > 0` — from any
  constraint, `w = 0` would give `1 ≤ lab i * (−c)` for all i… wait that IS possible
  when all labels share a sign!  BUT then margins: hyperplane of `v' = 0`…
  `hyperplane 0 c'` is `∅` or `univ`, `infDist` to `∅` is `0` by convention, to
  `univ` is `0` — so margins are 0 and (c) is easy; handle `v' = 0` and `w = 0`
  cases separately via `Metric.infDist_empty`… check Mathlib's convention:
  `Metric.infDist p ∅ = 0` ✓ (`Metric.infDist_empty`), and `p ∈ s → infDist = 0`.)
  For `m > 0` and `v' ≠ 0`: each `i` has `|⟪x i, v'⟫ − c'| ≥ m ‖v'‖` and the sign
  matches `lab i`, so `lab i * (⟪x i, v'⟫ − c') ≥ m ‖v'‖`, hence
  `(1/(m ‖v'‖)) • v'` with offset `c'/(m ‖v'‖)` is FEASIBLE with norm `1/m`; minimality
  of `‖w‖` gives `‖w‖ ≤ 1/m` i.e. `m ≤ 1/‖w‖` = margin(w,c) bound from (b)…
  (b) actually gives `dataMargin x w c ≥ 1/‖w‖`; combined: `m ≤ dataMargin x w c` ✓.
  This is the most intricate proof of the lane; extract `private` lemmas per step and
  commit each.
- `norm_sq_eq_gram_quadForm`: expand `inner_sum`/`sum_inner`/`inner_smul_*` over the
  real field; `real_inner_comm` to match `⟪x j, x i⟫`.

## Representer.lean

Instances: `dataSpan` has a `FiniteDimensional` instance (declared in-file) ⇒
`CompleteSpace` ⇒ `HasOrthogonalProjection` (automatic instances).

- `apply_eq_zero_of_mem_dataSpan_orthogonal`: `h ⊥ kernelFun H (x i)` (a generator ∈
  span), then `h (x i) = ⟪k_{x i}, h⟫ = 0` (`inner_kernelFun`;
  `Submodule.inner_right_of_mem_orthogonal` with `Submodule.mem_span`-generator
  membership `Submodule.subset_span ⟨i, rfl⟩`).  Mind slot orientation.
- `starProjection_dataSpan_apply`: `f = P f + (f − P f)`, second summand ∈ `(dataSpan)ᗮ`
  vanishes at data points; `map_sub`-style through the coercion (`RKHS.coe_sub`).
- `representer_mem_dataSpan`: write `f₀ = g + h`, `g := P f₀`, `h ⊥ dataSpan`.
  `J(g) ≤ J(f₀)` with equality iff `W(‖g‖²) = W(‖g‖² + ‖h‖²)`; StrictMono ⇒ `‖h‖ = 0`.
  Use `hmin` at `f := g` for the reverse inequality.  Norm split:
  `‖f₀‖² = ‖g‖² + ‖h‖²` (orthogonal Pythagoras: search `norm_add_sq_eq` for
  orthogonal summands, `Submodule.norm_sq_eq_add...`, or
  `inner_mul_le_norm_mul_norm`-free direct computation with `⟪g,h⟫ = 0`:
  `norm_add_sq_real`-analogue for `𝕜` via `re ⟪g,h⟫ = 0`).
- `representer_starProjection_isMin`: same decomposition, `Monotone` gives
  `J(P f₀) ≤ J(f₀) ≤ J(f)`.
- `representer_existsUnique_of_convex`:
  *Uniqueness*: for minimizers `f, g`: apply minimality at `(f+g)/2` and add;
  parallelogram (`norm_add_sq_real`… over `𝕜` use `re`-versions:
  `parallelogram_law_with_norm`) + convexity of `L` (applied at the midpoint of the
  value vectors: `hL.2` with `t = 1/2`; note `((f+g)/2) (x i) = (f (x i) + g (x i))/2`
  by `RKHS.coe_add`/`coe_smul`) forces `‖f − g‖² ≤ 0`.
  *Existence*: reduce to `S := dataSpan x` (finite-dim): by the weak representer
  argument, `inf over H = inf over S` and a minimizer in `S` is a global one
  (for any `f`, `J(P f) ≤ J(f)` — the `Monotone id` case of
  `representer_starProjection_isMin`-style computation with `W = id`).  On `S`:
  `J` restricted is continuous (norm continuous; `L` continuous — derive from
  convexity: search `ConvexOn.continuousOn` in
  `Mathlib/Analysis/Convex/Continuous.lean`: convex functions on a finite-dimensional
  space are continuous on the interior of their domain = `univ`; the value map
  `S → (Fin n → 𝕜)` is linear continuous in finite dim) and coercive:
  `L` has an affine minorant (`ConvexOn.exists_affine_le` on `univ`,
  `Mathlib/Analysis/Convex/...`) so
  `J(f) ≥ ‖f‖² − C₁‖f‖ − C₂ → ∞`; minimize over the closed ball
  `{‖f‖ ≤ R}` (compact in finite dim: `isCompact_closedBall` via
  `FiniteDimensional.proper`) with `IsCompact.exists_isMinOn`
  and check the ball radius beats the outside values.  Extract private lemmas; this
  existence argument is the second-hardest item of the lane.
- `convexOn_hinge`: sum of convex functions (`Finset.convexOn_sum`?  search
  `ConvexOn.sum`); each term is `max 0 ∘ affine`: affine maps are convex AND concave
  (`ConvexOn` of `fun v => 1 − lab i * v i`:
  linear + const — `LinearMap.convexOn`?  or directly:
  `(convexOn_const ...)`, `ConvexOn.add`…); `max` of two convex is convex
  (`ConvexOn.sup`).  Search `ConvexOn.sup`, `convexOn_id`, `ConvexOn.comp_affineMap`.
