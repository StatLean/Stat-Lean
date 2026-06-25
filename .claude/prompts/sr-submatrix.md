Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use the search tools (`./tools/loogle.sh`, `./tools/api.sh`, `exact?`, `simp?`). Never `lake update`. You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries.

# CONTEXT (do NOT modify other files)
`StatLean/HighDimensionalStatistics/ForMathlib/SupportSubmatrix.lean` (namespace
`StatLean.HighDimensionalStatistics`, `open Matrix`, `open scoped InnerProductSpace`,
`variable {n d : ℕ}`) defines, with `↥S = {x // x ∈ S}` for `S : Finset (Fin d)`:
* `Xsub X S = X.submatrix id Subtype.val : Matrix (Fin n) ↥S ℝ`  (columns of X indexed by S)
* `designSub X S = Matrix.toEuclideanLin (Xsub X S) : E^{↥S} →ₗ E^n`
* `col X j = WithLp.toLp 2 (fun i => X i j) : E^n`  (j-th column)

Background already in the library:
* `designMap X = Matrix.toEuclideanLin X` (`LinearModel/Defs.lean`); note the pattern from
  `Lasso/RandomNoise.lean`: `(designMap M v).ofLp = M *ᵥ v.ofLp` holds by `rfl`.
* `EuclideanSpace.norm_eq`, `WithLp.ofLp`/`WithLp.toLp`, `WithLp.ofLp_toLp`.

# TASK
Close ALL 7 sorries in `SupportSubmatrix.lean` to 0-sorry. Do NOT change any signature.

# PROOFS
- `designSub_apply`: `(designSub X S v).ofLp = (Xsub X S).mulVec v.ofLp`. Try `rfl`; else
  `simp [designSub, Matrix.toEuclideanLin_apply]` (mirror RandomNoise's `rfl` for `designMap`).
- `Xsub_mulVec`: `funext i`; unfold `Matrix.mulVec`, `dotProduct`, `Xsub`, `Matrix.submatrix_apply`.
  LHS `= ∑ k:↥S, X i k.val * v k`; RHS `= ∑ j:Fin d, X i j * (if h:j∈S then v⟨j,h⟩ else 0)`.
  Bridge with `Finset.sum_subtype` / `Fintype.sum_subtype` (sum over `↥S` ↔ sum over `S` with the
  `dite`), or `Finset.sum_attach`. `Finset.sum_dite_eq`-style simp may help collapse the `if`.
- `Xsub_transpose_mulVec_apply`: `simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Xsub,
  Matrix.submatrix_apply, id]` — `(Xsub X S)ᵀ i k = (Xsub X S) k i = X k i.val`.
- `normSq_designSub`: rewrite `‖designSub X S v‖^2` via `designSub_apply` and
  `EuclideanSpace.norm_eq` (so `‖Xₛv‖² = ∑ i:Fin n, ((Xsub).mulVec v.ofLp i)^2`); the RHS is
  `((Xsub)ᵀ.mulVec ((Xsub).mulVec v.ofLp)) ⬝ᵥ v.ofLp`. Use `Matrix.dotProduct_mulVec`
  (`x ⬝ᵥ (Aᵀ *ᵥ y) = (A *ᵥ x) ⬝ᵥ y`) / `Matrix.dotProduct_comm` to fold `(Xₛᵀ(Xₛv)) ⬝ᵥ v` into
  `(Xₛv) ⬝ᵥ (Xₛv) = ∑ i, (Xₛv i)^2`. Search: `./tools/loogle.sh '"dotProduct_mulVec"'`.
- `col_eq_designMap_single`: `apply WithLp.ofLp_injective 2; funext i`; both sides `.ofLp i = X i j`
  via `Matrix.mulVec_single` (`(M *ᵥ Pi.single j 1) i = M i j`) and `col`/`EuclideanSpace.single`.
- `designMap_restrict_eq_designSub`: `apply WithLp.ofLp_injective 2` (or compare `.ofLp`); both reduce
  to `X.mulVec`. LHS `(designMap X (restrict S θ)).ofLp = X *ᵥ (restrict S θ).ofLp`,
  RHS `(designSub …).ofLp = (Xsub X S) *ᵥ (fun i:↥S => θ.ofLp i.val)` `= X *ᵥ (extend …)` by `Xsub_mulVec`.
  Then `(restrict S θ).ofLp j = if j∈S then θ.ofLp j else 0` (`restrict_ofLp_apply`) matches the `dite`.
- `inner_designMap_transpose`: `⟪Xθ,u⟫ = ⟪θ,Xᵀu⟫`. Turn both inner products into `dotProduct` via
  `PiLp.inner_apply`/`RCLike.inner_apply` (real ⇒ plain `*`, see CLAUDE.md §7.2), then it is
  `(X *ᵥ θ.ofLp) ⬝ᵥ u.ofLp = θ.ofLp ⬝ᵥ (Xᵀ *ᵥ u.ofLp)` = `Matrix.dotProduct_mulVec`/`dotProduct_comm`.

# REQUIREMENTS
ZERO sorry. Keep the 5 signatures verbatim (they are hypothesis-free identities — no tags to add).
You MAY add `private` helper lemmas in THIS file only. Do not touch any other file, the umbrella,
`lakefile.lean`, `lake-manifest.json`, or `lean-toolchain`.

# TOUCH-SET: ONLY  StatLean/HighDimensionalStatistics/ForMathlib/SupportSubmatrix.lean
# BUILD: lake build StatLean.HighDimensionalStatistics.ForMathlib.SupportSubmatrix
# DONE = build exits 0; `lake build ... 2>&1 | grep -c sorry` is 0; commit
  (`sr(submatrix): support-submatrix bridges (Wainwright §7.5)`).
  Report: build status, sorry count, any helper lemmas added, any signature that needed adjustment.
