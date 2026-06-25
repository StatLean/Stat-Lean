Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use the search tools and `exact?`/`simp?`. Never `lake update`. You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries. This is convex analysis; prove in named `private` pieces and time-box hard steps.

# CONTEXT (do NOT modify other files)
`StatLean/HighDimensionalStatistics/Lasso/SupportRecovery/Subgradient.lean` (namespace
`StatLean.HighDimensionalStatistics`, `open Matrix`, `open scoped InnerProductSpace`,
`variable {n d : ℕ}`) has 7 sorried theorems. Available (imported, PROVED unless noted):
* `Lasso/Defs.lean`: `lassoObjective X Y λ β = (1/2n)‖Y − Xβ‖² + λ·l1Norm β`,
  `IsLassoEstimator X Y λ β̂ = ∀β, lassoObjective β̂ ≤ lassoObjective β`.
* `SupportRecovery/Defs.lean`: `IsL1Subgradient z θ` (∀i: θᵢ>0→zᵢ=1; θᵢ<0→zᵢ=-1; |zᵢ|≤1),
  `IsKKT X Y λ θ z = (1/n)•designMap Xᵀ (designMap X θ − Y) + λ•z = 0`, `LowerEigenvalue X S cmin`.
* `ForMathlib/VecNorms.lean`: `l1Norm`, `linfNorm`, `abs_inner_le_l1Norm_mul_linfNorm`,
  `abs_le_linfNorm`, `restrict`, `restrict_*`, `l1Norm_split`, `norm_restrict_le_norm`.
* `ForMathlib/SupportSubmatrix.lean` (NOTE: may still be a stub when you start — its *statements*
  are stable; use them): `inner_designMap_transpose : ⟪Xθ,u⟫ = ⟪θ,Xᵀu⟫`,
  `designMap_restrict_eq_designSub`, `designSub`, `normSq_designSub`.
* `designMap X = Matrix.toEuclideanLin X`; `(designMap M v).ofLp = M *ᵥ v.ofLp` by `rfl`.

# TASK
Close ALL 8 sorries to 0-sorry. Keep every signature + `-- USER-INPUT` tag verbatim.

# PROOFS
- `inner_le_l1Norm_of_linfNorm_le_one`: `⟪z,θ⟫ ≤ |⟪z,θ⟫| = |⟪θ,z⟫|` (`real_inner_comm`,`le_abs_self`)
  `≤ l1Norm θ * linfNorm z` (`abs_inner_le_l1Norm_mul_linfNorm θ z`) `≤ l1Norm θ * 1` (`hz`,
  `l1Norm_nonneg`) `= l1Norm θ`.
- `l1_subgradient_iff`: (→) `⟪z,θ⟫ = ∑ zᵢθᵢ` (`PiLp.inner_apply`, real); per-i `zᵢθᵢ = |θᵢ|`
  (3 cases on sign of θᵢ using the subgradient clauses; θᵢ=0 ⇒ both sides 0); sum ⇒ `⟪z,θ⟫=l1Norm θ`;
  `linfNorm z ≤ 1` by `ciSup_le` from `|zᵢ|≤1`. (←) from `linfNorm z ≤ 1`: `|zᵢ|≤1` (`abs_le_linfNorm`);
  then `∑(|θᵢ| − zᵢθᵢ) = l1Norm θ − ⟪z,θ⟫ = 0` with each term `≥ 0`, so each `zᵢθᵢ = |θᵢ|`
  (`Finset.sum_eq_zero_iff_of_nonneg`); deduce signs.
- `loss_convex_gradient`: let `r := Y − designMap X θ`, `h := θ' − θ`; then
  `Y − Xθ' = r − Xh`, so `‖Y−Xθ'‖² = ‖r‖² − 2⟪r, Xh⟫ + ‖Xh‖²` (`norm_sub_sq_real`/`@norm_sub_pow_two_real`).
  `⟪(1/n)•Xᵀ(Xθ−Y), h⟫ = (1/n)⟪Xθ−Y, Xh⟫` (`inner_smul_left`/real + `inner_designMap_transpose`,
  note `Xθ−Y = −r`). So LHS−(1/2n)‖r‖² = (1/n)⟪Xθ−Y,Xh⟫ = −(1/n)⟪r,Xh⟫, and RHS−(1/2n)‖r‖² =
  −(1/n)⟪r,Xh⟫ + (1/2n)‖Xh‖²; conclude by `(1/2n)‖Xh‖² ≥ 0`. (`nlinarith`/`linarith` after rewriting.)
- `lasso_minimizer_exists`: apply `Continuous.exists_forall_le'` (check its exact shape via
  `./tools/check.sh 'Continuous.exists_forall_le''`). Continuity of `lassoObjective` (norm² + `l1Norm`
  continuous — `l1Norm` is a finite sum of `|·∘ofLp|`, continuous). Coercivity: `lassoObjective ≥
  λ·l1Norm β ≥ λ·‖β‖` using `‖β‖ ≤ l1Norm β` (add a `private` lemma: `∑ βᵢ² ≤ (∑|βᵢ|)²`); since
  `λ>0` this `→ ∞`, giving the "≥ f x₀ outside a compact ball" hypothesis (use a ball of radius
  `(lassoObjective 0)/λ`).
- `kkt_of_isLassoEstimator` (HARD): set `z := −(1/λ)•((1/n)•designMap Xᵀ (designMap X θ̂ − Y))`. Then
  `IsKKT` holds by `field_simp`/`smul` algebra (`λ>0`). For `IsL1Subgradient z θ̂`: per coordinate j,
  use optimality at the competitors `θ̂ ± t•(EuclideanSpace.single j 1)`. Expanding `lassoObjective`
  (the quadratic part is exact: `g(θ̂+t e_j) = g(θ̂) + t·gⱼ + (t²/2n)‖X e_j‖²` with `gⱼ = ((1/n)Xᵀ(Xθ̂−Y))ⱼ`,
  and `l1Norm(θ̂+t e_j) = l1Norm θ̂ − |θ̂ⱼ| + |θ̂ⱼ+t|`) gives `0 ≤ t·gⱼ + (t²/2n)‖Xe_j‖² + λ(|θ̂ⱼ+t|−|θ̂ⱼ|)`
  for all t. Take small `t>0` and `t<0`: deduce `θ̂ⱼ>0 ⇒ gⱼ+λ=0 ⇒ zⱼ=1`; `θ̂ⱼ<0 ⇒ zⱼ=−1`;
  `θ̂ⱼ=0 ⇒ |gⱼ|≤λ ⇒ |zⱼ|≤1`. (`zⱼ = −gⱼ/λ`.) Lift the per-coordinate optimality bound to a named
  `private` lemma. Time-box; if the limiting step is painful, derive the three sign facts via the
  inequality at a single well-chosen small `t` plus `t→0` (`le_of_forall_lt`/division).
- `lassoEstimator_of_kkt` (convex sufficiency): `∀β, lassoObjective β − lassoObjective θ ≥ 0`.
  Expand: `= [g(β)−g(θ)] + λ(‖β‖₁−‖θ‖₁) ≥ ⟪∇g(θ), β−θ⟫ + λ(‖β‖₁−‖θ‖₁)` (`loss_convex_gradient`),
  with `∇g(θ) = (1/n)Xᵀ(Xθ−Y) = −λ•z` (`hkkt`). So `≥ −λ⟪z,β−θ⟫ + λ(‖β‖₁−‖θ‖₁) =
  λ(‖β‖₁ − ⟪z,β⟫) + λ(⟪z,θ⟫ − ‖θ‖₁)`. Now `⟪z,θ⟫=‖θ‖₁` (`l1_subgradient_iff` ←direction on hsub)
  and `⟪z,β⟫ ≤ ‖β‖₁` (`inner_le_l1Norm_of_linfNorm_le_one`), so both summands `≥ 0`.
- `pdw_every_minimizer_supported` (Lemma 7.23b): `θ̃` optimal and `θ̂` optimal ⇒ equal objective.
  From `hkkt`: `λ•zhat = −(1/n)•designMap Xᵀ(Xθ̂−Y)`. Apply `loss_convex_gradient X Y θ̂ θ̃`:
  `g(θ̃) ≥ g(θ̂) + ⟪(1/n)Xᵀ(Xθ̂−Y), θ̃−θ̂⟫ = g(θ̂) − λ⟪zhat, θ̃−θ̂⟫`. Optimality of both:
  `g(θ̃)+λ‖θ̃‖₁ = g(θ̂)+λ‖θ̂‖₁`. Combine ⇒ `λ‖θ̃‖₁ ≤ λ⟪zhat,θ̃⟫ − λ⟪zhat,θ̂⟫ + λ‖θ̂‖₁`; with
  `⟪zhat,θ̂⟫ = ‖θ̂‖₁` (`l1_subgradient_iff` on hsub) ⇒ `‖θ̃‖₁ ≤ ⟪zhat,θ̃⟫`. But `⟪zhat,θ̃⟫ ≤ ‖θ̃‖₁`
  (`inner_le_l1Norm_of_linfNorm_le_one`, `linfNorm zhat ≤ 1` from hsub). So `⟪zhat,θ̃⟫ = ‖θ̃‖₁`, i.e.
  `∑(|θ̃ⱼ| − zhatⱼθ̃ⱼ)=0`, each term `≥0` ⇒ `zhatⱼθ̃ⱼ = |θ̃ⱼ|` ∀j. For `j∉S`, `|zhatⱼ|<1` (hstrict)
  forces `θ̃ⱼ=0` (since `zⱼθⱼ=|θⱼ|` with `|zⱼ|<1` ⇒ `θⱼ=0`).
- `pdw_unique` (Lemma 7.23a): existence from `lasso_minimizer_exists`. Uniqueness: any two minimizers
  `θ₁,θ₂` are supported on `S` (`pdw_every_minimizer_supported`). Strict convexity on `S`: the loss
  difference along `Δ=θ₁−θ₂` (supported on S) is `(1/2n)‖XΔ‖² = (1/2n)‖designSub X S (Δ|↥S)‖² ≥
  (cmin/2)‖Δ|↥S‖²` (`hA3`,`designMap_restrict_eq_designSub`, `restrict_eq_self`). If `θ₁≠θ₂` this is
  `>0`, contradicting that the midpoint `(θ₁+θ₂)/2` would have strictly smaller objective than the
  common minimum (convexity of `l1Norm` + strict drop in the quadratic). Conclude `θ₁=θ₂`.

# REQUIREMENTS
ZERO sorry. Keep the 7 signatures + tags. Add `private` helpers in THIS file only. Do not touch other
files, the umbrella, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`.

# TOUCH-SET: ONLY  StatLean/HighDimensionalStatistics/Lasso/SupportRecovery/Subgradient.lean
# BUILD: lake build StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Subgradient
# DONE = build exits 0; 0 sorries; commit (`sr(subgrad): ℓ¹ subgradient + Lemma 7.23 (Wainwright §7.5)`).
  Report build status, sorry count, helpers added, and any step that needed a different argument than above.
