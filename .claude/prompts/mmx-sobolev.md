Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "natural-language query"` (semantic) — over loogle (user preference); use `./tools/check.sh '<exact.name>'` / `./tools/api.sh <file>` for exact names/signatures, `#leansearch "..."` in a scratch file as backup. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors and 0 sorries in the target file.

# CONTEXT
File: `StatLean/Minimaxity/ForMathlib/Packing/SobolevEntropy.lean` (namespace `StatLean.Minimaxity`).
One `sorry`, in the existential crux `sobolev_packing_lower_bound_aux` (delegated to by the public
`sobolev_packing_lower_bound`). Current statement (the LOWER packing bound for the Sobolev ellipsoid
`ℰ_α = {θ ∈ ℓ²(ℕ) : Σⱼ ((j+1)^{2α}) θⱼ² ≤ 1}`, Wainwright Example 5.12):

```
∃ (c : ℝ) (_ : 0 < c) (T : Finset (lp (fun _ : ℕ => ℝ) 2)),
  c * (1 / δ) ^ (1 / α) ≤ Real.log T.card ∧
  (∀ x ∈ T, ∑' j : ℕ, ((j : ℝ) + 1) ^ (2 * α) * (x j) ^ 2 ≤ 1) ∧
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ ‖x - y‖
```

# STATEMENT REPAIR (REQUIRED — the lemma is FALSE for large δ; the ellipsoid has ℓ²-diameter ≤ 2)
Add a hypothesis `(hδ2 : δ ≤ 1 / 2)` to BOTH `sobolev_packing_lower_bound_aux` AND
`sobolev_packing_lower_bound`, with the tag
`-- LEAN-ONLY: δ ≤ 1/2 (small-scale regime; the ellipsoid has ℓ²-diameter ≤ 2 so no δ-separated pair exists for large δ); the metric-entropy rate is a δ→0 statement (Wainwright Ex 5.12).`
Keep everything else (names, conclusion, `c` existential) unchanged. The public theorem keeps delegating
to the aux lemma (pass `hδ2` through).

# REUSE (this is the key — do NOT build metric entropy from scratch)
`exists_sphere_packing (k : ℕ) : ∃ T : Finset (EuclideanSpace ℝ (Fin k)), (k/10 : ℝ) ≤ Real.log T.card ∧
  (∀ v ∈ T, ‖v‖ = 1) ∧ ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1/2 : ℝ) ≤ ‖u - v‖`
is CLOSED in `StatLean/Minimaxity/ForMathlib/Packing/SpherePacking.lean` — `import` it.

# CONSTRUCTION (volume-ratio packing via the closed sphere packing — Wainwright Ex 5.12 lower bound)
Let `k : ℕ := ⌊(1/(2δ))^(1/α)⌋`. Since `0 < δ ≤ 1/2` and `α > 1/2`, `(1/(2δ))^(1/α) ≥ 1`, so `k ≥ 1`.
Take the sphere packing `S ⊆ EuclideanSpace ℝ (Fin k)` from `exists_sphere_packing k`
(`log|S| ≥ k/10`, unit-norm, pairwise `≥ 1/2`-separated). Set `ρ := (k : ℝ)^(-α)`.
Embed each `v : EuclideanSpace ℝ (Fin k)` into `lp (fun _ : ℕ => ℝ) 2` by the finitely-supported
sequence `emb v : ℕ → ℝ := fun j => if h : j < k then ρ * v ⟨j, h⟩ else 0` (it has finite support ⇒
`Memℓp`; build the `lp` element via `lp.single`/`Finset.sum` of `lp.single`, or `Memℓp.toLp`).
Let `T := S.image emb` (`emb` injective on `S` since `ρ ≠ 0`).
* **Norm preserved**: `‖emb v‖ = ρ * ‖v‖ = ρ` (for `‖v‖ = 1`); and `‖emb u - emb v‖ = ρ * ‖u - v‖`.
* **Ellipsoid membership**: `∑' j, ((j+1)^{2α}) (emb v j)² = ρ² Σ_{j<k} ((j+1)^{2α}) v_j²
  ≤ ρ² k^{2α} Σ_{j<k} v_j² = ρ² k^{2α} ‖v‖² = ρ² k^{2α} = 1`
  (use `(j+1)^{2α} ≤ k^{2α}` for `j ≤ k-1` since `2α > 0`; the tsum is a finite sum since `emb v` is
  supported on `j < k`; `ρ² k^{2α} = k^{-2α} k^{2α} = 1`).
* **Separation**: `‖emb u - emb v‖ = ρ ‖u - v‖ ≥ ρ · (1/2) = k^{-α}/2 ≥ δ` (because
  `k ≤ (1/(2δ))^{1/α} ⟹ k^α ≤ 1/(2δ) ⟹ k^{-α} ≥ 2δ`).
* **Cardinality**: `log|T| = log|S| ≥ k/10 > 0`. Choose `c := (k/10) / ((1/δ)^(1/α))` (`> 0` since `k ≥ 1`,
  `δ > 0`); then `c * (1/δ)^(1/α) = k/10 ≤ log|T|`. (c may depend on δ — the statement allows it.)

Watch the `lp`/`tsum` plumbing: `‖·‖` on `lp _ 2`, `lp.norm_eq_tsum_rpow` / `Memℓp` of finite support,
`tsum` over a finitely-supported function `= Finset.sum`. Find exact lemma names via
`./tools/explore.sh "norm of lp single"` / `"tsum of finitely supported function"` /
`"Memℓp finite support"` / `"real rpow"` (LeanExplore; preferred). Lift fiddly steps to `private`
helpers IN THIS FILE.

# REQUIREMENTS
ZERO sorry in the file. Keep the public theorem name/conclusion; only the added `hδ2` hypothesis (tagged)
changes signatures. Helpers `private`, in THIS file only. Do NOT edit other files except adding the
`import StatLean.Minimaxity.ForMathlib.Packing.SpherePacking`. Do NOT touch `StatLean/Minimaxity.lean`,
`lakefile`, `lean-toolchain`, `lake-manifest.json`, `Defs.lean`, or `Fano/`/`SparsePacking.lean`.

# TOUCH-SET: ONLY  StatLean/Minimaxity/ForMathlib/Packing/SobolevEntropy.lean
# BUILD: lake build StatLean.Minimaxity.ForMathlib.Packing.SobolevEntropy
# DONE = build exits 0 AND grep finds no sorry in the file.
  Commit: `mmx(#25): close sobolev_packing_lower_bound via sphere-packing embedding (Wainwright Ex 5.12; +δ≤1/2)`.
  Report: build status, final sorry count, the added hypothesis, helpers added.
