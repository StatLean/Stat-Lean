Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "..."` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`. Build with plain `lake build`, ITERATE to 0 errors / 0 sorries. Lift sub-steps to proven `private` helpers IN THIS FILE; never fabricate.

# CONTEXT (this is a RE-ATTEMPT with a corrected, simpler strategy)
File: `StatLean/Minimaxity/Examples/PCA.lean`. The crux `pca_fano_config` (spiked-covariance PCA, Ex 15.19)
is the sole `sorry`. A prior feasibility pass established TWO obstructions to the ORIGINAL statement and the
fix; APPLY the fixes (both are pre-authorized: minimal forced hypothesis + loose constant per CLAUDE.md §1):

* **(O1) Fano needs many hypotheses ⇒ large d.** For small `d` the construction gives `mutualInformation = 0`
  / too-small `log M`, so the Fano bracket can't beat a positive RHS. ADD a forced hypothesis `(hd0 : d₀ ≤ d)`
  to BOTH `pca_fano_config` AND `pca_minimax_rate` (replace/augment `hd : 1 ≤ d`), with `d₀` the concrete
  threshold your bound needs (pick it from the arithmetic, e.g. `d ≥ 32`), tagged
  `-- LEAN-ONLY: d ≥ d₀ — Fano's method needs e^{Ω(d)} hypotheses; the small-d regime is a separate two-point bound. Wainwright Ex 15.19 is a large-d rate.`
* **(O2) loose constant.** `exists_sphere_packing` certifies only `log M ≥ (d-1)/10`, so the book's `128⁻¹`
  is unreachable by a factor ≈2.5–5. LOOSEN the constant in BOTH the crux RHS and `pca_minimax_rate` from
  `128⁻¹` to the provable value you achieve (e.g. `512⁻¹` or `1024⁻¹`), tagged
  `-- USER-INPUT: constant loosened from book 128⁻¹ to the value provable from the n/10 sphere-packing brick (Wainwright Ex 15.19; CLAUDE.md §1).`
  Keep the `min(…, 1)` and the `(1+ν)/ν²·(d/n)` shape.

# THE SIMPLE ROUTE (pairwise convexity — NO #24/blockdiag/symmetric-packing needed)
Use the PUBLIC convexity MI bound, not the max-entropy lemma:
`mutualInformation_le_avg_pairwise_kl` (`Fano/MutualInformation.lean`): `I(Z;J) ≤ M⁻² ∑ⱼₖ klDiv (Q j)(Q k)`.
1. **Construction (tilt; symmetry NOT needed here).** `v_a` = a 1/2-packing of the unit sphere of `e₀^⊥`
   from `exists_sphere_packing (d-1)` (`log M ≥ (d-1)/10`, `‖v_a‖=1`, pairwise `≥1/2`). `θ_a := √(1-δ²)·e₀ + δ·v_a`
   (unit norm ⇒ on the sphere). Separation `‖θ_a-θ_b‖ = δ‖v_a-v_b‖ ≥ δ/2`, so `IsSeparatedFamily` with `δ_sep = δ/4`.
   Pick `δ² := min((1+ν)/ν² · (d/n) · κ, 1)` with `κ` the small constant from the arithmetic.
2. **Spiked det + pairwise KL (Sherman–Morrison).** `S_a := 1 + ν·vecMulVec θ_a θ_a`, `det S_a = 1+ν` (`det_add_mul`,
   `‖θ_a‖=1`); PosDef. Single-sample `klDiv (𝒩 0 S_a)(𝒩 0 S_b) = ½·ν²(1 − ⟨θ_a,θ_b⟩²)/(1+ν)` — derive from the
   PUBLIC `klDiv_multivariateGaussian_zero` (`ForMathlib/GaussianKLMulti.lean`) + Sherman–Morrison for `S_b⁻¹`
   and `det`, log-det terms cancel (`det S_a = det S_b = 1+ν`).
3. **n-fold.** `P θ = (𝒩 0 S_θ)^{⊗n} = Measure.pi`; `klDiv_pi_eq_nsmul` ⇒ `klDiv (P θ_a)(P θ_b) = n • (single)`.
4. **MI bound.** `I ≤ M⁻² ∑ₐᵦ n·½ν²(1−⟨θ_a,θ_b⟩²)/(1+ν)`. With the tilt, `1−⟨θ_a,θ_b⟩² ≤ 2(1−⟨θ_a,θ_b⟩) = 2δ²(1−⟨v_a,v_b⟩) ≤ 4δ²`,
   so `∑ₐᵦ(…) ≤ M²·4δ²` (NO `v̄=0`/symmetry needed — the bare bound `≤4δ²` per pair suffices). Hence `I ≤ 2nν²δ²/(1+ν)`.
5. **Fano.** `log M ≥ (d-1)/10`; with `δ²` as above and `d ≥ d₀`, `I + log2 ≤ ½ log M`, so the bracket
   `(1 − (I+log2)/log M) ≥ ½`. Then `δ_sep²·½ = δ²/32 ≥ (loose const)·min((1+ν)/ν²·d/n, 1)`. Conclude.

# REQUIREMENTS
ZERO sorry. Apply the (O1)+(O2) signature changes to BOTH `pca_fano_config` and `pca_minimax_rate` (tagged).
Helpers `private`, THIS file only. Add imports (`...GaussianKLMulti`, matrix). Do NOT touch
`StatLean/Minimaxity.lean`, `lakefile`, `lean-toolchain`, `lake-manifest.json`, `Defs.lean`, `Fano/`,
`GaussianKLMulti.lean`, `GaussianMaxEntropy.lean`, `SpherePacking.lean`, other `Examples/`.

# TOUCH-SET: ONLY  StatLean/Minimaxity/Examples/PCA.lean
# BUILD: lake build StatLean.Minimaxity.Examples.PCA
# DONE = build exits 0 AND no sorry in the file.
  Commit: `mmx(#23): close pca_fano_config via pairwise-KL Fano (Wainwright Ex 15.19; +d≥d₀, loosened const)`.
  Report: build status, sorry count, the chosen d₀ and constant, the construction, helpers, deviations.
