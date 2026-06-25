# Close the 5 sorries in MEstimator/Bound.lean (Wainwright Lemma 9.21, Theorem 9.19, Corollary 9.20)

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON the
cluster — iterate with plain `lake build StatLean.HighDimensionalStatistics.MEstimator.Bound` (no `srun`).

## Hard constraints
- **Only edit** `StatLean/HighDimensionalStatistics/MEstimator/Bound.lean`. Touch nothing else (NOT
  `Defs.lean` — the constants there are fixed and provable; NOT `Deviation.lean`/`SubspaceLip.lean`).
- Goal **0 sorries**, 0 errors. Keep signatures, USER-INPUT tags, docstrings, constants UNCHANGED.
  Lines ≤ 100. If a piece resists, lift to a `private lemma` with one `sorry` + `-- TODO(me):`.
- After green: `#print axioms mestimator_l2_bound` → only `propext, Classical.choice, Quot.sound`.

## Available API (already proven, use as black boxes)
- `error_mem_cone dr L hL hdiff θstar θhat lam hlam hopt hG : (θhat - θstar) ∈ errorCone dr θstar`
  (Prop 9.13). `errorCone dr θstar = {Δ | dr.Φ ((dr.Mbar)ᗮ.starProjection Δ) ≤ 3*dr.Φ (dr.Mbar.starProjection Δ) + 4*dr.Φ ((dr.M)ᗮ.starProjection θstar)}`.
- `reg_deviation_lower dr θstar Δ` (eq 9.32) and `cost_deviation_lower dr L hL hdiff θstar Δ lam hG` (eq 9.33).
- `subspaceLip_le dr.Φ S (hu : u ∈ S) : dr.Φ u ≤ subspaceLip dr.Φ S * ‖u‖` and
  `subspaceLip_nonneg dr.Φ S : 0 ≤ subspaceLip dr.Φ S`.
- `Submodule.starProjection_apply_mem`, `Submodule.norm_starProjection_apply_le` (‖proj x‖≤‖x‖),
  `Submodule.starProjection_add_starProjection_orthogonal` (`K.proj x + Kᗮ.proj x = x`).
- `Fcal L dr.Φ θstar lam Δ = L (θstar+Δ) - L θstar + lam*(dr.Φ (θstar+Δ) - dr.Φ θstar)` (def).
- `RSC L θstar dr.Φ κ R τSq` unfolds to `∀ Δ, ‖Δ‖≤R → taylorErr L θstar Δ ≥ κ/2*‖Δ‖^2 - τSq*(dr.Φ Δ)^2`,
  and `taylorErr L θstar Δ = L (θstar+Δ) - L θstar - ⟪gradient L θstar, Δ⟫_ℝ`.
- `dr.holder u v : ⟪u,v⟫_ℝ ≤ dr.Φ u * dr.Φstar v`. `GoodEvent dr.Φstar g lam` is `dr.Φstar g ≤ lam/2`.
- Seminorm: `map_add_le_add dr.Φ`, `map_smul_eq_mul`, `apply_nonneg dr.Φ`, `map_zero`,
  `dr.Φ.convexOn : ConvexOn ℝ univ dr.Φ`. `open StatLean.Optimization` (file already does).

## Proofs

### A. `errorCone_smul_mem` (add this `private lemma` first — star-shapedness, needed by Lemma 9.21)
`Δ ∈ errorCone dr θstar → 0 ≤ t → t ≤ 1 → (t • Δ) ∈ errorCone dr θstar`.
Proof: projections are linear (`map_smul` on the CLM `starProjection`), `dr.Φ (t • x) = |t| * dr.Φ x = t * dr.Φ x`
(`map_smul_eq_mul` + `abs_of_nonneg`). From `Δ∈ℂ`: `t*Φ(Δ_{M̄ᗮ}) ≤ t*(3Φ(Δ_{M̄}) + 4Φ₀) = 3*(t*Φ(Δ_{M̄})) + 4*(t*Φ₀) ≤ 3Φ((tΔ)_{M̄}) + 4Φ₀`
(last: `t*Φ₀ ≤ Φ₀` since `t ≤ 1`, `Φ₀ ≥ 0`). `simp [errorCone, Set.mem_setOf_eq]` then `nlinarith`.

### B. `norm_error_le_of_pos_on_sphere` (Lemma 9.21)
Contradiction: `by_contra h; push_neg at h` gives `δ < ‖θhat-θstar‖`. Set `Δ̂ := θhat - θstar`.
- `hmem : Δ̂ ∈ errorCone dr θstar := error_mem_cone …`.
- `hF0 : Fcal L dr.Φ θstar lam Δ̂ ≤ 0`: `θstar + Δ̂ = θhat` (`add_sub_cancel`); unfold `Fcal`; it equals
  `(L θhat + lam*Φ θhat) - (L θstar + lam*Φ θstar) ≤ 0` by `hopt θstar` (`nlinarith`/`linarith`).
- `t := δ / ‖Δ̂‖`. `‖Δ̂‖ > 0` (from `δ < ‖Δ̂‖`, `δ>0`). `ht0 : 0 < t`, `ht1 : t < 1` (since `δ<‖Δ̂‖`).
- `hnorm : ‖t • Δ̂‖ = δ`: `norm_smul`, `Real.norm_eq_abs`, `abs_of_pos ht0`, then `t*‖Δ̂‖ = δ` by `field_simp`.
- `hmemt : (t • Δ̂) ∈ errorCone dr θstar := errorCone_smul_mem hmem ht0.le ht1.le`.
- `hpos' := hpos (t•Δ̂) hmemt hnorm` — gives `0 < Fcal … (t•Δ̂)`.
- Contradiction via `Fcal … (t•Δ̂) ≤ t * Fcal … Δ̂ ≤ 0`: show `θstar + t•Δ̂ = (1-t)•θstar + t•θhat`
  (`Δ̂=θhat-θstar`, `module`/`abel` + smul algebra). Then `L`-convexity
  (`hL.2 (mem_univ _) (mem_univ _) (by linarith) ht0.le (by ring)` giving
  `L((1-t)•θstar+t•θhat) ≤ (1-t)*L θstar + t*L θhat`) and `dr.Φ`-convexity (same shape via `dr.Φ.convexOn.2`).
  Combine into `Fcal … (t•Δ̂) ≤ t * (Fcal … Δ̂)` by `nlinarith`; with `hF0`, `ht0`, that's `≤ 0`, contradicting `hpos'`.

### C. `mestimator_reg_bound` (Thm 9.19(a))
`Δ̂ := θhat-θstar ∈ ℂ` (`error_mem_cone`), so (unfold `errorCone` at the membership)
`Φ(Δ̂_{M̄ᗮ}) ≤ 3Φ(Δ̂_{M̄}) + 4Φ₀`. Then `Φ(Δ̂) ≤ Φ(Δ̂_{M̄})+Φ(Δ̂_{M̄ᗮ})` (rewrite `Δ̂ = Δ̂_{M̄}+Δ̂_{M̄ᗮ}` via
`starProjection_add_starProjection_orthogonal`, `map_add_le_add`) `≤ 4Φ(Δ̂_{M̄})+4Φ₀`. Finally
`Φ(Δ̂_{M̄}) ≤ subspaceLip dr.Φ dr.Mbar * ‖Δ̂_{M̄}‖ ≤ Ψ*‖Δ̂‖` (`subspaceLip_le` with `starProjection_apply_mem`,
then `norm_starProjection_apply_le` + `subspaceLip_nonneg`). `nlinarith`.

### D. `mestimator_l2_bound` (Thm 9.19(b)) — the core. Set
`Ψ := subspaceLip dr.Φ dr.Mbar`, `Φ₀ := dr.Φ ((dr.M)ᗮ.starProjection θstar)`, `c := κ/2 - 32*τSq*Ψ^2`.
- `hΨ0 : 0 ≤ Ψ := subspaceLip_nonneg _ _`. `hΦ0 : 0 ≤ Φ₀ := apply_nonneg _ _`.
- `hc : κ/4 ≤ c`: from `hτ : τSq*Ψ^2 ≤ κ/128`, `32*(τSq*Ψ^2) ≤ κ/4`, so `c = κ/2-32τSqΨ² ≥ κ/4`. `nlinarith`.
- `heps_pos : 0 < epsilonSq …` is NOT always true (if `Ψ=0 ∧ Φ₀=0`). Handle: `rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ epsilonSq …)`. If `epsilonSq = 0`: then `Ψ=0` and `Φ₀=0` (each term 0,
  `κ>0`,`λ>0`); show `‖Δ̂‖ = 0` — apply `norm_error_le_of_pos_on_sphere` is awkward at δ=0, so instead:
  `Δ̂∈ℂ` with `Φ₀=0` gives `Φ(Δ̂_{M̄ᗮ})≤3Φ(Δ̂_{M̄})`, and `Φ(Δ̂_{M̄})≤Ψ‖Δ̂‖=0`, so `Φ(Δ̂)=0`; combine with
  RSC at small radius… this edge case is fiddly — if it resists, lift to `private lemma l2_bound_degenerate`
  with a `sorry` + TODO, and prove the main `epsilonSq > 0` branch. (Generic case `Ψ>0` is the real content.)
- Main branch `0 < epsilonSq`: `δ := Real.sqrt (epsilonSq …)`. `hδ2 : δ^2 = epsilonSq …` (`Real.sq_sqrt heps_pos.le`).
  `hδpos : 0 < δ` (`Real.sqrt_pos.mpr heps_pos`). `hδR : δ ≤ R` (`Real.sqrt_le_… ` from `hεR : epsilonSq ≤ R^2`, `hR`).
  `hδlb : 12*(lam/κ)*Ψ ≤ δ`: from `(12*(lam/κ)*Ψ)^2 = 144*(lam^2/κ^2)*Ψ^2 ≤ epsilonSq = δ^2` and nonneg, `Real.le_sqrt`/`abs_le_of_sq_le_sq`.
  Apply `norm_error_le_of_pos_on_sphere dr L hL hdiff θstar θhat lam hlam hopt hG hδpos ?pos`, then
  `‖Δ̂‖ ≤ δ` ⟹ `‖Δ̂‖^2 ≤ δ^2 = epsilonSq` (`pow_le_pow_left`, `‖·‖≥0`).
  - `?pos`: `intro Δ hΔcone hΔnorm` (`hΔnorm : ‖Δ‖ = δ`). Show `0 < Fcal L dr.Φ θstar lam Δ`. Chain:
    * RSC: `hRSC Δ (hΔnorm ▸ hδR)` → `taylorErr ≥ κ/2*δ^2 - τSq*(dr.Φ Δ)^2` (rewrite `‖Δ‖=δ`).
    * `g := gradient L θstar`. `⟨g,Δ⟩ ≥ -(lam/2)*dr.Φ Δ`: `dr.holder Δ g` + `dr.holder (-Δ) g` (two-sided)
      + `hG` (`dr.Φstar g ≤ lam/2`) + `apply_nonneg`. (Same move as `cost_deviation_lower`.)
    * `reg_deviation_lower dr θstar Δ`.
    * `Φ(Δ_{M̄}) ≤ Ψ*δ` (`subspaceLip_le`+`norm_starProjection_apply_le`, `‖Δ‖=δ`).
    * `Φ(Δ) ≤ 4*Φ(Δ_{M̄}) + 4*Φ₀` (cone membership `hΔcone` + triangle), hence
      `(dr.Φ Δ)^2 ≤ 32*Ψ^2*δ^2 + 32*Φ₀^2` (`nlinarith [sq_nonneg (Φ(Δ_{M̄}) - Φ₀)]` / `(a+b)^2≤2a^2+2b^2`).
    * Assemble: `Fcal … Δ ≥ c*δ^2 - (3*lam/2)*Ψ*δ - (32*τSq*Φ₀^2 + 2*lam*Φ₀)`. Then close with
      **`nlinarith [hc, hδlb, hδ2, hδpos, hΨ0, hΦ0, mul_pos hδpos hδpos, mul_nonneg hΨ0 hδpos.le, ...]`**.
      The certificate (split `c*δ^2` in half): `(1/2)c*δ^2 - (3lam/2)Ψδ ≥ 0` (uses `δ ≥ 12(λ/κ)Ψ`, `c≥κ/4`:
      `(1/2)cδ ≥ (1/2)(κ/4)·12(λ/κ)Ψ = (3/2)λΨ`) and `(1/2)c*δ^2 - (32τSqΦ₀²+2λΦ₀) > 0` (uses `δ^2 = epsilonSq ≥ (32/κ)(λΦ₀+16τSqΦ₀²)`,
      `c≥κ/4`, `δ>0`). Give nlinarith these as explicit product hints if it doesn't close directly:
      `mul_le_mul hc (le_refl ..) …`, `mul_nonneg`, `sq_nonneg`.

### E. `cor_l2_bound_of_mem` (Cor 9.20, eq 9.49b)
`θ*∈M ⟹ (dr.M)ᗮ.starProjection θstar = 0` (find lemma: `v∈K → Kᗮ.starProjection v = 0`; try `exact?`,
likely `Submodule.starProjection_orthogonal_eq_zero`/`starProjection_apply_eq_zero_of_mem` or via
`Submodule.starProjection_eq_zero_iff` + `mem` and `K ≤ (Kᗮ)ᗮ`). Then `Φ₀ = dr.Φ 0 = 0` (`map_zero`),
so `epsilonSq dr θstar lam κ τSq = 144*(lam^2/κ^2)*Ψ^2` (`simp [epsilonSq, this, map_zero]`). Conclude
by `mestimator_l2_bound … hτ ?hεR'` where `?hεR'` reuses `hεR` rewritten with `Φ₀=0`. `rw`/`simpa`.

### F. `cor_reg_bound_of_mem` (Cor 9.20, eq 9.49a)
`mestimator_reg_bound` gives `Φ(Δ̂) ≤ 4*(Ψ*‖Δ̂‖ + Φ₀)`; `Φ₀=0` (as in E) ⟹ `Φ(Δ̂) ≤ 4Ψ‖Δ̂‖`.
`cor_l2_bound_of_mem` gives `‖Δ̂‖^2 ≤ 144*(lam^2/κ^2)*Ψ^2`, so `‖Δ̂‖ ≤ 12*(lam/κ)*Ψ` (`abs_le_of_sq_le_sq`/
`Real.sqrt`, `‖·‖≥0`, `Ψ≥0`, `lam,κ>0`). Then `Φ(Δ̂) ≤ 4Ψ·12(λ/κ)Ψ = 48(λ/κ)Ψ^2` (`nlinarith [hΨ0]`).

Report final `lake build` status + `#print axioms` for the 5 results (note any lifted `private` sorry).
