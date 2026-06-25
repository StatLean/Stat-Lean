Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use the search tools and `exact?`. Never `lake update`. Inside an srun allocation — `lake build`, ITERATE to 0 errors / 0 sorries. THIS IS THE HARDEST UNIT (block KKT matrix algebra). Build it as named `private` steps; time-box each; commit progress.

# CONTEXT (do NOT modify other files; all imports below are PROVED by now)
`Lasso/SupportRecovery/DualCertificate.lean` has ONE sorried theorem `pdw_witness_exists`.
Imports give you:
* F1 `SupportSubmatrix`: `Xsub X S`, `designSub`, `col X j`, `Xsub_mulVec`,
  `Xsub_transpose_mulVec_apply`, `designMap_restrict_eq_designSub`, `inner_designMap_transpose`,
  `col_eq_designMap_single`.
* F2 `GramMatrix`: `gram = XₛᵀXₛ`, `gramInv = gram⁻¹`, `projPerp = 1 − Xₛ·gramInv·Xₛᵀ`,
  `matLinftyNorm`, `gram_quadForm`, `gramInv_mulVec_gram`, `gramInv_isHermitian`,
  `norm_gramInv_mulVec_le`, `projPerp_apply_norm_le`, `matLinftyNorm_mulVec_le`,
  `gram_isUnit_det`, and a right-inverse you may add (`gram·gramInv = 1`, `Matrix.mul_nonsing_inv`).
* C0 `Defs`: `MutualIncoherence X S α`, `LowerEigenvalue X S cmin`, `IsL1Subgradient`, `IsKKT`,
  `projNoiseLinf X S w` (= `‖Xₛᶜᵀ Π_{S⊥} w/n‖_∞`), `supportRecoveryBound X S w λ` (= B(λ;X), 7.45),
  `gramInvNorm = ((1/n)•gram)⁻¹` (= `(XₛᵀXₛ/n)⁻¹`; note `gramInvNorm = n•gramInv`).
* A1 `Subgradient`: `l1_subgradient_iff`, `inner_le_l1Norm_of_linfNorm_le_one`, `loss_convex_gradient`,
  `lasso_minimizer_exists`, `kkt_of_isLassoEstimator`.

# GOAL  (Wainwright §7.5.2, the PDW construction + 7.51–7.54)
Produce `θ̂, ẑ` with: `θ̂` supported on S; `ẑ ∈ ∂‖θ̂‖₁`; full KKT (7.48) for `Y = Xθ*+w`;
strict dual feasibility `|ẑ_j|<1` for `j∉S`; and `‖restrict S (θ̂−θ*)‖_∞ ≤ supportRecoveryBound X S w λ`.

# CONSTRUCTION & PROOF (lift each ▸ to a named `private` lemma)
1. **Oracle θ̂.** Take `θ̂` = minimizer of `lassoObjective X Y λ` over `{β | ∀ j∉S, βⱼ=0}` (the
   S-supported subspace). Existence: coercive EVT on the subspace (adapt `lasso_minimizer_exists`,
   restricting to S; or minimize over `EuclideanSpace ℝ ↥S` and zero-extend). Get `hsupp : ∀ j∉S, θ̂ⱼ=0`.
2. **Define ẑ** `:= −(1/(λ*n)) • designMap Xᵀ (designMap X θ̂ − Y)`. Then `IsKKT X Y λ θ̂ ẑ` holds by
   `smul` algebra (`λ>0`, `n>0`): `(1/n)•Xᵀ(Xθ̂−Y) + λ•ẑ = 0`.
3. ▸ **oracle_kkt**: `ẑ` restricted to S is a subgradient of `‖θ̂_S‖₁`, i.e. `∀ j∈S, (θ̂ⱼ>0→ẑⱼ=1) ∧
   (θ̂ⱼ<0→ẑⱼ=−1) ∧ |ẑⱼ|≤1`. Proof: optimality of θ̂ under perturbations `θ̂ ± t•single j 1` with
   `j∈S` (these stay S-supported) — same per-coordinate argument as A1's `kkt_of_isLassoEstimator`.
4. ▸ **theta_diff_eq (7.52)**: using `Y = designMap X θ* + w`, `θ*` supported on S
   (`designMap X θ* = designSub …` via `designMap_restrict_eq_designSub`+`restrict_eq_self`), and the
   S-block of KKT: `(Gₛ/n)·(θ̂_S − θ*_S) = (1/n)Xₛᵀw − λ ẑ_S`, hence (apply `gramInvNorm`,
   `gramInv_mulVec_gram`) `θ̂_S − θ*_S = gramInvNorm·((1/n)Xₛᵀw) − λ·gramInvNorm·ẑ_S`.
5. ▸ **linf_error_bound (7.54)**: `‖restrict S (θ̂−θ*)‖_∞ = ⨆_{i∈S}|θ̂ᵢ−θ*ᵢ| ≤
   ‖gramInvNorm·(1/n)Xₛᵀw‖_∞ + λ·‖gramInvNorm·ẑ_S‖_∞ ≤ (first term of B) + λ·matLinftyNorm(gramInvNorm)·1`
   (`matLinftyNorm_mulVec_le`, `‖ẑ_S‖_∞ ≤ 1` from step 3) `= supportRecoveryBound X S w λ`.
6. ▸ **zSc_eq (7.53)**: for `j∉S`, substitute step 4 into `ẑⱼ = −(1/(λn))Xⱼᵀ(Xθ̂−Y) =
   −(1/(λn))Xⱼᵀ(Xₛ(θ̂_S−θ*_S) − w)` to get `ẑ_{Sᶜ} = μ + V`, with
   `μⱼ = ⟨gramInv·(Xₛᵀ Xⱼ), ẑ_S⟩` and `Vⱼ = Xⱼᵀ (projPerp · (w/(λn)))`.
7. ▸ **incoherence_bound**: `|μⱼ| = |⟨gramInv·(XₛᵀXⱼ), ẑ_S⟩| ≤ (∑_{i∈S}|（gramInv·XₛᵀXⱼ)ᵢ|)·‖ẑ_S‖_∞
   ≤ α·1 = α` (Hölder on ↥S + `MutualIncoherence` (note `XₛᵀXⱼ = Xₛᵀ·(col X j)`, `gramInv` symmetric);
   `‖ẑ_S‖_∞≤1` from step 3).
8. ▸ **noise_bound**: `|Vⱼ| ≤ ‖V‖_∞ = (1/λ)·‖Xₛᶜᵀ projPerp (w/n)‖_∞ = (1/λ)·projNoiseLinf X S w
   ≤ (1/λ)·(λ(1−α)/2) = (1−α)/2`, from `hlam : λ ≥ (2/(1−α))·projNoiseLinf X S w` and `α<1`.
9. ▸ **strict_dual_feasibility**: `|ẑⱼ| ≤ |μⱼ| + |Vⱼ| ≤ α + (1−α)/2 = (1+α)/2 < 1` (needs `α<1`).
10. **IsL1Subgradient ẑ θ̂**: on S from step 3; for `j∉S`, `θ̂ⱼ=0` and `|ẑⱼ|<1≤1` (step 9) ⇒ all three
    clauses hold (the sign clauses are vacuous since `θ̂ⱼ=0`).
Assemble: `exact ⟨θ̂, ẑ, hsupp, (IsL1Subgradient), (IsKKT step 2), (step 9), (step 5)⟩`.

# REQUIREMENTS
ZERO sorry. Keep `pdw_witness_exists`'s signature + all `-- USER-INPUT` tags. Add `private` lemmas
for steps 1,3–9 in THIS file only. Do not touch other files / umbrella / build config. If you must
deviate from a stated identity (e.g. a sign or a `1/n` placement), document it in the commit report.

# TOUCH-SET: ONLY  StatLean/HighDimensionalStatistics/Lasso/SupportRecovery/DualCertificate.lean
# BUILD: lake build StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.DualCertificate
# DONE = build exits 0; 0 sorries; commit (`sr(dualcert): primal-dual witness + strict feasibility (Wainwright §7.5.2)`).
  Report build status, sorry count, the named private steps, and ANY deviation from the roadmap above.
