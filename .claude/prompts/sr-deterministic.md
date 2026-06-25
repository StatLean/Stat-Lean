Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use search tools/`exact?`. Never `lake update`. Inside an srun allocation — `lake build`, ITERATE to 0 errors / 0 sorries. This is pure assembly (wiring A1 + A2); should be short.

# CONTEXT (do NOT modify other files; all imports PROVED by now)
`Lasso/SupportRecovery/DeterministicGuarantee.lean` has 4 sorried theorems (parts a–d of Wainwright 7.21).
All share hypotheses: `hn:0<n`, `hsupp:∀j∉S,θstarⱼ=0`, `hA3:LowerEigenvalue X S cmin`, `hcmin:0<cmin`,
`hA4:MutualIncoherence X S α`, `hα0:0≤α`, `hα1:α<1`, `hlampos:0<lam`,
`hlam: lam ≥ (2/(1−α))*projNoiseLinf X S w`; with `Y = designMap X θstar + w`.
Available:
* A2 `pdw_witness_exists X S θstar w lam α cmin hn hsupp hA3 hcmin hA4 hα0 hα1 hlampos hlam :
  ∃ θ̂ ẑ, (∀j∉S,θ̂ⱼ=0) ∧ IsL1Subgradient ẑ θ̂ ∧ IsKKT X Y lam θ̂ ẑ ∧ (∀j∉S,|ẑⱼ|<1) ∧
  linfNorm (restrict S (θ̂−θstar)) ≤ supportRecoveryBound X S w lam`.
* A1 `pdw_unique`, `pdw_every_minimizer_supported`, `lassoEstimator_of_kkt`.
  **NOTE:** both PDW lemmas take `hlam : 0 < lam` as their FIRST hypothesis (after the explicit
  args, before `hn`) — supply `hlampos`. Exact hypothesis order:
  `pdw_unique X Y S lam cmin θ̂ ẑ  hlam hn hsupp hsub hkkt hstrict hA3 hcmin`;
  `pdw_every_minimizer_supported X Y S lam θ̂ ẑ θtil  hlam hn hsupp hsub hkkt hstrict hopt`.
* `ForMathlib/VecNorms.lean`: `abs_le_linfNorm`, `restrict_ofLp_apply`.

# TASK
Close all 4 sorries to 0-sorry. Keep signatures + `-- USER-INPUT` tags verbatim.

# PROOFS
- (a) `lasso_support_recovery_unique`: `obtain ⟨θ̂,ẑ,hsp,hsub,hkkt,hstrict,_⟩ := pdw_witness_exists …`;
  `exact pdw_unique X (designMap X θstar + w) S lam cmin θ̂ ẑ hlampos hn hsp hsub hkkt hstrict hA3 hcmin`.
- (b) `lasso_support_recovery_no_false_inclusion`: `obtain ⟨θ̂,ẑ,hsp,hsub,hkkt,hstrict,_⟩ := …`;
  `exact pdw_every_minimizer_supported X (designMap X θstar + w) S lam θ̂ ẑ βhat hlampos hn hsp hsub hkkt hstrict hopt`.
- (c) `lasso_support_recovery_linf`: `obtain ⟨θ̂,ẑ,hsp,hsub,hkkt,hstrict,hbound⟩ := …`;
  `have hθ̂min := lassoEstimator_of_kkt X (designMap X θstar + w) lam θ̂ ẑ hn hlampos hsub hkkt`;
  `have huniq := pdw_unique … ` (as in (a)); `have : βhat = θ̂ := huniq.unique hopt hθ̂min`;
  `rw [this]; exact hbound`. (`ExistsUnique.unique`.)
- (d) `lasso_support_recovery_no_false_exclusion`: from (c), `linfNorm (restrict S (βhat−θstar)) ≤ B`.
  For `i∈S`: `(restrict S (βhat−θstar)).ofLp i = (βhat−θstar).ofLp i` (`restrict_ofLp_apply`, `if_pos`)
  `= βhatᵢ − θstarᵢ`. So `|βhatᵢ − θstarᵢ| ≤ linfNorm (restrict S (βhat−θstar)) ≤ B < |θstarᵢ|`
  (`abs_le_linfNorm`, hbig). If `βhatᵢ = 0` then `|θstarᵢ| = |βhatᵢ − θstarᵢ| < |θstarᵢ|` — contradiction.
  So `βhatᵢ ≠ 0`. (Mind `(βhat−θstar).ofLp i = βhat.ofLp i − θstar.ofLp i` via `WithLp.ofLp_sub`/`PiLp`.)

# REQUIREMENTS
ZERO sorry. Keep the 4 signatures + tags. Add `private` helpers in THIS file only if needed. Do not
touch other files / umbrella / build config.

# TOUCH-SET: ONLY  StatLean/HighDimensionalStatistics/Lasso/SupportRecovery/DeterministicGuarantee.lean
# BUILD: lake build StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.DeterministicGuarantee
# DONE = build exits 0; 0 sorries; commit (`sr(thm721): Theorem 7.21 (a)-(d) assembly (Wainwright §7.5)`).
  Report build status, sorry count, any wiring that needed adjustment.
