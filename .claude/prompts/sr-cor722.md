Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. Use search tools/`exact?`. Never `lake update`. Inside an srun allocation — `lake build`, ITERATE to 0 errors / 0 sorries. Build named `private` lemmas; time-box.

# TEMPLATE TO COPY
**Study `StatLean/HighDimensionalStatistics/Lasso/RandomNoise.lean` first** — it is the structural
blueprint (good-event decomposition, per-coordinate sub-Gaussian via `isSubGaussian_const_mul` +
`HasSubgaussianMGF.sum_of_iIndepFun`, union-bound tail, `ENNReal.ofReal (1−δ) ≤ μ {good}`). Mirror it.

# CONTEXT (do NOT modify other files; all imports PROVED by now)
`Lasso/SupportRecovery/Corollary7_22.lean` has ONE sorried theorem `lasso_support_recovery_subgaussian`.
`noiseVec ω := WithLp.toLp 2 (fun i => w i ω) : E^n`; `Y ω = designMap X θstar + noiseVec ω`.
Available:
* `ConcentrationInequalities`: `IsSubGaussian`, `isSubGaussian_const_mul`,
  `HasSubgaussianMGF.sum_of_iIndepFun`, `IsSubGaussian.measure_abs_sub_integral_lt_le`,
  `tail_max_le` (`μ{ω | t < ⨆ j, X j ω} ≤ ENNReal.ofReal (m·exp(−t²/(2σ²)))`, needs `[NeZero m]`).
* F2: `projPerp_apply_norm_le` (‖Π u‖≤‖u‖), `norm_gramInv_mulVec_le` (‖gramInv·u‖≤(1/(cmin·n))‖u‖),
  `matLinftyNorm`, `gramInvNorm`.
* C0: `projNoiseLinf X S w` (= ‖Xₛᶜᵀ Π w/n‖_∞), `supportRecoveryBound X S w lam` (= B(λ;X)),
  `ColumnNormalized X C`.
* A3 `Theorem7_21`: `lasso_support_recovery_no_false_inclusion`, `lasso_support_recovery_linf`.

# GOAL
`ENNReal.ofReal (1 − 4·exp(−nδ²/2)) ≤ μ {ω | (∀ j∉S, (βhatω)ⱼ=0) ∧ linfNorm(restrict S (βhatω−θstar))
 ≤ (σ/√cmin)(√(2log s/n)+δ) + matLinftyNorm(gramInvNorm X S)·lam}` where `σ = √σ2`, `s = S.card`.

# PROOF ROADMAP (lift ▸ to named `private` lemmas)
Let `m_Sᶜ = d − s = (Sᶜ).card`, `s = S.card`.
1. ▸ **proj_col_subGaussian**: for `j∈Sᶜ`, `Zⱼ ω := (1/n)·⟪col X j, WithLp.toLp 2 (projPerp X S ·ᵥ
   noiseVec ω .ofLp)⟫` is sub-Gaussian with proxy `≤ C²σ2/n`. It is a linear functional
   `∑ᵢ aᵢ (w i ω)` of the independent noise (expand `projPerp·noiseVec` coordinatewise, `projPerp`
   symmetric so `⟪col X j, Π v⟫ = ⟪Π (col X j), v⟫`); proxy `= ‖Π(col X j)‖²σ2/n² ≤ ‖col X j‖²σ2/n²
   ≤ C²σ2/n` (`projPerp_apply_norm_le`, `ColumnNormalized`). Build sub-Gaussianity exactly as
   `RandomNoise.colInner_isSubGaussian` (scale + `sum_of_iIndepFun` + proxy monotonicity).
2. ▸ **gramInv_coord_subGaussian**: for `i∈S`, `Z̃ᵢ ω := eᵢᵀ·(gramInvNorm X S ·ᵥ Xₛᵀ (noiseVec ω/n))`
   is sub-Gaussian with proxy `≤ σ2/(cmin·n)` (linear functional of noise; bound via
   `norm_gramInv_mulVec_le`, i.e. row `i` of `(Gₛ/n)⁻¹Xₛᵀ/n` has ℓ² norm `≤ √(1/(cmin n))`).
3. ▸ **lambda_event** (good event G1): set `t = C·√σ2·(√(2log(↑m_Sᶜ)/n)+δ)`. By `tail_max_le`
   (two-sided, over `Sᶜ`; `[NeZero m_Sᶜ]` from `hsd`) `μ{projNoiseLinf X S (noiseVecω) > t} ≤
   2·m_Sᶜ·exp(−nt²/(2C²σ2))`. With `(a+b)²≥a²+b²`: `nt²/(2C²σ2) ≥ log(m_Sᶜ)+nδ²/2`, so this `≤
   2·exp(−nδ²/2)`. With the (7.46) `hlam`, `projNoiseLinf ≤ t ⇒ lam ≥ (2/(1−α))·projNoiseLinf`
   (the (7.44) condition).
4. ▸ **linf_event** (good event G2): set `t' = (√σ2/√cmin)(√(2log(↑s)/n)+δ)`; by `tail_max_le`
   over `S` (`[NeZero s]` from `hs`): `μ{first-term-of-B > t'} ≤ 2·exp(−nδ²/2)`. The "first term of B"
   is `supportRecoveryBound`'s `⨆_{i∈S}` term.
5. **Union**: `μ(G1ᶜ ∪ G2ᶜ) ≤ 4·exp(−nδ²/2)`, so `μ(G1∩G2) ≥ 1 − 4·exp(−nδ²/2)` (mirror RandomNoise
   Steps 4–5, `measure_union_le`, `measure_compl`, `ENNReal.ofReal_sub`).
6. **On G1∩G2 apply Theorem 7.21**: G1 gives (7.44) ⇒ with `hLasso ω`,
   `lasso_support_recovery_no_false_inclusion` ⇒ `∀j∉S,(βhatω)ⱼ=0`, and
   `lasso_support_recovery_linf` ⇒ `linfNorm(restrict S (βhatω−θstar)) ≤ supportRecoveryBound X S
   (noiseVecω) lam`. On G2 the first term of `supportRecoveryBound` is `≤ t'`, so the whole bound is
   `≤ t' + matLinftyNorm(gramInvNorm)·lam` = the GOAL RHS. Hence `G1∩G2 ⊆ {good}`; `measure_mono`.
   (You may assume `hσ2 : 0<σ2`; the proxy/`tail_max_le` need it.)

# REQUIREMENTS
ZERO sorry. Keep `lasso_support_recovery_subgaussian`'s signature + all tags. Add `private` lemmas in
THIS file only. Do not touch other files / umbrella / build config. If a constant must change
(e.g. `4` → larger, or the `(a+b)²≥a²+b²` step needs adjusting), document it in the report and in a
docstring `Deviation:` note (book constant vs provable).

# TOUCH-SET: ONLY  StatLean/HighDimensionalStatistics/Lasso/SupportRecovery/Corollary7_22.lean
# BUILD: lake build StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Corollary7_22
# DONE = build exits 0; 0 sorries; commit (`sr(cor722): support recovery under sub-Gaussian noise (Wainwright §7.5)`).
  Report build status, sorry count, named private lemmas, and any constant deviation from `4·exp(−nδ²/2)`.
