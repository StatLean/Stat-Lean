# Lasso support recovery — status (Batch 5)

Integration branch: `hds/lasso-support-recovery` (off `main` @ `a6a1a26`).
Reference: Wainwright §7.5 — Theorem 7.21, Corollary 7.22. See `outline.md` for the full
interface contract (signatures + sub-lemma tables + DAG).

**State: SCAFFOLDING (Wave 0).** Stubs being written on laptop; not yet stub-gated on cluster.

## Unit ledger

| Unit | Branch | File | Main decls | Status |
|---|---|---|---|---|
| F1 | `hds/sr-submatrix` | `ForMathlib/SupportSubmatrix.lean` | Xsub, designSub, col + bridges | ⬜ stub |
| F2 | `hds/sr-gram` | `ForMathlib/GramMatrix.lean` | gram, gramInv, projPerp + posDef/inv/norm bounds | ⬜ stub |
| C0 | (laptop) | `Lasso/SupportRecovery/Defs.lean` | LowerEigenvalue, MutualIncoherence, IsL1Subgradient, IsKKT, ColumnNormalized, supportRecoveryBound | ⬜ stub |
| A1 | `hds/sr-subgrad` | `Lasso/SupportRecovery/Subgradient.lean` | l1_subgradient_iff, lasso_minimizer_exists, kkt_of_isLassoEstimator, **Lemma 7.23** (pdw_every_minimizer_supported, pdw_unique) | ⬜ stub |
| A2 | `hds/sr-dualcert` | `Lasso/SupportRecovery/DualCertificate.lean` | oracle_solution, theta_diff_eq, zSc_eq, incoherence_bound, noise_bound, strict_dual_feasibility, linf_error_bound | ⬜ stub |
| A3 | `hds/sr-thm721` | `Lasso/SupportRecovery/Theorem7_21.lean` | **lasso_support_recovery_{unique,no_false_inclusion,linf,no_false_exclusion}** (7.21 a–d) | ⬜ stub |
| A4 | `hds/sr-cor722` | `Lasso/SupportRecovery/Corollary7_22.lean` | **lasso_support_recovery_subgaussian** (Cor 7.22) + concentration lemmas | ⬜ stub |

Legend: ⬜ stub · 🟡 stub-gated green-with-sorries · 🔵 proof in progress (cluster) · ✅ real (0-sorry, verified at laptop gate).

## Expected named sorry debts (per file, pre-proof)

Each `sorry` corresponds to one named lemma in the `outline.md` tables. No anonymous `have … := sorry`.
Verification gate per unit: fresh `lean-fasrc-build --worktree cannon/<branch> <Target>` + sorry
inventory == the table above + `git diff main...cannon/<branch>` (tags, touch-set, no laundering,
no edits to umbrellas/`lean-toolchain`/`lakefile.lean`/`lake-manifest.json`).

## Reuse ledger (do not rebuild)

- `designMap`, `l1Norm`, `linfNorm`, `restrict`, `abs_inner_le_l1Norm_mul_linfNorm`, `l1Norm_split`,
  `restrict_*` (`ForMathlib/VecNorms.lean`, `LinearModel/Defs.lean`).
- `IsLassoEstimator`, `lassoObjective` (`Lasso/Defs.lean`) — Wainwright's Lagrangian Lasso verbatim.
- `IsSubGaussian`, `isSubGaussian_const_mul`, `HasSubgaussianMGF.sum_of_iIndepFun`,
  `measure_abs_sub_integral_lt_le`, **`tail_max_le`** (`ConcentrationInequalities/{SubGaussian,Maximal}/*`).
- `Lasso/RandomNoise.lean` = structural template for A4 (designMap Xᵀ, noiseVec, good-event union bound).

## Mathlib bricks verified present (LeanExplore)

`Matrix.linfty_opNorm_def`, `Matrix.isUnit_iff_isUnit_det`/`nonsingInvUnit`,
`Continuous.exists_forall_le'`, `Matrix.IsHermitian.iInf_eigenvalues_le_dotProduct_mulVec`.

## Book-vs-Lean constants

(see `outline.md`; fill as proved)
