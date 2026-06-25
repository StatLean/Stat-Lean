# Lasso support recovery — status (Batch 5)

Integration branch: `hds/lasso-support-recovery` (off `main` @ `a6a1a26`).
Reference: Wainwright §7.5 — Theorem 7.21, Corollary 7.22. See `outline.md` for the full
interface contract (signatures + sub-lemma tables + DAG).

**State: ✅ COMPLETE — Batch 5 fully proved, 0-sorry, verified.**
All 7 units merged into `hds/lasso-support-recovery`. Full HDS umbrella build green:
`Build completed successfully (3113 jobs)`, exit 0, **0 sorries** across all of
HighDimensionalStatistics (no regressions). **Axiom audit:** all five main theorems
(`lasso_support_recovery_{unique,no_false_inclusion,linf,no_false_exclusion}`,
`lasso_support_recovery_subgaussian`) depend only on `[propext, Classical.choice, Quot.sound]` —
**no `sorryAx`**. (History: foundation gate 2336 jobs; full assembly stub-gate 2877 jobs / 28
sorries; closed via 7 cluster proof subagents across 4 waves.)

## Unit ledger

| Unit | Branch | File | Lemmas | Status |
|---|---|---|---|---|
| F1 | `hds/sr-submatrix` | `ForMathlib/SupportSubmatrix.lean` | 7 | ✅ real (merged, verified) |
| F2 | `hds/sr-gram` | `ForMathlib/GramMatrix.lean` | 10 | ✅ real (merged, verified) |
| C0 | (laptop) | `Lasso/SupportRecovery/Defs.lean` | defs | ✅ real |
| A1 | `hds/sr-subgrad` | `Lasso/SupportRecovery/Subgradient.lean` | 8 | ✅ real (merged, verified) |
| A2 | `hds/sr-dualcert` | `Lasso/SupportRecovery/DualCertificate.lean` | 1 (+helpers) | ✅ real (merged, verified) |
| A3 | `hds/sr-thm721` | `Lasso/SupportRecovery/DeterministicGuarantee.lean` | 4 | ✅ real (merged, verified) |
| A4 | `hds/sr-cor722` | `Lasso/SupportRecovery/SubGaussianNoise.lean` | 1 (+helpers) | ✅ real (merged, verified) |

**Book-vs-Lean constants (final, all provable as stated):**
| Result | Book | Lean (proved) | Note |
|---|---|---|---|
| λ lower constant (7.44) | `2/(1−α)` | `2/(1−α)` | exact |
| strict feasibility | `½(1+α)<1` | `½(1+α)<1` | exact (needs `α<1`) |
| Cor 7.22 prob (7.47) | `1−4e^{−nδ²/2}` | `1−4e^{−nδ²/2}` | **exact** (2 over `d−s` + 2 over `s`) |
| (A3) form | `γ_min(XₛᵀXₛ/n)≥cmin` | quadratic-form (≡) | Courant–Fischer |

**Accepted deviations (tagged in code):** A1 added `USER-INPUT: 0 < λ` to `pdw_unique` /
`pdw_every_minimizer_supported` (false without it). A2 realized the oracle via a `zeroOffCols`
device (reuses A1, avoids `↥S` re-index) and its steps 4–9 as named `have`s. No signature drift in
the 5 main theorems; no constant weakened vs the book.

**Waves 1–2 landed (verified):** F1, A1, F2 merged into `hds/lasso-support-recovery`; the
`Subgradient` target builds green 0-sorry on the integration branch (covers F1+F2+C0+A1).
**Deviation accepted:** A1 added a tagged `USER-INPUT: 0 < λ` to `pdw_unique` /
`pdw_every_minimizer_supported` (false without it; Wainwright assumes λ>0). A3 supplies via `hlampos`
(prompt `sr-thm721.md` updated). **Cluster note:** primary-worktree verify builds intermittently hit a
transient networked-FS `ENOENT`; re-run clears it (code is fine — subagent fresh-worktree builds were green).

Legend: ⬜ stub · 🟡 stub-gated green-with-sorries · 🔵 proof in progress (cluster) · ✅ real (0-sorry, verified at laptop gate).

## Proof-wave schedule (cluster `lean-fasrc-cluster-claude`, prompts `.claude/prompts/sr-*.md`)

Each unit's prover builds on **statements** of its deps (stable, frozen) — F2/A2/A4 trust upstream
lemma signatures even while those are still sorried, and each closes only its own file's sorries.

- **Wave 1:** F1 (`hds/sr-submatrix`) + A1 (`hds/sr-subgrad`) — concurrent, file-disjoint.
- **Wave 2:** F2 (`hds/sr-gram`) — after F1 merged (F2 proofs lean on F1 identities).
- **Wave 3:** A2 (`hds/sr-dualcert`) — the crux, after F1+F2 merged.
- **Wave 4:** A3 (`hds/sr-thm721`) + A4 (`hds/sr-cor722`) — after A1+A2 (+F2) merged; A3 frozen sigs.
- **Final:** merge integration branch → main; full `lean-fasrc-build`; `#print axioms`; status update.

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
