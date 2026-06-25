# Lasso support recovery — outline (Batch 5)

**Reference:** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*
(CUP 2019), **§7.5** — Theorem 7.21 (deterministic primal–dual witness), Corollary 7.22
(sub-Gaussian-noise specialization). Tag token in code: `Wainwright §7.5`.
PDFs: `ref/Wainwright/Wainwright_LassoSupportRecovery.pdf`, `…_HDStatistics.pdf` (§7.5.1–7.5.2).

Integration branch: `hds/lasso-support-recovery` off `main`. Area: `HighDimensionalStatistics`.
All declarations in `namespace StatLean.HighDimensionalStatistics`, `open Matrix`,
`open scoped InnerProductSpace`, `variable {n d : ℕ}`. Support subtype `↥S = {x // x ∈ S}`.

## Conventions / encoding decisions

- **Lasso objective is REUSED**: `lassoObjective X Y λ β = (1/2n)‖Y − Xβ‖² + λ·l1Norm β` and
  `IsLassoEstimator X Y λ β̂ = ∀β, lassoObjective β̂ ≤ lassoObjective β` already exist in
  `Lasso/Defs.lean` — identical to Wainwright's Lagrangian Lasso (7.18). Do NOT redefine.
- **Design action / (A3) / noise shell stay in full `Fin d` space** via `designMap`,
  `restrict S` (from `ForMathlib/VecNorms.lean`). The support subtype `↥S` is confined to the
  **Gram matrix, its inverse, incoherence (A4), and the matrix-ℓ∞ bound** — the places that
  genuinely need a square invertible block.
- **(A3) encoding = quadratic form** (user decision), via `designSub` on `↥S`:
  `∀ v, cmin·‖v‖² ≤ (1/n)·‖designSub X S v‖²`, i.e. Rayleigh quotient of `XₛᵀXₛ/n` ≥ `cmin`,
  equivalent to `γ_min ≥ cmin` (Courant–Fischer; cited in docstring).
- Vectors on `↥S` use inline `∑ i, |v.ofLp i|` (ℓ¹) / `⨆ i, |v.ofLp i|` (ℓ∞) or the existing
  `l1Norm`/`linfNorm` generalized; matrix ℓ∞ op-norm `|||A|||_∞` via Mathlib `Matrix.linfty_opNorm`
  (fallback: local `matLinftyNorm A := ⨆ i, ∑ j, |A i j|` if instance friction).

## Definitions (laptop-only; C0 `Lasso/SupportRecovery/Defs.lean`, F1/F2 ForMathlib)

**F1 `ForMathlib/SupportSubmatrix.lean`**
```
def Xsub (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) : Matrix (Fin n) ↥S ℝ
  := X.submatrix id Subtype.val                       -- columns of X indexed by S
noncomputable def designSub (X) (S) : EuclideanSpace ℝ ↥S →ₗ[ℝ] EuclideanSpace ℝ (Fin n)
  := Matrix.toEuclideanLin (Xsub X S)                  -- v ↦ Xₛ v
def col (X : Matrix (Fin n) (Fin d) ℝ) (j : Fin d) : EuclideanSpace ℝ (Fin n)
  := WithLp.toLp 2 (fun i => X i j)                    -- j-th column X_j
```
**F2 `ForMathlib/GramMatrix.lean`**
```
def gram (X) (S) : Matrix ↥S ↥S ℝ := (Xsub X S)ᵀ * (Xsub X S)            -- XₛᵀXₛ
noncomputable def gramInv (X) (S) : Matrix ↥S ↥S ℝ := (gram X S)⁻¹       -- (XₛᵀXₛ)⁻¹
noncomputable def projPerp (X) (S) : Matrix (Fin n) (Fin n) ℝ
  := 1 - (Xsub X S) * (gramInv X S) * (Xsub X S)ᵀ                        -- Π_{S⊥}(X)
```
**C0 `Lasso/SupportRecovery/Defs.lean`**
```
def LowerEigenvalue (X) (S) (cmin : ℝ) : Prop :=                          -- (A3), 7.43a
  ∀ v : EuclideanSpace ℝ ↥S, cmin * ‖v‖^2 ≤ (1/(n:ℝ)) * ‖designSub X S v‖^2
def MutualIncoherence (X) (S) (α : ℝ) : Prop :=                           -- (A4), 7.43b
  ∀ j ∉ S, (∑ i : ↥S, |((gramInv X S).mulVec ((Xsub X S)ᵀ.mulVec (col X j).ofLp)) i|) ≤ α
def IsL1Subgradient (z θ : EuclideanSpace ℝ (Fin d)) : Prop :=            -- ∂‖·‖₁, §7.5.2
  ∀ i, (0 < θ.ofLp i → z.ofLp i = 1) ∧ (θ.ofLp i < 0 → z.ofLp i = -1) ∧ |z.ofLp i| ≤ 1
def IsKKT (X) (Y) (λ : ℝ) (θ z : EuclideanSpace ℝ (Fin d)) : Prop :=      -- 7.48
  (1/(n:ℝ)) • designMap Xᵀ (designMap X θ - Y) + λ • z = 0
def ColumnNormalized (X) (C : ℝ) : Prop := ∀ j, ‖col X j‖ ≤ C * Real.sqrt n   -- Cor 7.22
noncomputable def supportRecoveryBound (X) (S) (w : EuclideanSpace ℝ (Fin n)) (λ : ℝ) : ℝ
  := (⨆ i:↥S, |((gramInv' X S).mulVec ((Xsub X S)ᵀ.mulVec w.ofLp)) i|)     -- B(λ;X), 7.45
   + matLinftyNorm (gramInv' X S) * λ        -- where gramInv' uses (XₛᵀXₛ/n)⁻¹ = n·gramInv
```
(`gramInv'` = inverse of the *normalized* Gram `XₛᵀXₛ/n`; in code either carry the `1/n`
explicitly or note `(G/n)⁻¹ = n • G⁻¹`. Finalize during F2.)

## Dependency DAG

```
VecNorms, LinearModel/Defs (existing)
   └─ F1 SupportSubmatrix ─┬─ F2 GramMatrix ─┬─ A2 DualCertificate ─┐
                           │                 └─ A4 Corollary7_22    ├─ A3 Theorem7_21 ─ A4(final)
   C0 Defs (imports F1,F2) ┘                 A1 Subgradient ────────┘
SubGaussian/*, Maximal/FiniteMaximal (existing) ─ A4
```

## Per-file sub-lemma tables (interface contract; `R`=real target, `S`=sorry-stub)

### F1 SupportSubmatrix.lean  (branch `hds/sr-submatrix`)
| name | statement | st |
|---|---|---|
| `Xsub_mulVec` | `(Xsub X S).mulVec v = X.mulVec (fun j => if h:j∈S then v ⟨j,h⟩ else 0)` | S |
| `Xsub_transpose_mulVec_apply` | `((Xsub X S)ᵀ.mulVec u) i = ∑ k, X k i.val * u k` | S |
| `designSub_apply` | `(designSub X S v).ofLp = (Xsub X S).mulVec v.ofLp` | S |
| `normSq_designSub` | `‖designSub X S v‖^2 = ∑ i:↥S, ((Xsub X S)ᵀ.mulVec ((Xsub X S).mulVec v.ofLp)) i * v.ofLp i` (= vᵀGₛv) | S |
| `col_eq_designMap_single` | `col X j = designMap X (EuclideanSpace.single j 1)` (links column to design map) | S |

### F2 GramMatrix.lean  (branch `hds/sr-gram`, after F1)
| name | statement | st |
|---|---|---|
| `gram_eq_quadForm` | `(gram X S).mulVec v ⬝ᵥ v = ‖designSub X S v‖^2` (quadratic form identity) | S |
| `gram_isHermitian` | `(gram X S).IsHermitian` | S |
| `gram_posDef_of_lowerEigenvalue` | `0<cmin → 0<n → LowerEigenvalue X S cmin → (gram X S).PosDef` | S |
| `gram_isUnit_det` | `… → IsUnit (gram X S).det` (⇒ `Invertible`, `gramInv` is two-sided inverse) | S |
| `gramInv_mulVec_gram` / `gram_mulVec_gramInv` | `(gramInv X S).mulVec ((gram X S).mulVec v) = v` etc. | S |
| `gramInv_isHermitian` | `(gramInv X S).IsHermitian` (inverse of Hermitian is Hermitian) | S |
| `norm_gramInv_mulVec_le` | `‖(gramInv X S).mulVec u‖ ≤ (1/(cmin·n))·‖u‖` (op-2 bound from min-eig) | S |
| `projPerp_apply_norm_le` | `‖(projPerp X S).mulVec u‖ ≤ ‖u‖` (orthogonal projection is contractive) | S |
| `projPerp_idempotent` | `(projPerp X S) * (projPerp X S) = projPerp X S` (optional, for honesty) | S |
| `matLinftyNorm_mulVec_le` | `‖A.mulVec v‖_∞ ≤ matLinftyNorm A · ‖v‖_∞` (Mathlib `linfty_opNorm` or local) | S |

### A1 Subgradient.lean  (branch `hds/sr-subgrad`)
| name | statement | st |
|---|---|---|
| `l1_subgradient_iff` | `IsL1Subgradient z θ ↔ (⟪z,θ⟫_ℝ = l1Norm θ ∧ linfNorm z ≤ 1)` | S |
| `inner_le_l1Norm_of_linfNorm_le_one` | `linfNorm z ≤ 1 → ⟪z,θ⟫_ℝ ≤ l1Norm θ` (Hölder, reuse VecNorms) | S |
| `loss_convex_gradient` | `(1/2n)‖Y−Xθ̃‖² ≥ (1/2n)‖Y−Xθ̂‖² + ⟪(1/n)Xᵀ(Xθ̂−Y), θ̃−θ̂⟫_ℝ` (gradient ineq of quad loss) | S |
| `lasso_minimizer_exists` | `0<λ → ∃ β̂, IsLassoEstimator X Y λ β̂` (coercive EVT, `Continuous.exists_forall_le'`) | S |
| `kkt_of_isLassoEstimator` | `IsLassoEstimator X Y λ θ̂ → ∃ z, IsL1Subgradient z θ̂ ∧ IsKKT X Y λ θ̂ z` | S |
| `pdw_every_minimizer_supported` (7.23b) | witness (`θ̂` supp⊆S, `z` with `IsL1Subgradient`, `IsKKT`, `linfNorm (restrict Sᶜ z)<1`) → every `IsLassoEstimator X Y λ θ̃` has `restrict Sᶜ θ̃ = 0` | S |
| `pdw_unique` (7.23a) | witness + `LowerEigenvalue` (A3) → the Lasso minimizer is unique | S |

### A2 DualCertificate.lean  (branch `hds/sr-dualcert`, after F1,F2)
| name | statement | st |
|---|---|---|
| `oracle_solution` | `0<λ→0<n→LowerEigenvalue X S cmin→ ∃ θ̂ z, restrict Sᶜ θ̂ = 0 ∧ IsL1Subgradient z θ̂ ∧ IsKKT … ∧ (zS-block solves oracle)` (PDW steps 1–2) | S |
| `theta_diff_eq` (7.52) | `θ̂_S − θ*_S = (G_S)⁻¹Xₛᵀw − λn(G_S)⁻¹z_S` (block KKT solve) | S |
| `zSc_eq` (7.53) | `z_{Sᶜ} = μ + V_{Sᶜ}` with `μ = XₛᶜᵀXₛ(G_S)⁻¹z_S`, `V_{Sᶜ}=XₛᶜᵀΠ_{S⊥}(w/λn)` | S |
| `incoherence_bound` | `MutualIncoherence X S α → linfNorm(restrict Sᶜ z)≤α` for `μ` (incoherence+Hölder, `‖z_S‖_∞≤1`) | S |
| `noise_bound` | `λ ≥ (2/(1−α))‖XₛᶜᵀΠw/n‖_∞ → ‖V_{Sᶜ}‖_∞ ≤ ½(1−α)` | S |
| `strict_dual_feasibility` | `… → linfNorm (restrict Sᶜ z) < 1` (= `½(1+α)<1`) | S |
| `linf_error_bound` (7.54) | `… → linfNorm (restrict S (θ̂−θ*)) ≤ supportRecoveryBound X S w λ` | S |

### A3 Theorem7_21.lean  (branch `hds/sr-thm721`, after A1,A2)  — **main**
| name | statement | st |
|---|---|---|
| `lasso_support_recovery_unique` (a) | `…(A3)(A4)(λ≥7.44)(y=Xθ*+w)→ ∃! β̂, IsLassoEstimator X y λ β̂` | S |
| `lasso_support_recovery_no_false_inclusion` (b) | `…→ IsLassoEstimator X y λ β̂ → ∀ j∉S, β̂.ofLp j = 0` | S |
| `lasso_support_recovery_linf` (c) | `…→ IsLassoEstimator X y λ β̂ → linfNorm (restrict S (β̂−θ*)) ≤ supportRecoveryBound X S w λ` | S |
| `lasso_support_recovery_no_false_exclusion` (d) | `…→ IsLassoEstimator → ∀ i∈S, supportRecoveryBound X S w λ < |θ*.ofLp i| → β̂.ofLp i ≠ 0` | S |

### A4 Corollary7_22.lean  (branch `hds/sr-cor722`, after F2+Maximal; finalize after A3)  — **main**
| name | statement | st |
|---|---|---|
| `proj_noise_col_isSubGaussian` | `Zⱼ = ⟨projPerp Xⱼ, w⟩/n` sub-Gaussian proxy ≤ C²σ²/n (uses `projPerp_apply_norm_le`+`ColumnNormalized`+`isSubGaussian_const_mul`/`sum_of_iIndepFun`) | S |
| `gramInv_noise_coord_isSubGaussian` | `Z̃ᵢ = eᵢᵀ(G_S/n)⁻¹Xₛᵀw/n` sub-Gaussian proxy ≤ σ²/(cmin·n) (uses `norm_gramInv_mulVec_le`) | S |
| `lambda_event_highProb` | `P((2/(1−α))‖XₛᶜᵀΠw/n‖_∞ ≤ λ) ≥ 1 − 2e^{−nδ²/2}` for 7.46 λ (`tail_max_le` over `d−s`) | S |
| `linf_term_highProb` | `P(‖(G_S/n)⁻¹Xₛᵀw/n‖_∞ ≤ (σ/√cmin)(√(2log s/n)+δ)) ≥ 1 − 2e^{−nδ²/2}` (`tail_max_le` over `s`) | S |
| `lasso_support_recovery_subgaussian` (Cor 7.22) | union ⇒ both events w.p. `≥1−4e^{−nδ²/2}`; on them apply Thm 7.21 ⇒ unique, supp⊆S, ℓ∞ bound (7.47) | S |

## Parallelization waves (cluster; ≤3 concurrent, file-disjoint touch-sets)

- **Wave 0 (laptop):** all stub files + C0 Defs + umbrella registration + `.claude/prompts/sr-*.md`;
  commit; `lean-fasrc-build --worktree hds/lasso-support-recovery <Target>` green-with-sorries.
- **Wave 1:** F1 (`hds/sr-submatrix`) · A1 (`hds/sr-subgrad`, matrix-free parts).
- **Wave 2:** F2 (`hds/sr-gram`, after F1) · A1 uniqueness half (after F2).
- **Wave 3:** A2 (`hds/sr-dualcert`, after F1,F2) · A4 concentration lemmas (`hds/sr-cor722`, after F2).
- **Wave 4:** A3 (`hds/sr-thm721`, after A1,A2) → finalize A4 (after A3).

## Book-vs-Lean constants (fill as proved)

| Result | Book | Lean (proved) | Note |
|---|---|---|---|
| λ lower constant (7.44) | `2/(1−α)` | TBD | exact target |
| strict feasibility | `½(1+α)<1` | TBD | needs `α<1` |
| Cor 7.22 prob (7.47) | `1−4e^{−nδ²/2}` | TBD | `2 (over d−s) + 2 (over s)` |
| (A3) form | `γ_min(XₛᵀXₛ/n)≥cmin` | quadratic-form (≡) | Courant–Fischer |

## Risks (see plan)

1. `↥S` submatrix coercions (F1 isolates). 2. Block KKT 7.50–7.53 (A2, each step a named lemma).
3. Lemma 7.23 strict-convex uniqueness (A1). 4. Cor 7.22 sub-Gaussian proxy bookkeeping (F2 norm lemmas).
5. `Matrix.linfty_opNorm` exact API — verify on cluster, local `matLinftyNorm` fallback.
