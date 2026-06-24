# Compressed sensing (Lu-BDA ch. 6–7) — outline

Batch 4. Adds the `CompressedSensing/` sub-area to `StatLean/HighDimensionalStatistics/`.
Three book theorems, all noiseless exact recovery:

| Tag | Lean name | File | Book |
|---|---|---|---|
| T1 | `basisPursuit_unique_iff_cone_inter_ker` | `CompressedSensing/ConeTheorem.lean` | §6 `thm:cone` |
| T2 | `basisPursuit_recovers_of_rip` | `CompressedSensing/RIPRecovery.lean` | §7 `thm:rip` |
| T3 | `prob_rip_of_iid_gaussian` | `CompressedSensing/RandomRIP.lean` | §7 `thm:3s-rip` |

## Definitions (laptop-only `CompressedSensing/Defs.lean`)
- `IsSparse s x := ∃ S, S.card ≤ s ∧ ∀ i∉S, x.ofLp i = 0`  (book `‖x‖₀ ≤ s`).
- `IsBasisPursuit X Y β̂`  / `IsUniqueBasisPursuit X Y β̂`  (ℓ¹-min feasible / unique).
- `IsRIP X s δ := ∀ β, IsSparse s β → (1−δ)‖β‖² ≤ ‖Xβ‖² ≤ (1+δ)‖β‖²`.
- Cone `C(S) = reCone S 1` (reused from `Lasso/Defs.lean`); `Null(X) = ker (designMap X)`.

## Dependency DAG (files)
```
VecNorms(+5 bricks) ─┐
                     ├─ BasisPursuit (A1 cone-membership, A2 sufficiency) ─┬─ ConeTheorem (T1)
Defs ────────────────┘                                                    └─ RIPRecovery (T2) ─ TopK
GaussianMGF (existing) ─┐
SubExponential (existing)├─ GaussianChiSquared (chiSq1 sub-exp, fixed-β tail) ─ RandomRIP (T3)
CoveringBall (existing) ─┘
```

## Parallelization (cluster, 3 concurrent / 2 waves)
- **Wave 1 (leaves):** U1 `cs-base` {VecNorms, BasisPursuit} · U2 `cs-topk` {TopK} · U3 `cs-chisq` {GaussianChiSquared}.
- **Wave 2 (assemblies):** U4 `cs-cone` {ConeTheorem} · U5 `cs-rip` {RIPRecovery} · U6 `cs-random` {RandomRIP}.
- All touch-sets pairwise file-disjoint; each Wave-2 unit consumes merged Wave-1 output.
- Branches `hds/cs-{base,topk,chisq,cone,rip,random}` off integration branch `hds/compressed-sensing`.
- Prompts in `.claude/prompts/cs-*.md`.

## Key sub-lemmas
- VecNorms bricks: `l1Norm_add_le`, `l1Norm_split`, `restrict_add_restrict_compl`,
  `norm_le_sqrt_card_mul_linfNorm`, `norm_restrict_le_of_subset`.
- TopK: `orderedBlocks` (greedy decreasing-|·| `k`-block partition of `Sᶜ`) + disjoint/card/cover/
  empty-tail/`linfNorm`-averaging interface.
- BasisPursuit: `deviation_mem_cone_of_basisPursuit` (A1), `unique_basisPursuit_of_cone_trivial` (A2).
- GaussianChiSquared: `chiSq1_centered_isSubExponential` (α=4), `gaussian_quadratic_form_tail`.
- RIPRecovery core: private `rip_cone_trivial` (the bucketing/shelling NSP argument) → A2.
- RandomRIP core: `sup_ball_le_two_sup_net`, union bound over supports × ¼-net × per-vector tail.

## Book-vs-Lean constants
- T2 threshold `δ < 1/3`: exact and tight (`(1+δ)/(2(1−δ)) < 1 ⟺ 3δ < 1`).
- χ²₁ sub-exponential `α`: book uses sharp `α=2` (→ tail `exp(−nδ²/8)`); Lean uses `α=4` (range
  `|λ|≤1/4`), giving fixed-β tail `exp(−nδ²/C)` with `C` (likely 32). Documented in-file.
- T3 sample size `n ≥ (96/δ²)·s·log(18d/ε)`: the `96`/`18` are book values; the proof states the
  provable constant (adjusted to match the χ² tail `C`), order `O(s log(d/ε))` preserved.
