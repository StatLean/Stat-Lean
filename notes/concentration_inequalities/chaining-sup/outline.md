# chaining-sup — genuine `sup_{t∈T}` chaining statements (outline)

Branch `conc/chaining-sup` off local main bb84b0b2. Plan:
`~/.claude/plans/i-want-to-fix-eager-snail.md`. User decisions (2026-08-15):
separable-process design; full-symmetry scope (54 decls); land on local main
only (no origin push, no website update).

## Problem

All chaining headliners are per-finite-subset (`F.sup'`, HDP Remark 7.2.1
reading) or countable (2 decls). The user wants honest `sup_{t∈T}` over an
arbitrary — possibly uncountable — metric space `T` (HDP Thm 8.1.3 / 8.5.2).
A genuine uncountable-sup statement is FALSE without a version-selection
hypothesis (per-`t` null modifications preserve `SubGaussianIncrements`,
inflate the sup): hence `IsSeparableProcess` (value-space Doob separability)
with constructors `of_countable` and `of_continuousOn` (+
`isSeparable_of_coveringNumber_ne_top`).

## Dependency tree

```
CountableSupLift.lean  (engines; no probability instance)
  E1 lintegral_biSup_le_of_forall_finset      — MCT lift (template Dudley.lean:609-708)
  E2 measure_exists_lt_le_of_forall_finset    — tail lift, existential event
  E3 measure_exists_pair_lt_le_of_forall_finset
  E6 lintegral_biSup_finset_ofReal_eq         — finite ⨆ofReal ↔ ofReal ∫ sup'
  E7 toReal_biSup_ofReal                      — guarded ofReal/⨆ commutation [FALLBACK]
  BR1/BR2 exists_(pair_)lt_of_lt_biSup_real   — ⨆-event → ∃-event (0 ≤ thr)
  E4/E5 integrable_biSup…/integral_biSup_le…  — Bochner bridges (≠⊤ guard)
SeparableProcess.lean
  S1 IsSeparableProcess (def) ; S2 of_countable ; S3 isSeparable_of_cov… ;
  S4 of_continuousOn ; S5 biSup_ennreal_comp_eq… (lsc) ;
  S6 biSup_real_comp_eq… (+hφ0, [FALLBACK]) ; S7 pair transport (lsc) ;
  S8 exists_lt_comp_of_mem_closure
DudleySup.lean        ← Dudley + engines + separable      (12 decls)
DudleyTailSup.lean    ← DudleyTail + engines + separable  (5 decls; T2a [FALLBACK])
GenericChainingSup.lean ← GenericChaining + …             (10 decls; G0 [FALLBACK])
DiscreteDudleySup.lean  ← DiscreteDudley + …              (7 decls)
DudleyConsumers.lean  (append)                            (3 decls)
```

## Constants (all frozen, unchanged from per-F family)

| family | anchored/mean-zero | abs | pair | tail |
|---|---|---|---|---|
| discrete (dudleyLSum) | 6√3 | 20 | — | — |
| integral (dudleyLIntegral) | 12√3 | 40 | 80 | 200·(toReal+u·diam) & 3-term |
| γ₂ (gammaTwo/gammaFunctional) | 20 | 20 | — | (12+4u) |
| consumer (√(CD)) | — | 80 | — | — |

## Statement-design invariants

- Mean-zero sup forms = anchored carrier `ENNReal.ofReal (X t − X t₀)`,
  `t₀ ∈ T` (bare real `⨆ t∈T, X t` is FALSE at |T|=1 — positive-part trap).
- ℝ≥0∞ primaries; real displays only under `hDL` / `hγ ≠ ⊤` guards.
- Cores measure entropy of FULL `T` (`F ⊆ C ⊆ T` composes; no ε/2 loss).
- Tail engines conclude on ∃-events; ⨆-displays via BR1/BR2 (`0 ≤ thr`).
- S6 carries `hφ0 : ∀ v, 0 ≤ φ v` (without it FALSE at `T = univ`,
  negative values); S5/S7 take LowerSemicontinuous (pair composition).
- Hypothesis shape: `Metric.diam T ≤ D` (published pairwise-cap
  `dudley_inequality_countable` untouched); constant shape
  `ENNReal.ofReal c * ↑K * …` per the per-F family.
- All existing declarations byte-identical (DudleyConsumers gets 1 added
  import + appended decls only).
