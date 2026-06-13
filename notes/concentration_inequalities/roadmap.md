# ConcentrationInequalities — roadmap

Area reference: Lu, *Big Data Analysis*, ch. 2–4 (`ref/Lu_Big-Data-Analysis/latex/chapters/`). Tag with `Lu-BDA §X.Y`. Scope: **all theorems** of ch2–4; **no examples** (the KDE uniform-rate result is promoted from example to a stated theorem — verify at scaffold time it is wanted).

> Book constants are sometimes off by small factors. State the *provable* constant and record any deviation in the declaration docstring + the milestone `outline.md` constants table.

## Milestones (each gets `<milestone>/status.md` + `outline.md` when scaffolded)

| Milestone dir | Book items (env, label) |
|---|---|
| `subgaussian_core/` | ch2: LLN, CLT (unlabeled, Mathlib wrappers); Markov (`Markov`); Chernoff (`thm:chernoff`, Legendre-dual form); Sub-Gaussian def; two-sided tail (`thm:two-sided`); bounded⇒sub-Gaussian (proxy `(b-a)²/4`); Hoeffding (`thm:hoefdding`) |
| `subexponential_bernstein/` | ch3: sub-exponential def, two-regime tail (`thm:sub-exp`), sub-exp sample mean. ch4: Bernstein condition def, Bernstein inequality |
| `mcdiarmid/` | ch3: McDiarmid bounded-differences (`McDiarmid`) — not in Mathlib; build via Doob martingale + Mathlib conditional-sub-Gaussian Azuma |
| `maximal_covering/` | ch4: finite maximal (`thm:finite-maximal`); ε-net def; covering number of ℓ²-ball (`lm:covering-num`, `(1+2/ε)^d`); ℓ²-norm maximal (`thm:l2`) |

## Layout (`StatLean/ConcentrationInequalities/`, namespace `StatLean.ConcentrationInequalities`)

```
ConcentrationInequalities/
├── ClassicalLimits.lean            -- LLN + CLT, book-faithful wrappers over Mathlib
├── SubGaussian/{Defs,Chernoff,TailBounds,Bounded,Hoeffding}.lean
├── SubExponential/{Defs,TailBounds,SampleMean}.lean
├── McDiarmid/{CondHoeffding,DoobDecomposition,McDiarmid}.lean
├── Bernstein/{Defs,MGFBound,Bernstein}.lean
└── Maximal/{FiniteMaximal,CoveringNumbers,CoveringBall,L2Maximal}.lean
```

Key design decisions:
- **Sub-Gaussian** = `def IsSubGaussian X σ² μ := HasSubgaussianMGF (fun ω => X ω - μ[X]) σ² μ` — a bridge to Mathlib's `ProbabilityTheory.HasSubgaussianMGF`, which already gives the MGF sum bounds and Azuma machinery. The integrability side-condition is an honest `-- LEAN-ONLY` field.
- **LLN/CLT/Markov** are Mathlib wrappers: `ClassicalLimits.lean` states book-faithful forms whose proofs delegate to `strong_law_ae` / `tendstoInDistribution_inv_sqrt_mul_sum_sub` / `mul_meas_ge_le_integral_of_nonneg`.
- **McDiarmid, sub-exponential, Bernstein, the `(1+2/ε)^d` ball-covering bound** are NOT in Mathlib — built here.

## Hardest items (time-box + named-sorry fallback)
- `McDiarmid/CondHoeffding` → `DoobDecomposition` (conditional Hoeffding on `Measure.pi`). Fallback sorry: `condExp_hoeffding_mgf`.
- `Maximal/CoveringBall` (Zorn-maximal separated set + Haar volume count). Fallback sorry: `card_le_of_isSeparated_ball`. **Do not** substitute a coordinate grid — it corrupts the √d rate in `thm:l2`.

DAG: `ForMathlib(AS) → SubGaussian → {SubExponential, Bernstein, Maximal, McDiarmid}`. Cross-area: `HighDimensionalStatistics` consumes `SubGaussian` (Hoeffding, tails) and `Maximal` (`thm:l2`).
