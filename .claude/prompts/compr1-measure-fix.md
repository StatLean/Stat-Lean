# Lane B follow-up — close the three repaired rejection-sampling theorems

READ `.claude/prompts/compr1-_common.md` FIRST and obey every shared rule.

## Touch-set (the ONLY file you may modify)

`StatLean/ComputationalStatistics/MonteCarlo/RejectionSampling.lean`
(+ `LANE-REPORT.md`)

Build gate: `lake build StatLean.ComputationalStatistics.MonteCarlo.RejectionSampling`

## Context

The previous session refuted the three theorems at the `q ≡ ∞` corner (see the
retained `private` falsity witnesses in the file and the analysis + full
assembly route in `LANE-REPORT.md`). The laptop session has since REPAIRED the
statements by adding the missing book hypothesis
`hq1 : ∫⁻ z, q z ∂ν = 1` to `rejectionSampling_restrict_map`,
`rejectionSampling_acceptProb`, and `rejectionSampling_conditionalLaw`.
The statements as they now stand are FROZEN. Your job: replace their three
`sorry`s with proofs.

## Key consequences of `hq1` (per the previous session's own analysis)

- `q < ∞` a.e.[ν] (`ae_lt_top hq (hq1 ▸ ENNReal.one_ne_top)`), which kills the
  degenerate corner: the pointwise section computation can now be run under an
  a.e. filter where `q y ≠ ∞`.
- The route in `LANE-REPORT.md` ("the full pointwise case analysis and assembly
  route, which then goes through unchanged") is the intended proof: per
  measurable `S`, `Measure.map_apply` + `Measure.restrict_apply` +
  `Measure.prod_apply`; the `y`-section of the accept region has
  `uniform01`-measure `p y / (c * q y)` whenever `0 < q y < ∞` (envelope makes
  the ratio ≤ 1); `lintegral_withDensity_eq_lintegral_mul` converts the outer
  integral; `(p y / (c * q y)) * q y = p y / c` off `{q = 0} ∪ {q = ∞}`
  (`{q = 0}` contributes `0` to both sides since `p ≤ c·q` forces `p = 0`
  there; `{q = ∞}` is ν-null by `hq1`); finish with
  `lintegral_const_mul'`/`div_eq_mul_inv` and `withDensity_apply`.
- `rejectionSampling_acceptProb` = the restrict_map computation at `S = univ`
  plus `hp1` (or literally `congrArg (μ ↦ μ univ)` of restrict_map + `map_apply`
  at `univ` + `withDensity_apply … MeasurableSet.univ` + `hp1`).
- `rejectionSampling_conditionalLaw`: `ProbabilityTheory.cond` is
  `(μ A)⁻¹ • μ.restrict A`; use `Measure.map_smul`, the two previous theorems,
  `smul_smul`, `ENNReal.inv_inv`, `ENNReal.inv_mul_cancel hc0 hcT`-style
  algebra (watch the order: `(c⁻¹)⁻¹ * c⁻¹ = c * c⁻¹ = 1` needs `c ≠ 0, ≠ ∞`).

Do NOT modify the falsity-witness lemmas or any signature/docstring.
Commit after each closed theorem; finish with the build gate + updated
`LANE-REPORT.md` (append a "follow-up session" section) + final commit.
