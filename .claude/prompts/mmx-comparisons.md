# Close Pinsker (Lemma 15.2) and Le Cam inequality (Lemma 15.3)

Lean 4 / Mathlib proof engineer on **StatLean** (read `CLAUDE.md` §2,§6,§7). Pin `v4.29.1`. ON cluster
inside `srun` — iterate to 0 errors/0 sorries.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/PinskerInequality.lean`
- `StatLean/Minimaxity/ForMathlib/LeCamInequality.lean`
Keep signatures, tags, citation docstrings UNCHANGED. No `axiom`/`admit`. Helpers `private`. These are
genuine hard theorems; Mathlib has NO Pinsker. Available: `tvDist` (sup form), `klDiv`, `sqHellinger`
(all in `StatLean.Minimaxity`, use as black boxes via their `*_eq_*`/density lemmas in the same dir).

## Proofs
- `pinsker_tv_le_kl` : `tvDist μ ν ≤ (2⁻¹ * klDiv ν μ)^(1/2:ℝ)` (Ex 15.6). Reduce to Bernoulli via the
  partition `A={p≥q}` and the data-processing/`2(δ_p−δ_q)² ≤ δ_p log(δ_p/δ_q)+(1−δ_p)log((1−δ_p)/(1−δ_q))`
  pointwise inequality, then Jensen. If the full proof resists, lift the Bernoulli crux to a `private`
  lemma `pinsker_bernoulli` (sorry + `-- TODO(mmx): Ex 15.6`) and derive the general case, OR lift the
  whole thing to a single named debt and report — do not block LeCamInequality.
- `lecam_tv_le_hellinger` : `tvDist μ ν ≤ (sqHellinger μ ν)^(1/2) * (1 − sqHellinger μ ν/4)^(1/2)`
  (Ex 15.5). Cauchy–Schwarz on `|p−q| = |√p−√q|·|√p+√q|` against `μ+ν`: `∫|p−q| ≤ √(∫(√p−√q)²)·√(∫(√p+√q)²)`
  and `∫(√p+√q)² = 2 + 2∫√(pq) = 4 − H²`. Combine with `tvDist = ½∫|p−q|` (use `tvDist_eq_half_lintegral`).
  If it resists, lift to a named debt + report.

## DONE
`grep -c sorry` = 0 per file (or only reported named debts). Report closed/debt + the crux lemmas.
