# Close the 8 sorries in ForMathlib/TrigDiscreteSums.lean + Projection/{TrigOrthogonality,DiscreteOrthogonality}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain
`lake build StatLean.NonparametricStatistics.ForMathlib.TrigDiscreteSums` (then
`.Projection.TrigOrthogonality`, `.Projection.DiscreteOrthogonality`; no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/ForMathlib/TrigDiscreteSums.lean`,
  `StatLean/NonparametricStatistics/Projection/TrigOrthogonality.lean`,
  `.../Projection/DiscreteOrthogonality.lean`. Touch nothing else (NOT `Projection/Defs.lean`).
- Goal **0 sorries**, 0 errors. Signatures/tags/docstrings frozen. You MAY add `import Mathlib.*`
  and `private` helpers. Lines ≤ 100. Escape hatch: one lifted `private` sorry + TODO + report.
  Foreground `lake build` only.
- After green: `#print axioms` on `trigBasis_orthonormal`, `trigBasis_discrete_orthonormal` →
  only `propext, Classical.choice, Quot.sound`.

## Frozen definitions (Projection/Defs.lean)
```
trigBasis j x = if j = 0 then 0 else if j = 1 then 1
  else if j % 2 = 0 then √2 * cos (2π * (j/2 : ℕ) * x) else √2 * sin (2π * (j/2 : ℕ) * x)
regularDesign n i = ((i:ℕ) + 1 : ℝ) / n    -- i : Fin n
```

## Strongly recommended groundwork (private normal-form lemmas, prove FIRST)
- `trigBasis_one : trigBasis 1 x = 1`; for `1 ≤ q`:
  `trigBasis_even : trigBasis (2*q) x = √2 * cos (2*π*q*x)` and
  `trigBasis_odd : trigBasis (2*q+1) x = √2 * sin (2*π*q*x)` (ℕ-division: `(2*q)/2 = q`,
  `(2*q+1)/2 = q` — `Nat.mul_div_cancel_left`, `Nat.succ_div`… or `omega`-friendly forms;
  parity conditions `(2*q) % 2 = 0`, `(2*q+1) % 2 = 1` by `omega`/`Nat.mul_mod_right`).
- Every `j ≥ 2` is `2*q` (`q = j/2 ≥ 1`) or `2*q+1` (`q = j/2 ≥ 1`): case on `Nat.even_or_odd j`
  with `j = 2*q` / `j = 2*q+1` extraction (`Nat.even_iff_exists_two_mul`…), plus `1 ≤ q` from
  `2 ≤ j`.
- Product-to-sum identities (private, by `Real.cos_add`/`cos_sub`/`sin_add`/`sin_sub` + `ring`):
  `2*cos A*cos B = cos (A−B) + cos (A+B)`; `2*sin A*sin B = cos (A−B) − cos (A+B)`;
  `2*sin A*cos B = sin (A+B) + sin (A−B)`.

## Proofs

### TrigDiscreteSums.lean (4 lemmas)
Complexify: with `e s := Complex.exp (2*π*Complex.I*m*(s+1)/n)`,
`∑_{s∈range n} cos(2π m (s+1)/n) = (∑ s ∈ range n, e s).re` and similarly `.im` for sin —
bridge via `Complex.exp_ofReal_mul_I_re/_im` (`exp(θi).re = cos θ`) and `Complex.re_sum`
(`Complex.re_sum`/`map_sum` for `Complex.reAddHom`?? — find; fallback: `Finset.sum_comm`-free
induction or `Complex.ofReal_sum`). Set `ζ := Complex.exp (2*π*Complex.I*m/n)`; `e s = ζ^(s+1)`
(`Complex.exp_nat_mul`/`← Complex.exp_int_mul`, exponent algebra). Then:
- `n ∣ m` case: `m/n ∈ ℤ`… write `m = n*k`: each angle `2π k (s+1)` — `cos = 1`, `sin = 0`
  REAL-side directly (`Real.cos_int_mul_two_pi`, `Real.sin_int_mul_two_pi` — check names;
  `Real.cos_nat_mul_two_pi`), sum of ones = `n`. (Do these two WITHOUT complexifying.)
  Edge `n = 0`: `range 0` sums are `0 = (0:ℝ)` ✓ (`Nat.cast_zero`).
- `¬ n ∣ m` case: `n ≠ 0` (since `0 ∣ m ↔ m = 0`… from `hm : ¬(n:ℤ) ∣ m`, `n = 0` would need
  `m ≠ 0` and still `¬0∣m` holds — handle: for `n = 0` the sum is empty = 0 ✓ so wlog `n ≥ 1`).
  `ζ ≠ 1`: `Complex.exp_eq_one_iff : exp z = 1 ↔ ∃ k : ℤ, z = k * (2*π*I)`; from
  `2πI·m/n = k·2πI` ⇒ `m/n = k` ⇒ `n ∣ m` in ℤ (`div_eq_iff`, `π ≠ 0` `Real.pi_ne_zero`,
  cast juggling `Complex.ofReal_ne_zero`) — contradiction.
  `ζ^n = 1`: `ζ^n = exp(2πI·m)` (`← Complex.exp_nat_mul`, `mul_div_cancel₀` with `(n:ℂ) ≠ 0`)
  `= 1` (`Complex.exp_int_mul_two_pi_mul_I m` — mind operand order `2*π*I*m` vs `m*(2*π*I)`;
  `mul_comm` congruence).
  `∑ s ∈ range n, ζ^(s+1) = ζ * ∑ s ∈ range n, ζ^s = ζ * (ζ^n − 1)/(ζ − 1) = 0`
  (`pow_succ'`/`Finset.mul_sum`, `Finset.geom_sum_eq hζ1`, `ζ^n − 1 = 0`). Real/imag parts → both sums 0.

### TrigOrthogonality.lean (3 lemmas)
- `trigBasis_abs_le`: case split on the if-chain; `|0| ≤ √2` (`Real.sqrt_nonneg` +
  `Real.one_le_sq_iff…` — for `1 ≤ √2`: `Real.one_le_sqrt` (with `1 ≤ 2`) or
  `Real.lt_sqrt`/`Real.le_sqrt'`); `|√2 * cos θ| = √2 * |cos θ| ≤ √2 * 1`
  (`abs_mul`, `abs_of_nonneg (Real.sqrt_nonneg 2)`, `Real.abs_cos_le_one`, `Real.abs_sin_le_one`).
- `trigBasis_measurable`: each branch continuous → measurable; the if-chain on `j` is a
  DISJUNCTION ON j (not x!) — so `trigBasis j` is literally one of the four functions:
  `rcases`/`split_ifs` OUTSIDE and use `Continuous.measurable` + `fun_prop` per branch.
- `trigBasis_orthonormal`: key integral facts (private):
  `Ic : ∀ k : ℕ, 1 ≤ k → ∫ x in (0:ℝ)..1, cos (2*π*k*x) = 0` and `Is` (sin version):
  substitute `intervalIntegral.integral_comp_mul_left` (or `..._comp_mul_left'`?):
  `∫₀¹ cos(c x) dx = c⁻¹ * ∫₀^c cos = c⁻¹ (sin c − sin 0)` (`intervalIntegral.integral_cos`),
  `sin (2πk) = 0` (`Real.sin_int_mul_two_pi` / `Real.sin_nat_mul_two_pi`? — if only
  `Real.sin_int_mul_pi` exists use `2πk = (2k)π`). Then the 9-case split on `(j, k)`
  (each `= 1` / even / odd, via the groundwork normal forms):
  * `j = k = 1`: `∫₀¹ 1 = 1` (`intervalIntegral.integral_const`).
  * `1` × (even/odd): `√2 * (cos/sin integral) = 0` via `Ic`/`Is` (`integral_const_mul`).
  * even(p) × even(q): integrand `2 cos(2πpx) cos(2πqx) = cos(2π(p−q)x) + cos(2π(p+q)x)`
    (`√2*√2 = 2` — `Real.mul_self_sqrt`). If `p = q` (⟺ `j = k`): first term `cos 0 = 1`
    integrates to 1, second `Ic (2p)` = 0 → total 1. If `p ≠ q`: BOTH frequencies nonzero —
    `p − q ≠ 0`: use the SUBTRACTION-SAFE form: write
    `cos(2πpx)cos(2πqx) = (cos((2πp−2πq)x) + cos((2πp+2πq)x))/2` with REAL coefficients
    (avoid ℕ-subtraction: work with `(p:ℝ) − q`, and extend `Ic` to REAL nonzero frequency:
    `Ic' : ∀ c : ℝ, c ≠ 0 → ∫ x in (0:ℝ)..1, cos (2*π*c*x) = sin (2*π*c)/(2*π*c)` won't be 0
    for general c!! — CAREFUL: `sin(2πc) = 0` only for INTEGER c. Here `c = p − q ∈ ℤ \ {0}` ✓
    so state `Ic'` for `c : ℤ`, `c ≠ 0`.) Same pattern for the rest.
  * even × odd / odd × odd: `2 sin cos = sin(sum) + sin(diff)` — `Is'` for `c : ℤ` — note
    `sin(2πc·x)` integral is `(1 − cos(2πc))/(2πc) = 0` since `cos(2πc) = 1` for `c ∈ ℤ` ✓
    (this one vanishes even at… no: `c = 0` gives integrand 0 anyway — `sin 0 = 0` — so `Is'`
    can take `c = 0` separately). Odd×odd same-frequency: `2sin² = 1 − cos(2·)` → 1.
  * Off-diagonal same-parity `j ≠ k` ⇒ `p ≠ q` (injectivity of `q ↦ 2q`/`2q+1`) and
    cross-parity always `j ≠ k`-consistent: even ≠ odd indices ✓ (the `if j = k` in the goal:
    `rw [if_neg]`/`if_pos` per case — index arithmetic by `omega`).
  Interval integrability side goals: all integrands continuous (`Continuous.intervalIntegrable`,
  `fun_prop`).

### DiscreteOrthogonality.lean (1 lemma)
`trigBasis_discrete_orthonormal`, `1 ≤ j, k ≤ n − 1`:
- Notation: `x_i = (i+1)/n`; the discrete sum `∑ i : Fin n, F ((i+1)/n)` ↔
  `∑ s ∈ Finset.range n, F ((s+1)/n)` (`Finset.sum_range` / `Fin.sum_univ_eq_sum_range`).
- From ranges: `2 ≤ n` (`1 ≤ j ≤ n−1` forces `n ≥ 2` — `omega` on ℕ facts).
- Same 9-case split; each product becomes cosine/sine sums at ℤ-frequencies `p ± q` scaled:
  `cos(2πp·(s+1)/n)·cos(2πq·(s+1)/n) = (cos(2π(p−q)(s+1)/n) + cos(2π(p+q)(s+1)/n))/2` — again
  keep frequencies in ℤ (or split by `p = q` / `p ≠ q` and use ℕ frequencies `p+q` and
  `p − q` with explicit sign handling: `cos` is EVEN so `cos(2π(p−q)x) = cos(2π(q−p)x)` —
  use `|p − q|`-free approach via wlog `q ≤ p`, `Real.cos_neg`).
- Apply `sum_cos_two_pi_mul_div_eq_zero` / `sum_sin_two_pi_mul_div_eq_zero` (ForMathlib, ℤ-dvd
  hypothesis `¬(n:ℤ) ∣ (m:ℤ)` for ℕ-frequency `m`) and the `_of_dvd` versions:
  * frequency ranges: `p, q ≤ (n−1)/2 <` — precisely: `j ≤ n−1` with `j = 2p` gives
    `2p ≤ n−1 < n`; `j = 2p+1` gives `2p < n`. So `p+q ≤ (j+k)/2 ≤ n−1 < n` and
    `0 < p+q < n` when at least one nonzero ⇒ `¬ n ∣ (p+q)` (`Nat.not_dvd_of_pos_of_lt`,
    cast to ℤ: `Int.natCast_dvd_natCast`); `0 ≤ |p−q| < n` similarly, `n ∣ (p−q) ↔ p = q`
    (in range). The double-frequency diagonal terms `2p, 2q < n` ✓ (from `j = 2p ≤ n−1` etc.).
  * diagonal: `(1/n)·∑ (1 + cos(2π(2p)(s+1)/n))/1` — sum of ones = `n` (`Finset.sum_const`,
    `Finset.card_range`), cosine sum 0, normalize `(n:ℝ)⁻¹ * n = 1` (`n ≠ 0`).
  * `j = k = 1`: `(1/n)·∑ 1 = 1` ✓.
- Assemble with `Finset.sum_congr` product-to-sum rewrites, `Finset.sum_add_distrib`,
  `Finset.sum_div`, `mul_comm` bookkeeping; close numeric goals `field_simp`/`ring`
  (`(n:ℝ) ≠ 0`).

Report final `lake build` status for all three modules + `#print axioms` for the two named
theorems (note any lifted `private` sorry).
