# Close the 4 sorries in NonparametricStatistics/Projection/{Aliasing,SobolevRate}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain `lake build StatLean.NonparametricStatistics.Projection.Aliasing`
(then `.Projection.SobolevRate`; no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/Projection/Aliasing.lean` and
  `.../Projection/SobolevRate.lean`. Touch nothing else (NOT `Projection/Defs.lean`).
- Goal **0 sorries**, 0 errors. Signatures/tags/docstrings frozen. You MAY add `import
  Mathlib.*` and `private` helpers. Lines ≤ 100. Escape hatch: one lifted `private` sorry +
  TODO + report. Foreground `lake build` only; never background/poll.
- After green: `#print axioms` on `MemEllipsoid.summable_abs`, `riemannResidual_abs_le`,
  `proj_sobolev_rate` → only `propext, Classical.choice, Quot.sound`.
- Do not weaken statements; if false as stated, STOP and report.

## Available API (proved, black boxes)
- `trigBasis_discrete_orthonormal`, `trigBasis_abs_le`, `trigBasis_orthonormal` (C2, closed).
- `summable_nat_add_rpow_neg (hs : 1 < s) (n) : Summable fun m : ℕ => ((n + m : ℕ):ℝ)^(−s)`,
  `tsum_nat_add_rpow_neg_le (hs : 1 < s) (hn : 2 ≤ n) :
   (∑' m, ((n + m : ℕ):ℝ)^(−s)) ≤ s/(s−1) * ((n:ℝ)−1)^(1−s)` — ForMathlib/TailSumRpow (B1).
- `coeffEstimator_mean`, `coeffEstimator_sq_error`, `proj_mise_decomposition`,
  `seriesFun_abs_le`, `summable_sq_of_summable_abs` — Projection/{CoefficientRisk,
  MISEDecomposition} (D3 work item; if not yet landed, those modules may carry sorries —
  transitive `sorryAx` is then EXPECTED and clears when D3 lands; report it).
- Defs recap: `sobolevWeight β j = if j % 2 = 0 then (j:ℝ)^β else ((j:ℝ)−1)^β` (rpow);
  `MemEllipsoid β Q θ`: fields `summable : Summable fun j => (sobolevWeight β j * θ j)^2`,
  `tsum_le : ∑' j, (sobolevWeight β j * θ j)^2 ≤ Q`;
  `riemannResidual θ n j = (n:ℝ)⁻¹ * (∑ i : Fin n, seriesFun θ (regularDesign n i) *
   trigBasis j (regularDesign n i)) − θ j`; `tailEnergy θ N = ∑' m, θ (N+1+m)^2`;
  `ellipsoidRadius β L = L^2 / π^(2β)`; `residualConst β Q = 2·√Q·√(2β/(2β−1))·3^(β−1/2)`.

## Key elementary facts to establish first (private)
- `sobolevWeight_ge (hβ : 0 < β) {m : ℕ} (hm : 2 ≤ m) : ((m:ℝ) − 1)^β ≤ sobolevWeight β m`
  (even case: `(m−1)^β ≤ m^β` `Real.rpow_le_rpow`; odd case: equality).
- `sobolevWeight_ge_of_ge (hβ) {N m} (hm : N + 1 ≤ m) (hN : 1 ≤ N) :
   (N:ℝ)^β ≤ sobolevWeight β m` (from the previous: `m − 1 ≥ N`).
- Nonnegativity: `0 ≤ sobolevWeight β j` (`Real.rpow_nonneg`; casts ≥ 0 — for `j = 0` note
  `(0:ℝ)^β = 0` ✓ and odd `j = 1`: `(1−1)^β = 0` ✓).

## Proofs (Aliasing.lean)

### 1. `MemEllipsoid.summable_abs (hβ : 1/2 < β) (hQ : 0 ≤ Q) (hθ : MemEllipsoid β Q θ) :
     Summable fun j => |θ j|`
Split: `|θ j| = |θ j|` summable ⟺ tail (from `j = 2`) summable (`summable_nat_add_iff`,
finitely many exceptions). For `j ≥ 2`: `|θ j| = (sobolevWeight β j)⁻¹ * (sobolevWeight β j
* |θ j|)` (weight > 0 there: `(j−1)^β ≥ 1^β = 1 > 0`); Cauchy–Schwarz for infinite sums:
`Summable.mul_of_sq`-style — use `Summable.of_nonneg_of_le` with the AM-GM bound
`a·b ≤ (a² + b²)/2`: `|θ j| ≤ ((sobolevWeight β j)⁻² + (sobolevWeight β j * θ j)²)/2`
(from `x·y ≤ (x²+y²)/2`, `sq_abs`) — the second series is `hθ.summable`; the first:
`(sobolevWeight β j)⁻² ≤ ((j:ℝ)−1)^(−2β)` for `j ≥ 2` and
`Summable fun j => ((j−1:ℕ):ℝ)^(−2β)` from `summable_nat_add_rpow_neg (by linarith : 1 < 2*β) 1`
(reindex `j = 1 + m`: `((1+m):ℝ) − 1 = m`… careful — cleanest: compare against
`fun m : ℕ => ((1 + m : ℕ):ℝ)^(−(2*β))` after the shift; mind `Real.rpow_neg`,
`Real.rpow_natCast` conversions and `((j:ℝ)−1) = ((j−1 : ℕ):ℝ)` for `j ≥ 1` (`Nat.cast_sub`)).
Assemble with `Summable.add`, `Summable.div_const`.

### 2. `riemannResidual_abs_le_tail (hj : 1 ≤ j) (hj' : j ≤ n−1) (hθ1 : Summable |θ|) :
     |riemannResidual θ n j| ≤ 2 * ∑' m, |θ (n + m)|`
- `n ≥ 2` (`omega`). Write `S := (n:ℝ)⁻¹ ∑ i, seriesFun θ (xᵢ) φⱼ(xᵢ)`.
- Interchange the finite design sum with the tsum defining `seriesFun`:
  `S = ∑' k, θ k * ((n:ℝ)⁻¹ ∑ i, trigBasis k (xᵢ) * trigBasis j (xᵢ))` — per design point the
  series `k ↦ θ k φ_k(xᵢ) φⱼ(xᵢ)` is summable (comparison `≤ 2|θ k|`); use `tsum_sum`?
  direction: finite-sum-of-tsum = tsum-of-finite-sum (`Finset.sum_tsum`?? — the lemma is
  `tsum_sum` or `Summable.tsum_finsetSum`… find: `Finset.tsum_sum`? Actually want
  `∑ i ∈ s, ∑' k, f i k = ∑' k, ∑ i ∈ s, f i k` — `Finset.sum_tsum_comm`?? if elusive, use
  `tsum_finsetSum`-by-induction on the finset or `integral`-free route via
  `Summable.tsum_add` induction — a private lemma by `Finset.induction` with
  `Summable.tsum_add` is 10 lines and robust). Also pull `θ k` and `(n:ℝ)⁻¹` constants
  (`tsum_mul_left`).
- Split the tsum at `n`: `∑'_k = ∑_{k ∈ range n} + ∑'_m (at k = n + m)`
  (`Summable.sum_add_tsum_nat_add n` — summability of the whole from the comparison).
- Head terms `k ≤ n−1`: `θ k * [discrete orthonormality] = θ k · δ_{kj}` — careful `k = 0`:
  `trigBasis 0 = 0` kills it (private: `(n:ℝ)⁻¹ ∑ᵢ φ₀φⱼ = 0`); `1 ≤ k ≤ n−1`:
  `trigBasis_discrete_orthonormal` — the head sum collapses to `θ j` (mind the `(n:ℝ)⁻¹`
  placement: distribute it INSIDE before applying the orthonormality lemma — its statement
  has the `(n:ℝ)⁻¹ * ∑` shape ✓). So
  `riemannResidual θ n j = ∑'_m θ (n+m) * c_m` with
  `c_m := (n:ℝ)⁻¹ ∑ᵢ φ_{n+m}(xᵢ) φⱼ(xᵢ)`, `|c_m| ≤ 2` (crude: `|φ| ≤ √2` twice, `√2·√2 = 2`;
  average of ≤ 2 terms: `(n:ℝ)⁻¹ · n · 2 = 2` — `Finset.abs_sum_le_sum_abs` + `card_univ`).
- Conclude: `|∑' θ(n+m) c_m| ≤ ∑' |θ (n+m)| * 2` (`tsum` abs bound + termwise; summability by
  comparison) `= 2 ∑' |θ (n+m)|` (`tsum_mul_right`).

### 3. `riemannResidual_abs_le (hβ : 1/2 < β) (hQ : 0 ≤ Q) (hn : 3 ≤ n) (hj hj') (hθ) :
     |riemannResidual θ n j| ≤ residualConst β Q * (n:ℝ)^(1/2 − β)`
- By (2) + ellipsoid Cauchy–Schwarz on the tail:
  `∑' m, |θ (n+m)| = ∑' m, (w m)⁻¹ · (w m · |θ (n+m)|)` with `w m := sobolevWeight β (n+m) > 0`
  (n+m ≥ 3 ≥ 2 ✓). Cauchy–Schwarz for tsums: `tsum_mul_le_sqrt_mul_sqrt`?? — Mathlib has
  `inner_mul_le_norm_mul_norm` on `lp`… elementary route: for any M, finite C-S
  (`Finset.inner_mul_le_norm_mul_norm` / `Finset.sum_mul_sq_le_sq_mul_sq`) on partial sums +
  limit (`tsum_le_of_sum_le`-style with monotone convergence:
  `∑_{m<M} |θ(n+m)| ≤ √(∑_{m<M} w⁻²)·√(∑_{m<M} (wθ)²) ≤ √(∑' w⁻²)·√Q'` where
  `Q' := ∑' (over the tail) (w·θ)² ≤ Q` (tail tsum ≤ full tsum of nonnegs:
  `tsum_le_tsum_of_inj` with the injection `m ↦ n+m`, or
  `Summable.tsum_le_tsum_of_nonneg`… use `(hθ.summable.comp_injective (add_right_injective n))`
  + `tsum_comp ≤` — the clean lemma: `tsum_le_tsum_of_inj (Function.injective) (nonneg)` ✓
  exists as `tsum_le_tsum_of_inj`); then `tsum_le_of_sum_range_le` on the |θ|-tail with the
  M-free RHS). `∑'_m w_m⁻² ≤ ∑'_m ((n+m:ℝ)−1)^(−2β) = ∑'_m (((n−1)+m : ℕ):ℝ)^(−2β)
  ≤ (2β/(2β−1)) ((n−2):ℝ)^(1−2β)` (`tsum_nat_add_rpow_neg_le` at `n−1 ≥ 2` ✓ `hn`; cast care
  `(n−1:ℕ)` vs `(n:ℝ)−1` `Nat.cast_sub`).
- Numeric assembly to the stated constant: `|residual| ≤ 2·√Q·√((2β/(2β−1))·(n−2)^(1−2β))`;
  `(n−2)^(1−2β) ≤ (n/3)^(1−2β) = 3^(2β−1)·n^(1−2β)` — CAREFUL with the NEGATIVE exponent
  `1−2β < 0`: base-monotonicity REVERSES: need `n − 2 ≥ n/3` ⟺ `2n/3 ≥ 2` ⟺ `n ≥ 3` ✓
  (`Real.rpow_le_rpow_left_iff`-for-neg-exponent: use `Real.rpow_le_rpow_of_nonpos`? — find
  the right name: for `0 < x ≤ y`, `c ≤ 0` ⇒ `y^c ≤ x^c` — `Real.rpow_le_rpow_left_of_nonpos`??
  loogle type-shape `0 < ?x → ?x ≤ ?y → ?z ≤ 0 → ?y ^ ?z ≤ ?x ^ ?z`).
  `√(3^(2β−1) n^(1−2β)) = 3^(β−1/2) · n^(1/2−β)` (`Real.sqrt_eq_rpow`,
  `← Real.rpow_natCast`… all via `Real.rpow_mul`, `Real.sqrt_mul` on nonnegs). Fold into
  `residualConst` (`Real.sqrt_mul'`, `mul_assoc` bookkeeping; `√(ab) = √a·√b`).

## Proof (SobolevRate.lean)

### 4. `proj_sobolev_rate (hβ : 1 ≤ β) (hL : 0 < L) (hα : 0 < α) (hσ : 0 ≤ σξ2)`:
`∃ C > 0, ∀ n N (hn : 3 ≤ n) (hNdef : N = ⌈α n^(1/(2β+1))⌉₊) (hNn : N ≤ n−1) θ
 (hθ : MemEllipsoid β (ellipsoidRadius β L) θ) …noise…, risk ≤ ofReal (C·n^(−2β/(2β+1)))`.
- `refine ⟨σξ2 * (α + 1) + (residualConst β (ellipsoidRadius β L))^2 * α
    + (ellipsoidRadius β L) * α^(−2*β) + 1, by positivity, ?_⟩` — wait, check each piece's
  provenance below and ADJUST the constant to what the estimates actually give (you may pick
  ANY closed form; recompute freely — the statement only demands SOME positive `C`; keep it
  a readable sum). Positivity: `residualConst ≥ 0` (product of nonnegs — `hQ : 0 ≤
  ellipsoidRadius` from `hL` squares/π-powers `positivity`), `α^(−2β) > 0`, `+1 > 0`.
- Setup: `2 ≤ n−1`… derive `1 ≤ N` (ceil of a positive: `Nat.one_le_ceil_iff`,
  `Real.rpow_pos_of_pos`, `hα`) and `N ≤ n−1` given. `hθ1 : Summable |θ|` via
  `MemEllipsoid.summable_abs (by linarith : 1/2 < β) … hθ` — DERIVED, per the audit rule.
- Apply `proj_mise_decomposition hN hNn hσ hθ1 hξm hξi hξ0 hξ2`: risk
  `= ofReal (σξ2·N/n + ∑_{j∈Icc 1 N} αⱼ² + tailEnergy θ N)`.
- Three bounds (all real, then `ENNReal.ofReal_le_ofReal`):
  * `σξ2·N/n ≤ σξ2·(α+1)·n^(−2β/(2β+1))`: `N ≤ α n^(1/(2β+1)) + 1`
    (`Nat.ceil_le_add_one`?? — `Nat.ceil_lt_add_one` for reals ≥ 0: `(⌈x⌉₊:ℝ) < x + 1` ✓),
    so `N/n ≤ (α n^(1/(2β+1)) + 1)/n = α n^(1/(2β+1) − 1) + n⁻¹ ≤ (α+1)·n^(−2β/(2β+1))`
    (`1/(2β+1) − 1 = −2β/(2β+1)` `field_simp`-identity; `n⁻¹ = n^(−1) ≤ n^(−2β/(2β+1))`
    since `−1 ≤ −2β/(2β+1)` and `n ≥ 1`: `Real.rpow_le_rpow_of_exponent_le (1 ≤ n)`).
  * `∑_{j ∈ Icc 1 N} αⱼ² ≤ N · (residualConst · n^(1/2−β))²` (each `|αⱼ| ≤ …` by
    `riemannResidual_abs_le` — ranges `1 ≤ j ≤ N ≤ n−1` ✓, `sq_le_sq'`;
    `Finset.sum_le_card_nsmul`, `Nat.card_Icc` = N ✓)
    `≤ (α n^(1/(2β+1)) + 1) · residualConst² · n^(1−2β)`; exponent bookkeeping to
    `≤ residualConst²·(α+1)·n^(1/(2β+1)+1−2β)` and
    `1/(2β+1) + 1 − 2β ≤ −2β/(2β+1)` ⟺ `1 + (1−2β)(2β+1) ≤ −2β` ⟺ … VERIFY:
    `(1−2β)(2β+1) = 1 − 2β − 4β² + … ` compute: `= 2β + 1 − 4β² − 2β = 1 − 4β²`. So LHS-sum
    `= 1/(2β+1) + 1 − 2β`; target `−2β/(2β+1)`; difference:
    `1/(2β+1) + 1 − 2β + 2β/(2β+1) = (1+2β)/(2β+1) + 1 − 2β = 2 − 2β ≤ 0` ⟺ `β ≥ 1` ✓✓
    (`Real.rpow_le_rpow_of_exponent_le`, `1 ≤ n`).
  * `tailEnergy θ N ≤ Q·α^(−2β)·n^(−2β/(2β+1))` with `Q := ellipsoidRadius β L`:
    `θ(N+1+m)² ≤ (w)⁻²·(w·θ)²` with `w = sobolevWeight β (N+1+m) ≥ (N:ℝ)^β` (groundwork
    lemma; `N+1+m ≥ N+1`, `1 ≤ N`) ⇒ `tailEnergy ≤ (N:ℝ)^(−2β) · ∑'(tail)(wθ)²
    ≤ N^(−2β)·Q` (tail ≤ full by `tsum_le_tsum_of_inj`; `hθ.tsum_le`); and
    `(N:ℝ) ≥ α n^(1/(2β+1))` (`Nat.le_ceil`) ⇒ `N^(−2β) ≤ α^(−2β) n^(−2β/(2β+1))`
    (negative exponent flips: same `rpow`-antitone lemma as in (3); `Real.mul_rpow`,
    `Real.rpow_natCast`-free rpow of rpow: `(n^(1/(2β+1)))^(2β)`… wait sign — work with
    `N^(−2β) = (N^(2β))⁻¹` and `N^(2β) ≥ α^(2β) n^(2β/(2β+1))` then invert
    (`one_div_le_one_div_iff`, positives).
- Sum the three `ofReal`-bounds (`ENNReal.ofReal_le_ofReal`, single `ofReal` of the real sum;
  `nlinarith`/`gcongr` to fold into `C·n^(−2β/(2β+1))`, using `n^(−2β/(2β+1)) > 0`).

Report final `lake build` status for both modules + `#print axioms` for the three named
theorems (note any lifted `private` sorry and any D3 transitive taint).
