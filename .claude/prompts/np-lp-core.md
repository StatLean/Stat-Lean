# Close the 15 sorries in NonparametricStatistics/LocalPolynomial/{Quadratic,Reproduction,WeightBounds}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON the
cluster — iterate with plain `lake build StatLean.NonparametricStatistics.LocalPolynomial.Quadratic`
(then `.Reproduction`, `.WeightBounds`; no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/LocalPolynomial/Quadratic.lean`,
  `.../Reproduction.lean`, `.../WeightBounds.lean`. Touch nothing else (NOT `LocalPolynomial/Defs.lean`
  — definitions and constants there are frozen; NOT `Regression/Defs.lean`).
- Goal **0 sorries**, 0 errors. Keep theorem signatures, tags, docstrings UNCHANGED. You MAY add
  `import Mathlib.*` lines and `private` helper lemmas. Lines ≤ 100. If a piece resists, lift it
  to a `private lemma` with one `sorry` + `-- TODO(np):` and report.
- After green: `#print axioms` on `lpEstimator_eq_isLPSolution`, `lp_weight_reproduce_monomial`,
  `lp_weight_abs_le`, `lp_weight_sum_abs_le` → only `propext, Classical.choice, Quot.sound`.
- Do not weaken statements. If you believe one is false as stated, STOP and report why.

## Key definitions (Defs.lean, frozen — unfold with `simp [lpMatrix, lpWeight, …]`)
- `lpBasis ℓ u k = u^(k:ℕ) / (k:ℕ)!` — note `lpBasis ℓ 0 = Pi.single 0 1`-like: `0^0 = 1`,
  `0^k = 0` for `k ≥ 1`.
- `lpMatrix xdat K h ℓ t = ((n:ℝ)*h)⁻¹ • ∑ i, K zᵢ • Matrix.vecMulVec (lpBasis ℓ zᵢ) (lpBasis ℓ zᵢ)`
  with `zᵢ = (xdat i - t)/h`; `Matrix.vecMulVec u v = Matrix.of fun i j => u i * v j`.
- `lpRhs xdat Y K h ℓ t k = ((n:ℝ)*h)⁻¹ * ∑ i, Y i * lpBasis ℓ zᵢ k * K zᵢ`.
- `lpWeight … t i = ((n:ℝ)*h)⁻¹ * (lpMatrix …)⁻¹.mulVec (lpBasis ℓ zᵢ) 0 * K zᵢ`.
- `lpEstimator xdat Y K h ℓ t = ∑ i, Y i * lpWeight … i`.
- `lpObjective … θ = ∑ i, (Y i - ∑ k, θ k * lpBasis ℓ zᵢ k)^2 * K zᵢ`;
  `IsLPSolution … θ ↔ ∀ θ', lpObjective … θ ≤ lpObjective … θ'`.
- `lpWeightConst Kmax lam0 a₀ = max (2*Kmax/lam0) (4*Kmax*a₀/lam0)`.
- `DesignEigenvalueLB xdat K h ℓ lam0 : ∀ t ∈ Icc 0 1, ∀ v, lam0 * ∑ k, (v k)^2 ≤ ∑ k, v k * (lpMatrix …).mulVec v k`.
- `KernelBoxed K Kmax : (∀ u, |K u| ≤ Kmax) ∧ ∀ u, u ∉ Icc (-1) 1 → K u = 0`.
- `DesignDensityBound xdat a₀ : ∀ a b, a ≤ b → (n:ℝ)⁻¹ * ∑ i, (Icc a b).indicator 1 (xdat i) ≤ a₀ * max (b-a) (n:ℝ)⁻¹`.

## Useful Mathlib API
`Matrix.vecMulVec_apply`, `Matrix.transpose_smul`, `Matrix.transpose_sum`,
`Matrix.IsSymm` (`def`: `Mᵀ = M`), `Matrix.PosDef` (over ℝ: `M.IsHermitian ∧ ∀ x ≠ 0, 0 < x ⬝ᵥ M *ᵥ x`
— check the exact pin form; `Matrix.IsHermitian` over ℝ reduces to `IsSymm` via `star = id`,
`Matrix.isHermitian_iff_isSymm` or `IsSymm.isHermitian`), `Matrix.PosDef.det_pos`,
`Matrix.isUnit_iff_isUnit_det`/`Matrix.invertibleOfIsUnitDet`, `Matrix.nonsing_inv_mul`,
`Matrix.mul_nonsing_inv`, `Matrix.mulVec_mulVec`/`Matrix.mulVec` linearity (`Matrix.mulVec_add`,
`Matrix.mulVec_smul`, `Matrix.add_mulVec`, `Matrix.smul_mulVec_assoc`, `Matrix.sum_mulVec`?),
`Finset.sum_mul_sq_le_sq_mul_sq` (Cauchy–Schwarz for finite sums), `Finset.sum_comm`,
`Finset.mul_sum`/`Finset.sum_mul`, `abs_mul`, `abs_le`, `Real.exp_one_gt_d9` (e > 2.718…),
`Nat.factorial`, `Set.indicator_apply`, `Finset.sum_le_sum`, `pow_le_pow_left`,
`div_le_div_of_nonneg_left`, `nlinarith`.

## Proofs

### Quadratic.lean
1. `lpMatrix_isSymm`: `Matrix.IsSymm` = `Mᵀ = M`. Transpose commutes with `•` and `∑`
   (`Matrix.transpose_smul`, `Matrix.transpose_sum`); `(vecMulVec u u)ᵀ = vecMulVec u u`
   (entrywise: `Matrix.ext` + `vecMulVec_apply` + `mul_comm`).
2. `lpMatrix_posDef`: build `Matrix.PosDef`: hermitian from (1) (`IsSymm → IsHermitian` over ℝ);
   for `v ≠ 0`, `0 < lam0 * ∑ (v k)^2 ≤ vᵀMv` — positivity of `∑ (v k)^2` from `v ≠ 0`
   (`Finset.sum_pos'` + some `(v k)^2 > 0`, via `Function.ne_iff`). Bridge the stub's
   `∑ k, v k * M.mulVec v k` to Mathlib's `v ⬝ᵥ M *ᵥ v` (they are definitionally the same sum:
   `dotProduct`/`Matrix.dotProduct` unfolds to `∑ i, v i * w i`; `simp [Matrix.dotProduct]` or
   `rfl`-adjacent `change`).
3. `lpMatrix_inv_mulVec_sq_le`: let `B := lpMatrix …`, `w := B⁻¹.mulVec v`. If `∑ (w k)^2 = 0`
   trivial. Else: PosDef from (2) (instantiate `hLB` — note `hLB` here is at the fixed `t`, no
   `Icc` membership needed) ⇒ `IsUnit B.det` ⇒ `B.mulVec w = v` (`Matrix.mul_nonsing_inv` at the
   vector level: `mulVec_mulVec` or `Matrix.nonsing_inv_mulVec`-style; find with `exact?`).
   Chain: `lam0 * ∑ w² ≤ ∑ w (Bw) = ∑ w v ≤ √(∑w²)·√(∑v²)` — use the squared Cauchy–Schwarz
   `Finset.sum_mul_sq_le_sq_mul_sq : (∑ w v)^2 ≤ (∑ w²)(∑ v²)` and `nlinarith` to conclude
   `∑w² ≤ ∑v²/lam0²` (hint terms: `sq_nonneg (∑ w v)`, `mul_pos`, the chain squared).
4. `isLPSolution_iff_normal`: prove the completing-the-square identity first as a `private lemma`:
   for all `θ θ'` with `Δ := θ' - θ`,
   `lpObjective … θ' - lpObjective … θ
      = ((n:ℝ)*h) * (∑ k, Δ k * (lpMatrix …).mulVec Δ k)
        - 2*((n:ℝ)*h) * (∑ k, Δ k * ((lpMatrix …).mulVec θ - lpRhs …) k)` —
   CAREFUL with the `((n:ℝ)*h)⁻¹` normalization: this identity requires `(n:ℝ)*h ≠ 0`; when
   `(n:ℝ)*h = 0` the matrix is `0` (`inv_zero`-smul) and `hpd` is impossible ((2) with `v ≠ 0`
   fails; `Matrix.PosDef` of `0` is false since `Fin (ℓ+1)` is nonempty) — so first
   `rcases eq_or_ne ((n:ℝ)*h) 0` and kill the degenerate case from `hpd` (e.g.
   `hpd.det_pos`/quadratic at `Pi.single 0 1`). Expand everything with
   `simp [lpObjective, lpMatrix, lpRhs, Matrix.mulVec, Matrix.vecMulVec_apply, Finset.mul_sum]`,
   swap sums (`Finset.sum_comm`), `ring_nf`/`field_simp`. Then:
   (→) if `Bθ ≠ a`, pick `θ' := θ - s • (Bθ - a)` with small `s > 0`; the difference is
   `nh·(s²·qᵀBq - 2s·‖Bθ-a‖²) < 0` for `s < 2‖Bθ-a‖²/(qᵀBq+1)`-ish, contradicting minimality
   (bound `qᵀBq` crudely). (←) if `Bθ = a`, the difference is `nh·ΔᵀBΔ ≥ 0` by `hpd.2`/`hLB`
   (careful: `hpd.posDef` gives `> 0` for `Δ ≠ 0`; `= 0` case trivial).
5. `isLPSolution_inv_mulVec`: `(4).mpr` + `Matrix.mul_nonsing_inv`-style `B.mulVec (B⁻¹.mulVec a) = a`.
6. `isLPSolution_unique`: from (4), `B θ₁ = a = B θ₂`; injectivity of `mulVec` for invertible `B`
   (`B⁻¹.mulVec ∘ B.mulVec = id` via `Matrix.nonsing_inv_mul` + `mulVec_mulVec`; or
   `(Matrix.mulVec_injective_of_isUnit?)` — find with `exact?`).
7. `lpEstimator_eq_isLPSolution`: `lpEstimator = (B⁻¹.mulVec a) 0`: unfold `lpEstimator`,
   `lpWeight`, `lpRhs`; swap the `i`/matrix sums so that
   `∑ i, Y i * ((n h)⁻¹ * (B⁻¹.mulVec (U zᵢ)) 0 * K zᵢ) = (B⁻¹.mulVec (lpRhs …)) 0`
   (linearity of `mulVec` in the vector argument: `B⁻¹.mulVec` of a finite sum; use
   `Matrix.mulVec` unfolded as sums + `Finset.sum_comm` + `Finset.mul_sum`). Then `θ = B⁻¹ a`
   from (4)+(6): `θ = B⁻¹.mulVec a` since both are solutions.
8. `isLinearEstimator_lpEstimator`: `⟨fun t i => lpWeight xdat K h ℓ t i, fun Y t => rfl⟩`.

### Reproduction.lean
1. `lp_weight_reproduce_monomial`: define `q : Fin (ℓ+1) → ℝ := fun j => if (j:ℕ) = k then
   (Nat.factorial k : ℝ) * h^k else 0`. Check `∀ i, ∑ j, q j * lpBasis ℓ zᵢ j = (xdat i - t)^k`
   (single surviving term; `(zᵢ*h)^k = (xdat i - t)^k` needs `h ≠ 0`: `div_mul_cancel₀`).
   With responses `Y := fun i => (xdat i - t)^k`, `lpObjective … q = 0` (each residual `0`), so
   `q` is a minimiser (objective is a sum of `(…)²*K` — CAREFUL: `K` may be negative pointwise,
   so `lpObjective ≥ 0` is NOT automatic! Instead show `q` is a solution via the normal
   equations: `IsLPSolution ↔ B q = a` (Quadratic (4)) and verify `B q = a` directly — both
   sides are `(nh)⁻¹ ∑ᵢ (xᵢ-t)^k·U(zᵢ)·K(zᵢ)`-shaped sums; `Matrix.mulVec` + `vecMulVec_apply`
   expansion makes them literally equal after `Finset.sum_comm` + the single-term `q` collapse).
   Then `lpEstimator … = q 0` by `lpEstimator_eq_isLPSolution`, and
   `q 0 = if k = 0 then 1 else 0` (at `j = 0`: `0! * h^0 = 1`); finally
   `lpEstimator xdat (fun i => (xdat i - t)^k) … = ∑ i, (xdat i - t)^k * lpWeight … i` is `rfl`.
2. `lp_weight_sum_one`: specialize (1) to `k = 0`, `pow_zero`, `one_mul` under the sum.
3. `lp_weight_reproduce_poly`: linearity: distribute the outer sum
   (`Finset.sum_comm`, `Finset.sum_mul`), apply (1) termwise; only `k = 0` survives:
   `∑ k, c k * (if (k:ℕ) = 0 then 1 else 0)`-shape `= c 0` (`Finset.sum_ite_eq'`-style with
   `Fin` coercion care: the `if` is on `(k:ℕ) = 0` ↔ `k = 0` in `Fin (ℓ+1)`).

### WeightBounds.lean
1. `lpBasis_normSq_le`: `∑ k, (z^k/k!)² ≤ ∑ k, (1/k!)² ≤ ∑ k, 1/k!` (each factor `≤ 1`:
   `|z^k| ≤ 1` from `|z| ≤ 1`, `abs_pow`, `pow_le_one`; `(1/k!)² ≤ 1/k!` since `1/k! ≤ 1`).
   Then `∑_{k≤ℓ} 1/k! ≤ e`: `Real.sum_le_exp_of_nonneg`? — if no direct lemma, use
   `Real.exp_ge_sum_range`-style (`Real.sum_le_exp`… search; a known one:
   `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`? no). Robust route: `NNReal.exp`? Simplest:
   `Real.exp 1 = ∑' k, 1/k!` should exist as `Real.exp_eq_exp_ℝ`… search `exp_eq_tsum`/
   `Real.exp_eq_sum_range_add…`; if painful, prove `∑_{k≤ℓ} 1/k! ≤ 2.72 ≤ Real.exp 1` via
   `k! ≥ 2^(k-1)` (`Nat.factorial` vs `two_pow`: induction or find `Nat.two_pow_le_factorial`-ish)
   giving `∑ ≤ 1 + ∑_{k≥1} 2^{1-k} ≤ 1 + 2 = 3`? — that overshoots `e`. Use instead
   `∑_{k≤ℓ}(1/k!)² ≤ 1 + 1 + ∑_{k≥2}(1/k!)² ≤ 2 + ∑_{k≥2} 1/4^{k-1}·… ` — the TARGET is only
   `≤ Real.exp 1 ≈ 2.718`, and `∑(1/k!)² = 1 + 1 + 1/4 + 1/36 + … < 2.28`. Concretely:
   `(1/k!)² ≤ (1/2)^(2*(k-2))·(1/4)` for `k ≥ 2` (since `k! ≥ 2^(k-1)`), geometric sum
   `∑_{k≥2}(1/4)^{k-1} = 1/3`; total `≤ 2 + 1/3 < 2.7 < e` (`Real.exp_one_gt_d9`). Any correct
   route is fine.
2. `lp_weight_eq_zero_of_far`: `|zᵢ| = |xdat i - t|/h > 1` (`abs_div`, `hh`), so `K zᵢ = 0`
   (`hbox.2`, `zᵢ ∉ Icc (-1) 1` ↔ `1 < |zᵢ|` via `Set.mem_Icc`, `abs_le`); `lpWeight` has the
   factor `K zᵢ`: `mul_zero`.
3. `lp_weight_abs_le`: if `1 < |zᵢ|`, weight is `0` by (2) and RHS `≥ 0` (`lpWeightConst ≥ 0`
   from `le_max_left` + `div_nonneg`… note `2*Kmax/lam0 ≥ 0` needs `Kmax ≥ 0`, which follows
   from `hbox.1` at `u := 2` where `K 2 = 0`: `0 ≤ |K 2| ≤ Kmax`). Else `|zᵢ| ≤ 1`:
   `|lpWeight| = (nh)⁻¹ * |(B⁻¹.mulVec U(zᵢ)) 0| * |K zᵢ|`; coordinate ≤ norm:
   `|(w) 0|² ≤ ∑ k (w k)²`; `lpMatrix_inv_mulVec_sq_le` (with `hLB := heig t ht`) +
   `lpBasis_normSq_le` give `|w 0| ≤ √(e)/lam0 ≤ 2/lam0` (square both sides; `nlinarith` with
   `Real.exp_one_lt_d9` (e < 2.7182818286) and `sq_nonneg`); `|K zᵢ| ≤ Kmax`. Assemble:
   `≤ (nh)⁻¹ * (2/lam0) * Kmax = (2*Kmax/lam0)/(nh) ≤ lpWeightConst/(nh)` (`le_max_left`,
   `div_le_div_of_nonneg_right`-family, `(n:ℝ)*h > 0` from `hn`, `hh`).
4. `lp_weight_sum_abs_le`: split the sum by (2): only `i` with `|xdat i - t| ≤ h` contribute.
   `∑ i, |Wᵢ| ≤ (2Kmax/(lam0*n*h)) * ∑ i, (Icc (t-h) (t+h)).indicator 1 (xdat i)` (each
   contributing index has `xdat i ∈ Icc (t-h) (t+h)`: `abs_le`/`abs_sub_le_iff`; use (3) for the
   per-term bound and `Set.indicator` to count). `hdens (t-h) (t+h)` (with `t-h ≤ t+h` from
   `0 < h` derived from `hhl`+`hn`: `0 < 1/(2n) ≤ h`) gives
   `(n)⁻¹∑ indicator ≤ a₀ * max (2h) (n⁻¹) = a₀ * 2h` (since `h ≥ 1/(2n)` ⇒ `2h ≥ 1/n`:
   `max_eq_left`). Total: `(2Kmax/(lam0·nh))·(n·a₀·2h) = 4·Kmax·a₀/lam0 ≤ lpWeightConst`
   (`le_max_right`). Mind the `(n:ℝ)` cast arithmetic (`field_simp`; `n ≠ 0`).

Report final `lake build` status for all three modules + `#print axioms` for the four named
theorems (note any lifted `private` sorry).
