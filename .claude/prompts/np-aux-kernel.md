# Close the 1 sorry in NonparametricStatistics/KernelDensity/AuxiliaryKernel.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON the
cluster — iterate with plain `lake build StatLean.NonparametricStatistics.KernelDensity.AuxiliaryKernel`
(no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/KernelDensity/AuxiliaryKernel.lean`. Touch
  nothing else (NOT `KernelDensity/Defs.lean`).
- Goal **0 sorries**, 0 errors. Keep the theorem signature, tags, docstring UNCHANGED. You MAY
  add `import Mathlib.*` lines and `private` helper lemmas/defs. Lines ≤ 100. If a piece
  resists, lift it to a `private lemma` with one `sorry` + `-- TODO(np):` and report. Run plain
  foreground `lake build` only — NEVER background it or poll with pgrep loops.
- After green: `#print axioms StatLean.NonparametricStatistics.exists_bounded_kernel_of_order`
  → only `propext, Classical.choice, Quot.sound`.

## Target
`exists_bounded_kernel_of_order (ℓ : ℕ) : ∃ (K : ℝ → ℝ) (Kmax : ℝ), 0 < Kmax ∧
  IsKernelOfOrder K ℓ ∧ (∀ u, |K u| ≤ Kmax) ∧ ∀ u, u ∉ Set.Icc (-1:ℝ) 1 → K u = 0`
where `IsKernelOfOrder K ℓ` = { `integrable_pow : ∀ j ≤ ℓ, Integrable fun u => u^j * K u`;
`integral_eq_one : ∫ u, K u = 1`; `moment_eq_zero : ∀ j, 1 ≤ j → j ≤ ℓ → ∫ u, u^j * K u = 0` }.

## Construction (box superposition + Vandermonde)
Let `d := ℓ / 2 + 1` (so `2*(d-1) ≥ ℓ - 1`, covering all even moment orders `≤ ℓ`).
Scales `a : Fin d → ℝ, a r := (r + 1 : ℝ) / d` — distinct, in `(0, 1]`.
Box at scale `s`: `box s u := if u ∈ Set.Icc (-s) s then 1/(2*s) else 0` (an indicator; use
`Set.indicator (Set.Icc (-s) s) (fun _ => 1/(2*s))` to avoid `Decidable` friction).

Moments of a box (prove as private lemmas, `s > 0`):
- `∫ u, u^j * box s u = 0` for ODD `j` (odd integrand over symmetric interval:
  `MeasureTheory.integral_eq_zero_of_odd`?? — search `integral_zero_of_odd` /
  `intervalIntegral.integral_of_odd`?; if absent, compute directly:
  `∫ u in (-s)..s, u^j/(2s) = (s^(j+1) − (-s)^(j+1))/((j+1)·2s) = 0` for odd `j` via
  `intervalIntegral.integral_pow` + `Odd.neg_pow`).
- `∫ u, u^(2*q) * box s u = s^(2*q) / (2*q + 1)` for all `q` (same closed form:
  `integral_pow`, `Even.neg_pow`; convert the full-line integral to `intervalIntegral` via
  `MeasureTheory.integral_indicator` + `integral_Icc_eq_integral_Ioc` +
  `intervalIntegral.integral_of_le`).
- `Integrable fun u => u^j * box s u` (bounded, compactly supported, measurable:
  `Integrable.indicator`-style or `MeasureTheory.Integrable.of_bounded`… simplest:
  `(Continuous.integrableOn_Icc …)`-free route: the function is
  `(Set.Icc (-s) s).indicator (fun u => u^j/(2s))`, integrable by
  `MeasureTheory.IntegrableOn.integrable_indicator` with `integrableOn_Icc` of a continuous
  function (`Continuous.integrableOn_Icc`), `measurableSet_Icc`).

Kernel: `K u := ∑ r, c r * box (a r) u` with coefficients `c : Fin d → ℝ` to be chosen.
Moment system: for `q = 0, …, d-1`:
`∫ u^(2q) K = ∑ r, c r * (a r)^(2q)/(2q+1) = δ_{q,0}`.
Matrix form: `M q r := ((a r)^2)^q` is a (transposed) **Vandermonde** matrix in the DISTINCT
values `(a r)^2` (injective: `a` strictly monotone positive ⇒ squares distinct) — invertible:
`Matrix.det_vandermonde_ne_zero_iff.mpr` (mind transpose conventions:
`Matrix.vandermonde v q r = v q ^ r`?? CHECK the actual def `Matrix.vandermonde : (Fin n → R) →
Matrix (Fin n) (Fin n) R`, `vandermonde v i j = v i ^ (j : ℕ)`; use `Mᵀ` as needed +
`Matrix.det_transpose`). Choose `c` := the solution of `M' c = e₀` where
`M' q r := ((a r)^2)^q / (2*q+1 : ℝ)` — row-scaling by nonzero `1/(2q+1)` preserves
invertibility (`Matrix.det_mul_row`-style: `M' = D * M` with `D` diagonal
`Matrix.diagonal (fun q => 1/(2q+1))`, `Matrix.det_diagonal`, product of nonzeros ≠ 0 —
or simply solve `M c = b` with `b q := if q = 0 then 1 else 0` scaled: the system
`∑ r, c r * ((a r)^2)^q / (2q+1) = δ_{q0}` ⇔ `M c = b'` with `b' q := (2q+1) * δ_{q0} = δ_{q0}`
— because `(2·0+1) = 1`! So just solve `∑ r c r ((a r)^2)^q = δ_{q0}` and the `q = 0` row gives
`∑ c r = 1`… WAIT: recompute — the moment equation has the `1/(2q+1)` factor:
`∑_r c_r a_r^{2q}/(2q+1) = δ_{q0}` ⇔ `∑_r c_r a_r^{2q} = (2q+1)·δ_{q0} = δ_{q0}` since at
`q = 0` the factor is 1 and at `q ≠ 0` the RHS is 0 either way. So the system IS plain
Vandermonde `M c = e₀`.) Take `c := M⁻¹ *ᵥ Pi.single 0 1` (`Matrix.mulVec_nonsing_inv`-family
gives `M *ᵥ c = Pi.single 0 1` from `IsUnit M.det`).

Verification of the three fields:
- `integral_eq_one`: the `q = 0` row (each `∫ box = 1`, so `∫ K = ∑ c r = (M *ᵥ c) 0 = 1` —
  careful: `(M *ᵥ c) q = ∑ r, ((a r)^2)^q * c r`; at `q = 0` that's `∑ c r` ✓).
- `moment_eq_zero`: odd `j` — every box moment vanishes, sum of zeros. Even `j = 2q` with
  `1 ≤ j ≤ ℓ`: then `1 ≤ q ≤ ℓ/2 ≤ d - 1`, so `q` is a valid nonzero row index:
  `∫ u^{2q} K = (1/(2q+1)) ∑ r c r ((a r)^2)^q = (1/(2q+1)) * (M *ᵥ c) q = 0` ✓
  (index juggling `Fin d` vs ℕ: `q < d` from `2q ≤ ℓ` and `d = ℓ/2 + 1` — `Nat.div` arithmetic:
  `q ≤ ℓ/2` from `2q ≤ ℓ` is `Nat.le_div_iff_mul_le` ✓).
- `integrable_pow`: finite sum of integrable box moments (`Integrable.sum`? —
  `integrable_finset_sum`, `Integrable.const_mul`).
- Bound: `|K u| ≤ ∑ r |c r| * (d/(2*(r+1))) ≤ …` — just take
  `Kmax := (∑ r, |c r| / (2 * a r)) + 1` (each `|box (a r) u| ≤ 1/(2 a r)`; `+1` gives
  `0 < Kmax` for free; `Finset.abs_sum_le_sum_abs`, `abs_mul`,
  indicator bound `Set.indicator_le'`-style or case split on membership).
- Support: `a r ≤ 1` so `box (a r) u = 0` outside `Icc (-1) 1`
  (`Set.indicator_of_not_mem`, `Icc (-a r) (a r) ⊆ Icc (-1) 1`).

All integrals are over `volume` on ℝ. Keep every box-moment computation a separate private
lemma; the assembly is then mechanical.

Report final `lake build` status + `#print axioms exists_bounded_kernel_of_order` (note any
lifted `private` sorry).
