# bayes4-debt-score — close `truncScore_mean_expansion` [debt lane]

Branch `bay/debt-score`. The shared rules above apply. **Single target.**

## Touch-set (ONLY this file)

- `StatLean/Bayesian/BernsteinVonMises/ScoreTest.lean`

Gate: `lake build StatLean.Bayesian.BernsteinVonMises.ScoreTest`

## The one target

```
theorem truncScore_mean_expansion (hPDF : IsPDFOf M μ) (hsc : Measurable sc)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc) {L : ℝ} (hL : 0 < L) :
    (fun θ => ∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ)
        - ∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ₀)
        - ∫ x, ⟪θ - θ₀, sc x⟫ • bvmTruncScore sc L x ∂(bvmOneObs M μ θ₀))
      =o[𝓝 θ₀] fun θ => ‖θ - θ₀‖
```

This is vdV p. 143: "`P_θ ℓ̇^L_{θ₀} − P_{θ₀} ℓ̇^L_{θ₀} = (P_{θ₀} ℓ̇^L_{θ₀} ℓ̇^T_{θ₀} + o(1))(θ − θ₀)`".
Everything else in the file is already closed and available: `measurable_bvmTruncScore`,
`norm_bvmTruncScore_le` (`‖f^L x‖ ≤ √k · L`), `truncScore_separation` (which CONSUMES this
lemma), `truncScore_empirical_dev_tail`, `exists_moderate_tests`.

## Intended route (DQM in its `√p` form; work coordinatewise)

Write `s_θ := M.sqrtDensity θ` so `p_θ = s_θ²` (`M.sqrtDensity_sq`) and
`bvmOneObs M μ θ = μ.withDensity (ofReal ∘ p_θ)`.

1. Turn all three integrals into `μ`-integrals against densities
   (`integral_withDensity_eq_integral_smul`-style; the densities are `ofReal (p_θ x)` and the
   integrand is bounded by `√k·L`, so integrability is free from
   `IsPDFOf.density_integrable`).
2. Factor the difference of densities: `p_θ − p_{θ₀} = (s_θ − s_{θ₀})(s_θ + s_{θ₀})`.
   Hence, coordinatewise (fix `j` and work with the scalar `f_j := (f^L)_j`, `|f_j| ≤ L`):
   `∫ f_j p_θ − ∫ f_j p_{θ₀} = ∫ f_j (s_θ − s_{θ₀}) (s_θ + s_{θ₀}) dμ`.
3. DQM gives `s_θ − s_{θ₀} = ½⟪θ−θ₀, sc⟫ s_{θ₀} + r_θ` with `‖r_θ‖_{L²(μ)} = o(‖θ−θ₀‖)` —
   this is exactly `hDQM.mem` + `hDQM.isLittleO` after unfolding
   `DifferentiableQuadraticMean` (see `StatLean/AsymptoticStatistics/DQM/Defs.lean`; the
   residual there is stated for the increment `h` at `θ₀ + h`, so instantiate `h := θ − θ₀`).
4. Also write `s_θ + s_{θ₀} = 2 s_{θ₀} + (s_θ − s_{θ₀})`. Expanding,
   `∫ f_j (s_θ − s_{θ₀})(s_θ + s_{θ₀}) =`
   `∫ f_j ⟪θ−θ₀, sc⟫ s_{θ₀}²  (= the claimed main term, since s² = p)`
   `+ 2∫ f_j r_θ s_{θ₀}`
   `+ ∫ f_j (s_θ − s_{θ₀})²`
   `+ ∫ f_j ⟪θ−θ₀, sc⟫ s_{θ₀} (s_θ − s_{θ₀})`  — collect carefully; the exact split is
   yours to choose, the point is that every term except the first is `o(‖θ−θ₀‖)`.
5. Bound the error terms by **Cauchy–Schwarz** in `L²(μ)` with `|f_j| ≤ L`:
   * `|∫ f_j r_θ s_{θ₀}| ≤ L ‖r_θ‖₂ ‖s_{θ₀}‖₂ = L ‖r_θ‖₂ = o(‖θ−θ₀‖)`
     (`‖s_{θ₀}‖₂ = 1` because `∫ p_{θ₀} = 1`; `M.sqrtDensity_memLp_two`);
   * `|∫ f_j (s_θ − s_{θ₀})²| ≤ L ‖s_θ − s_{θ₀}‖₂²` and
     `‖s_θ − s_{θ₀}‖₂ = O(‖θ−θ₀‖)` by `dqm_sqrt_density_l2_convergence`
     (`DQM/Properties.lean`), so this term is `O(‖θ−θ₀‖²) = o(‖θ−θ₀‖)`;
   * the mixed term likewise `≤ L ‖⟪θ−θ₀,sc⟫ s_{θ₀}‖₂ ‖s_θ − s_{θ₀}‖₂ = O(‖θ−θ₀‖²)`
     (use `dqm_score_memLp_two` for `‖⟪u,sc⟫ s_{θ₀}‖₂ ≤ C‖u‖`).
6. Assemble the coordinatewise `o` bounds into the vector statement: in
   `EuclideanSpace ℝ (Fin k)`, `‖v‖ ≤ √k · max_j |v_j|`, or sum the squares — either way
   finitely many `o(‖θ−θ₀‖)` terms give `o(‖θ−θ₀‖)`.

Useful `Asymptotics` API: `Asymptotics.isLittleO_iff` (ε-δ form), `IsLittleO.add`,
`IsBigO.mul`, `Asymptotics.isLittleO_iff_forall_isBigOWith`. For the L² work:
`MeasureTheory.MemLp`, `MemLp.integrable_mul` (Hölder L²×L² → L¹),
`eLpNorm`/`‖·‖₂` conversions, and CLAUDE gotcha §3 (`MemLp.integrable_sq` needs
`Mathlib.MeasureTheory.Function.L2Space` imported — add the import if you need it).

## Done

Gate green, 0 sorries in this file. If a step genuinely resists after ~45 min, report the
exact obstruction (which term, which inequality) rather than weakening the statement.
