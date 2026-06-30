Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "..."` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries in the target file. Lift every sub-step to a proven `private` helper IN THIS FILE — NEVER leave a `sorry` or use `axiom`. This is a large measure-theory job (several hundred lines); that is expected — do it fully.

# CONTEXT
File: `StatLean/Minimaxity/Examples/LipschitzDensity.lean` (namespace `StatLean.Minimaxity`).
Two `sorry`s: `lipschitz_pointwise_modulus_bound` (#17, Ex 15.7, rate n^{-2/3}) and
`quadratic_two_point_modulus_bound` (#18, Ex 15.8, rate n^{-1/2}). Public theorems delegate via
`minimax_functional_modulus` (`LeCam/Functional.lean`, generic in `P : ι → Measure 𝓧`, needs
`[Nonempty ι]`, `[∀ i, IsProbabilityMeasure (P i)]`, `Monotone Φ`, `LowerSemicontinuous Φ`).

# AUTHORIZED STATEMENT REPAIR (both defects are confirmed; apply BOTH)
(a) **Existential restructure** (the universal `∀ family` form is false for a trivial `ι`).
(b) **Domain fix** (REQUIRED + AUTHORIZED): the reference measure must be
`volume.restrict (Set.Icc (-(1:ℝ)/2) (1/2))`, NOT unrestricted `volume` — Wainwright Ex 15.7/15.8 live on
`[-1/2,1/2]`, and `f ≥ 1/2` over all of ℝ has infinite mass (the current `volume.withDensity` form is
vacuous). Restate `lipschitz_density_pointwise_rate` as:
```
theorem lipschitz_density_pointwise_rate (n : ℕ) (hn : 1 ≤ n) :
    ∃ (ι : Type) (_ : MeasurableSpace ι) (_ : Nonempty ι) (f : ι → ℝ → ℝ)
      (_ : ∀ i, IsProbabilityMeasure
            ((volume.restrict (Set.Icc (-(1:ℝ)/2) (1/2))).withDensity fun x => ENNReal.ofReal (f i x)))
      (θfunc : ι → ℝ) (Pn : Kernel ι (Fin n → ℝ)) (_ : IsMarkovKernel Pn),
      (∀ i, θfunc i = f i 0) ∧
      (∀ i, LipschitzWith 1 (f i) ∧ ∀ x, (1/2:ℝ) ≤ f i x) ∧
      (∀ i, Pn i = Measure.pi fun _ : Fin n =>
            (volume.restrict (Set.Icc (-(1:ℝ)/2) (1/2))).withDensity fun x => ENNReal.ofReal (f i x)) ∧
      ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal (c * (n:ℝ)^(-(2:ℝ)/3)) ≤ minimaxRiskDist (·^2) θfunc Pn
```
and `quadratic_functional_two_point_rate` analogously (drop `hθ` and `LipschitzWith`; keep
`∀ i x, 1/2 ≤ f i x`; rate `n^{-1/2}`; `θfunc i := ∫_{Icc} (f i x)'^2` is hard to phrase — instead keep
`θfunc` abstract and use the value-gap the construction provides). Tag both:
`-- USER-INPUT: witnessing density sub-experiment on [-1/2,1/2] realizing the rate (Wainwright Ex 15.7/15.8); a lower bound on the full-class minimax.`

# WITNESS — `ι := Bool`, two explicit densities on `[-1/2,1/2]`
`f false := fun _ => (1:ℝ)`.  `f true := fun x => 1 + φ x`, hat function (Eq. 15.19) with `δ := (3/(4*n))^((1:ℝ)/3)`:
`φ x = if |x| ≤ δ then δ - |x| else if δ ≤ x ∧ x ≤ 3*δ then |x - 2*δ| - δ else 0` (for n ≥ 1, `δ ≤ 1/6`
after fixing the provable constant; ensure `3δ ≤ 1/2`, i.e. shrink δ or recenter so `supp φ ⊆ Icc`).
Prove as `private` helpers (all 0-sorry):
* `IsProbabilityMeasure ((restrict Icc).withDensity (ofReal ∘ f i))`: mass `= ∫_{Icc} f i = 1`
  (`f false`: `volume (Icc (-1/2) (1/2)) = 1`; `f true`: `1 + ∫_{Icc} φ = 1`, `∫_{Icc} φ = 0`).
* `LipschitzWith 1 (f i)` and `∀ x, 1/2 ≤ f i x` (φ is 1-Lipschitz, `‖φ‖∞ = δ ≤ 1/6` ⇒ `1+φ ≥ 5/6`).
* Value gap `|θfunc false − θfunc true| = |f false 0 − f true 0| = |φ 0| = δ`.
* Hellinger: `H²(P_false ‖ P_true) ≤ (1/8)∫_{Icc} φ² = (1/8)(4/3)δ³ = δ³/6` (Taylor of `√(1+u)`,
  `|Ψ''| ≤ 1/4`, first-order term killed by `∫φ=0`). With `δ³ = 3/(4n)`, `H² ≤ 1/(8n) ≤ (1/(2√n))²`.
  You will likely need a `private` bridge `sqHellinger ((rstr).withDensity (ofReal f)) ((rstr).withDensity (ofReal g))
  = ENNReal.ofReal (∫_{Icc} (√(f x) − √(g x))² dx)` — derive from the project's `sqHellinger` def
  (rnDeriv against the sum measure; both densities w.r.t. the common `restrict Icc`). Search
  `./tools/explore.sh "Radon Nikodym derivative withDensity"` / `"Hellinger withDensity"`.
* So the admissible pair (false,true) gives `hellingerModulus θfunc (fun i => P i) (ofReal(1/(2√n))) ≥ ofReal δ`,
  and `minimax_functional_modulus` ⇒ `minimaxRiskDist ≥ 4⁻¹(½δ)² = δ²/16 ≍ n^{-2/3}`. Set `c`.
#18: same family idea with the quadratic functional / single bump; suboptimal `n^{-1/2}` (do NOT attempt
the optimal n^{-4/9} — that is the separate `QuadraticFunctional.lean`, off-limits).

# REQUIREMENTS
ZERO sorry. Public names unchanged (statements existential + restricted-domain, tagged). Helpers `private`,
THIS file only. May add imports. Do NOT touch `StatLean/Minimaxity.lean`, `lakefile`, `lean-toolchain`,
`lake-manifest.json`, `Defs.lean`, `Fano/`, `LeCam/`, other `Examples/`. If you genuinely run out of
allocation time, commit all that compiles to 0-error (helpers proven, only the final assembly pending as ONE
clearly-named `private` lemma) and report precisely what remains — but aim for full closure.

# TOUCH-SET: ONLY  StatLean/Minimaxity/Examples/LipschitzDensity.lean
# BUILD: lake build StatLean.Minimaxity.Examples.LipschitzDensity
# DONE = build exits 0 AND no sorry in the file.
  Commit: `mmx(#17,#18): close Lipschitz/quadratic two-point rates — existential witness on [-1/2,1/2] (Wainwright Ex 15.7/15.8)`.
  Report: build status, sorry count, restructured statements, helpers added, constant deviations.
