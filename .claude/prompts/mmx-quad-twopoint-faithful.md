Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "..."` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`. Build with plain `lake build`, ITERATE to 0 errors / 0 sorries. `private` helpers IN THIS FILE; never fabricate.

# CONTEXT — FAITHFUL re-do of #18 (user decision), in a file shared with #17
File: `StatLean/Minimaxity/Examples/LipschitzDensity.lean` (namespace `StatLean.Minimaxity`). It contains
TWO public theorems: `lipschitz_density_pointwise_rate` (#17, Ex 15.7 — already FAITHFUL & CLOSED, DO NOT
CHANGE IT) and `quadratic_functional_two_point_rate` (#18, Ex 15.8). The merged #18 used squared loss `(·²)`
with a *decoupled* placeholder `θfunc` — inconsistent with the real functional. REWRITE #18 ONLY to the
faithful absolute-error form (the book's `E|θ̂−θ| ≳ n^{-1/2}`):

```
theorem quadratic_functional_two_point_rate (n : ℕ) (hn : 1 ≤ n) :
    ∃ (ι : Type) (_ : MeasurableSpace ι) (f : ι → ℝ → ℝ) (θfunc : ι → ℝ)
      (Pn : Kernel ι (Fin n → ℝ)) (_ : IsMarkovKernel Pn),
      (∀ i, ∀ x ∈ Set.Icc (0:ℝ) 1, (1/2:ℝ) ≤ f i x) ∧
      (∀ i, θfunc i = ∫ x in Set.Icc (0:ℝ) 1, (deriv (f i) x)^2) ∧          -- REAL functional ∫(f')²
      (∀ i, Pn i = Measure.pi fun _ : Fin n =>
            (volume.restrict (Set.Icc (0:ℝ) 1)).withDensity fun x => ENNReal.ofReal (f i x)) ∧
      ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal (c * (n:ℝ)^(-(1:ℝ)/2)) ≤ minimaxRiskDist id θfunc Pn
```
Tag: `-- USER-INPUT: absolute-error loss (Φ=id) with the genuine functional θ(f)=∫(f')² and book rate n^{-1/2} (Wainwright Ex 15.8); the suboptimal two-point bound (cf. optimal n^{-4/9} in QuadraticFunctional.lean).`
Use `minimax_functional_modulus` (`LeCam/Functional.lean`) with `Φ = id` (Monotone + LowerSemicontinuous):
`minimaxRiskDist id θfunc Pn ≥ 4⁻¹·id(½·hellingerModulus θfunc (·) (ofReal(1/(2√n))))`.

# CONSTRUCTION (Ex 15.8) — two-point, `ι := Bool`, `m` sub-bumps with `m⁴ ≍ n`
`f false := U` (`fun _ => 1`); `f true := g := 1 + Σ_{j<m} φ_j`, smooth bump `φ` supp `⊆[0,1]`, `‖φ‖∞≤1/2`,
`∫₀¹φ=0`, `b₀=∫φ²`, `b₁=∫(φ')²`; `φ_j(x)=(C/m²)φ(m·x−j)` (disjoint supp). `C` small ⇒ `g≥1/2`, twice-smooth.
Real functional: `θfunc(true)=∫(g')²=Σ_j∫(φ_j')²=m·C²b₁/m³=C²b₁/m²`, `θfunc(false)=0`; gap `=C²b₁/m²`.
Hellinger (Taylor, like #17): `½H²(U‖g) ≤ (1/8)∫(Σφ_j)² = (1/8)Σ∫φ_j² = (1/8)·m·C²b₀/m⁵ = cb₀/m⁴`; set `m⁴≍n`
⇒ `H² ≤ 1/(4n) ≤ (1/(2√n))²`. With `m²≍n^{1/2}`, gap `=C²b₁/m² ≍ n^{-1/2}`. So the admissible pair (false,true)
gives `hellingerModulus θfunc (·) (ofReal(1/(2√n))) ≥ ofReal(gap)`, and `minimax_functional_modulus` (Φ=id) ⇒
`minimaxRiskDist id θfunc Pn ≥ 4⁻¹·½·gap = gap/8 ≍ n^{-1/2}`. Set `c`.
You may reuse / adapt the Hellinger-withDensity bridge pattern that the merged #17 part already has in this file
(`sqHellinger_withDensity_eq` or similar — read the file).

# REQUIREMENTS
ZERO sorry. **Do NOT touch `lipschitz_density_pointwise_rate` (#17) or its helpers** — only rewrite #18's
`quadratic_functional_two_point_rate` and its private crux/helpers (rename freely). Helpers `private`, THIS
file only. Do NOT touch `StatLean/Minimaxity.lean`, `lakefile`, `lean-toolchain`, `lake-manifest.json`,
`Defs.lean`, `Fano/`, `LeCam/`, other `Examples/`. After editing, `grep -c sorry` the file = 0 and BOTH #17 and
#18 must still build.

# TOUCH-SET: ONLY  StatLean/Minimaxity/Examples/LipschitzDensity.lean
# BUILD: lake build StatLean.Minimaxity.Examples.LipschitzDensity
# DONE = build exits 0 AND no sorry in the file AND #17 unchanged.
  Commit: `mmx(#18): faithful quadratic two-point — real ∫(f')², absolute loss, n^{-1/2} (Wainwright Ex 15.8)`.
  Report: build status, sorry count, confirmation #17 untouched, the construction, helpers, deviations.
