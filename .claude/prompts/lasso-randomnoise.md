Read CLAUDE.md (repo root) first and obey it — §2, §6, §7, §9, §10. Use the search tools.
Never `lake update`. You are ALREADY inside an srun allocation — build with plain `lake build`.

# CONTEXT (do NOT modify; READ them)
`Lasso/DeterministicRate.lean`: `lasso_l2_rate` — DETERMINISTIC: under `n>0, κ>0, λ>0`,
  `RestrictedEigenvalue X S κ 3`, `IsLassoEstimator X Y λ βhat`, `Y = designMap X βstar + ε`,
  `βstar` supported on `S`, and the tuning condition `λ ≥ (2/n)·linfNorm (Xᵀε)`, gives
  `‖βhat − βstar‖ ≤ (3/κ)·√s·λ`.
`Lasso/Defs.lean`, `LinearModel/Defs.lean` (`designMap`), `ForMathlib/VecNorms.lean` (`linfNorm`).
`SubGaussian/{Defs,Hoeffding,TailBounds}.lean`: `IsSubGaussian`, `hoeffding`,
  `IsSubGaussian.measure_abs_sub_integral_lt_le` (two-sided sub-Gaussian tail).

# TASK
Create `StatLean/HighDimensionalStatistics/Lasso/RandomNoise.lean`
(namespace `StatLean.HighDimensionalStatistics`) proving Lu *Big Data Analysis* §8 **Corollary
(rate of Lasso under sub-Gaussian noise)** (`cor:lasso-rate`): if the noises `ε₁,…,εₙ` are
independent, each sub-Gaussian with variance-proxy `σ²`, the columns are normalised
`(1/n)‖X_j‖² ≤ 1` (so `‖X_j‖² ≤ n`), `RE(κ,3)` holds, and `δ ∈ (0,1)`, then choosing the tuning
parameter `λ = C·σ·√(log(2d/δ)/n)` (state the explicit `C` you can prove — see CONSTANT below),
with probability at least `1−δ`,
  `‖βhat − βstar‖ ≤ (3/κ)·√s·λ = O(√(s·log d / n))` (`= O_P(√(s log d/n))`).

# PROOF (book §8)
The deterministic `lasso_l2_rate` does all the algebra; the ONLY probabilistic content is verifying
the tuning event `λ ≥ (2/n)·linfNorm(Xᵀε)` holds w.p. `≥ 1−δ`. Now
`linfNorm(Xᵀε) = maxⱼ |⟨X_j, ε⟩|`, and each `⟨X_j,ε⟩ = ∑ᵢ X_{ij} εᵢ` is sub-Gaussian with proxy
`σ²‖X_j‖² ≤ σ²n` (linear combination of independent sub-Gaussians — use `hoeffding`/the MGF-sum
lemma; this is the "sub-Gaussian vector" step). Union bound over the `2d` events
`{⟨X_j,ε⟩ > t}, {−⟨X_j,ε⟩ > t}` with the one-sided sub-Gaussian tail `exp(−t²/(2σ²n))`:
  `P(maxⱼ|⟨X_j,ε⟩| > t) ≤ 2d·exp(−t²/(2σ²n))`.
Set this `= δ` ⇒ `t = σ√(2n log(2d/δ))`; then `(2/n)·t = (2σ/√n)·√(2 log(2d/δ))`, so the tuning
condition holds with `λ = (2σ/√n)·√(2 log(2d/δ))` (equivalently `λ = C σ √(log(2d/δ)/n)`).

# CONSTANT — IMPORTANT: the book's `λ = σ√(log(2d/δ)/(2n))` is ~4× too SMALL to satisfy
`λ ≥ (2/n)‖Xᵀε‖∞` under this tail bound. State the **provable** `λ` (the one your union-bound forces,
e.g. `λ = 2σ√(2 log(2d/δ)/n)` or whatever your constants give) and DOCUMENT the deviation in the
theorem docstring. The `O_P(√(s log d/n))` order conclusion is unaffected.

ZERO sorry. Independence, sub-Gaussian `σ²`, normalised columns, `RE(κ,3)`, `δ∈(0,1)`, the chosen `λ`,
and `IsLassoEstimator`/model are `-- USER-INPUT: …; Lu-BDA §8 (cor:lasso-rate)`. If the
"linear-combination-of-sub-Gaussians is sub-Gaussian with proxy σ²‖X_j‖²" step needs a helper, prove
it in-file (it's `hoeffding` applied to `aᵢεᵢ`, or the MGF-sum bound). If a genuine Mathlib gap
remains, isolate ONE named sorry + ESCALATE note.

# TOUCH-SET: ONLY `StatLean/HighDimensionalStatistics/Lasso/RandomNoise.lean`.
# BUILD: lake build StatLean.HighDimensionalStatistics.Lasso.RandomNoise
# DONE = build exits 0; ZERO sorries (or 1 named + ESCALATE); §2 tags; commit
(`hds(lasso): sub-Gaussian-noise rate O_P(√(s log d/n)) (Lu-BDA §8 cor:lasso-rate)`). Report build +
sorry status + the exact provable λ constant. Independently re-verified.
