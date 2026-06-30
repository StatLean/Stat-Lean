Read CLAUDE.md (repo root) first — §2, §6, §7, §9, §10. For Mathlib lemma search PREFER LeanExplore — `./tools/explore.sh "..."` — over loogle (user preference); `./tools/check.sh`/`./tools/api.sh` for exact names. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE until 0 errors / 0 sorries. Lift sub-steps to named `private` lemmas IN THIS FILE; never leave a `sorry`. This is the HARDEST example — time-box aggressively and build helper lemmas; if a deep analytic inequality resists, isolate it as a precisely-stated `private` lemma and prove it by elementary means (do NOT sorry).

# CONTEXT
File: `StatLean/Minimaxity/Examples/QuadraticFunctional.lean` (namespace `StatLean.Minimaxity`).
One `sorry`, crux `quadratic_convex_hull_config` (Wainwright Ex 15.11, OPTIMAL quadratic-functional rate
n^{-4/9} via Le Cam's convex-hull method). Public `quadratic_functional_optimal_rate` delegates to it via
`minimax_le_cam_convex_hull` (`StatLean/Minimaxity/LeCam/ConvexHull.lean`).

# STATEMENT REPAIR (REQUIRED — false for a trivial family `ι`)
Like the Lipschitz examples, the current public theorem takes `f : ι → ℝ→ℝ` UNIVERSALLY ⇒ false for a
singleton `ι` (no two separated functional values). Repair `quadratic_functional_optimal_rate` to the
EXISTENTIAL form asserting a WITNESSING sign-vector density family (this is exactly the book's construction
and matches `pca_minimax_rate`):
```
theorem quadratic_functional_optimal_rate (n : ℕ) (hn : 1 ≤ n) :
    ∃ (ι : Type) (_ : MeasurableSpace ι) (f : ι → ℝ → ℝ) (θfunc : ι → ℝ)
      (Pn : Kernel ι (Fin n → ℝ)) (_ : IsMarkovKernel Pn),
      (∀ i x, (1/2:ℝ) ≤ f i x) ∧
      (∀ i, Pn i = Measure.pi fun _ : Fin n =>
            (volume.restrict (Set.Icc (0:ℝ) 1)).withDensity fun x => ENNReal.ofReal (f i x)) ∧
      ∃ c : ℝ, 0 < c ∧ ENNReal.ofReal (c * (n:ℝ)^(-(4:ℝ)/9)) ≤ minimaxRiskDist (·^2) θfunc Pn
```
DOMAIN FIX (REQUIRED + AUTHORIZED): the reference measure MUST be `volume.restrict (Set.Icc (0:ℝ) 1)`,
not unrestricted `volume` — Wainwright Ex 15.11 lives on `[0,1]` and `f ≥ 1/2` over all of ℝ has infinite
mass (unrestricted `volume.withDensity` is vacuous / unwitnessable). The sign-vector bumps `φ_j` are
supported in `[0,1]`. Tag: `-- USER-INPUT: witnessing sign-vector density family on [0,1] realizing the optimal n^{-4/9} rate (Wainwright Ex 15.11).`
Re-shape the crux to construct the witness (or inline). Keep using `minimax_le_cam_convex_hull`.

# THE CONSTRUCTION (Wainwright Ex 15.11)
Index `ι := (Fin m → Bool)` (sign vectors `α ∈ {−1,+1}^m`), `m := ⌈stuff⌉` with `m^9 ≍ n²`.
`f_α(x) = 1 + Σ_{j<m} σ(α j) φ_j(x)`, `σ b = if b then 1 else -1`, `φ_j(x) = (C/m²)·φ(m(x − j/m))·𝟙[x∈[j/m,(j+1)/m]]`
for a fixed bump `φ : [0,1]→ℝ`, `‖φ‖∞ ≤ 1/2`, `∫φ = 0`, `b_0 = ∫φ² > 0`, `b_1 = ∫(φ')² > 0`. The functional
`θ(f) = ∫(f')²`. Two subfamilies `P₀ = {U^n}` (uniform), `P₁ = {P_α^n}`; the separation `δ ≍ n^{-2/9}` comes
from `θ(f_α) − θ(U) = C²b_1/m²`; the mixture `Q = 2^{-m} Σ_α P_α^n`.

# THE KEY BOUND (15.28) — build it (Wainwright cites Birgé–Massart 1995, Thm 1; you must prove it)
`H²(U^n ‖ Q) ≤ n² (Σ_{j<m} ∫ φ_j²)²`. Route (see Wainwright §15.2.2 derivation and bibliographic note):
the affinity `∫√(U^n · Q)` expands over the independent blocks; since each `φ_j` is supported on a distinct
sub-interval `I_j`, the cross terms factor, and a second-order (Taylor) expansion of `√` controls the
residual by `(Σ_j ∫φ_j²)²` with the `n²` from the product over samples. Formalize via the project's Hellinger
machinery in `StatLean/AsymptoticStatistics/ForMathlib/HellingerProduct.lean` (`api.sh` it). With
`∫φ_j² = (C²b_0)/m⁵`, this gives `H² ≤ n²(m·C²b_0/m⁵)² = n²C⁴b_0²/m⁸`; setting `m⁹ = 4b_0²n²` yields
`‖U^n − Q‖_TV ≤ H(U^n‖Q) ≤ 1/2`, and `minimax_le_cam_convex_hull` gives `≳ δ²/4 ≍ n^{-4/9}`.

If the full (15.28) proof is too long, isolate it as a single precisely-stated `private lemma` (named
`hellinger_signvector_mixture_le`) and prove it rigorously from the block structure — never `sorry`.

# REQUIREMENTS
ZERO sorry. Public name unchanged (statement becomes existential, tagged). Helpers `private`, in THIS file
only. May add imports. Do NOT touch `StatLean/Minimaxity.lean`, `lakefile`, `lean-toolchain`,
`lake-manifest.json`, `Defs.lean`, `Fano/`, other `Examples/`.

# TOUCH-SET: ONLY  StatLean/Minimaxity/Examples/QuadraticFunctional.lean
# BUILD: lake build StatLean.Minimaxity.Examples.QuadraticFunctional
# DONE = build exits 0 AND no sorry in the file.
  Commit: `mmx(#19): close quadratic_functional_optimal_rate, convex-hull + Birgé–Massart 15.28, existential (Wainwright Ex 15.11)`.
  Report: build status, sorry count, restructured statement, helpers added, how you proved 15.28, constant deviations.
  If you CANNOT close it fully, STOP, leave the single remaining sorry as a precisely-named `private` lemma,
  commit what compiles, and report exactly what is missing (so the laptop can fetch Birgé–Massart 1995).
