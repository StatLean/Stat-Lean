import StatLean.HypothesisTesting.GoodnessOfFit.SmoothTest
import StatLean.HypothesisTesting.ForMathlib.MultivariateBerryEsseen
import Mathlib.Algebra.Order.Chebyshev

/-!
# Smooth tests with a growing number of score directions

For fixed `k` the smooth test is consistent only against alternatives that move at least
one of the first `k` score directions — for the classical construction on `[0,1]`, only
against laws differing from the uniform in one of their first `k` moments. Letting `k` grow
with the sample size removes that restriction, at the price of a different limit theory:
the chi-squared approximation to the null law of `S_{n,k} = ∑_{j≤k} Z_{n,j}²` is replaced by
a normal one, since `χ²_k ≈ N(k, 2k)` for large `k`. The statement is
$$ \frac{S_{n,k_n} - k_n}{(2k_n)^{1/2}} \;\Longrightarrow\; N(0,1)
   \qquad (k_n \to \infty,\ k_n^3/n \to 0), $$
so that the test rejecting when that ratio exceeds `z_{1−α}` is asymptotically of level
`α`.

Contents:

* `bentkus_berry_esseen_convex`, `bentkus_berry_esseen_ball` — the multivariate
  Berry–Esseen bound the limit theorem rests on, over convex sets and over Euclidean
  balls; **statement only**;
* `weakConverges_of_tendsto_cdf` — the Helly–Bray/Lévy inversion on the line: pointwise
  convergence of distribution functions to that of a probability measure implies weak
  convergence (built from Mathlib's π-system criterion for weak convergence);
* `smoothStat_largeK_weakConverges_gaussian` — the limit theorem itself.

**Why a Berry–Esseen bound is needed.** For fixed `k` the null limit of `S_{n,k}` follows
from the central limit theorem alone. Here the dimension grows with `n`, so a limit theorem
at fixed `k` is useless: one needs a bound on the normal approximation error that is
explicit in `k` and `n`. The bound over Euclidean balls has an absolute constant — no
dimensional factor — which is exactly what makes the growth condition as weak as
`k_n^3/n → 0`: with `sup_j E|ψ_j|³ ≤ B` one gets `β = E|Y|³ ≤ B k^{3/2}` by Minkowski's
inequality, hence an error `≤ C B k_n^{3/2} n^{-1/2} → 0`. The convex-set bound, whose
constant carries a factor `k^{1/4}`, would force the strictly stronger `k_n^{7/2}/n → 0`.

**DEFERRAL-ELIGIBLE (planned debt; proofless in the reference tradition, cf. Bentkus
2003).** Both Berry–Esseen statements are recorded as named debts: they are quoted, not
proved, in the goodness-of-fit literature that uses them, and proving them is a
self-contained research-level project in its own right (Fourier analysis over convex
bodies, not an application of anything in this library). The limit theorem
`smoothStat_largeK_weakConverges_gaussian` is *not* deferral-eligible: it is **closed
here**, modulo the ball bound only (the convex-set bound is not used at all).

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 16 (Testing Goodness of
Fit), §16.4 (Neyman's Smooth Tests), Theorem 16.4.2 (§16.4.2, Neyman's Smooth Tests With Large
`k`) and Lemma 16.4.1 (the multivariate Berry–Esseen-type bound). (`TSH4 §16.4 Thm 16.4.2, Lem
16.4.1`.)

**Proof formalization notes.**
* Both Berry–Esseen statements are phrased at the level of laws — a probability measure
  `ν` on `EuclideanSpace ℝ (Fin k)` and the pushforward of the `n`-fold product under
  `y ↦ n^{-1/2} ∑ᵢ yᵢ` — rather than through random vectors on an ambient space. The
  i.i.d. hypothesis is then built into the product measure, and, more importantly, the
  absolute constant of the ball bound can be existentially quantified *outside* all of
  `k`, `n` and `ν` without dragging an ambient type through the existential.
* "Absolute constant" is transcribed literally: the constant is quantified outside the
  dimension, the sample size and the law. This is the whole content of that half of the
  statement — with a `k`-dependent constant it would follow from the convex-set half.
* Convex sets are required to be measurable as well as convex. In dimension at least two
  there exist convex sets that are not Borel (their boundary can carry a non-Borel set),
  so measurability is not implied and the probability of an arbitrary convex set is not
  otherwise defined.
* The third-moment quantity is `β = ∫ ‖y‖³ dν`, matching the source; the growth condition
  is `sup_j E|ψⱼ|³ ≤ B` uniformly in `j`, which yields `β ≤ B k^{3/2}` through Minkowski's
  inequality applied to `(∑ⱼ ψⱼ²)^{3/2}`.
* The limit theorem is stated with `AsymptoticStatistics.WeakConverges` for the
  standardized statistic, consistent with the rest of the directory, and the score system
  is an infinite family `ψ : ℕ → 𝓧 → ℝ` truncated to its first `kₙ` members at stage `n`.
* A one-line consequence, not stated separately: the test rejecting when
  `(S_{n,kₙ} − kₙ)/(2kₙ)^{1/2} > z_{1−α}` is asymptotically of level `α`.

**Bibliographic comments.** The smooth test and its score system are due to J. Neyman
("Smooth test for goodness of fit," *Skandinavisk Aktuarietidskrift* **20** (1937),
149–199). The multivariate Berry–Esseen bound over convex sets and, with a
dimension-free constant, over Euclidean balls is due to V. Bentkus ("On the dependence of
the Berry–Esseen bound on dimension," *J. Statist. Plann. Inference* **113** (2003),
385–402); the one-dimensional ancestors are A. C. Berry ("The accuracy of the Gaussian
approximation to the sum of independent variates," *Trans. Amer. Math. Soc.* **49** (1941),
122–136) and C.-G. Esseen ("On the Liapunoff limit of error in the theory of probability,"
*Ark. Mat. Astr. Fys.* **28A** (1942), 1–19). Normal limits for chi-squared-type statistics
with growing dimension go back to H. Cramér and, in the goodness-of-fit setting, to the
analyses of the number of cells by H. Mann and A. Wald (*Ann. Math. Statist.* **13** (1942),
306–317).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators InnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (chiSquared)

/-! ### The multivariate Berry–Esseen bound (statement only) -/

/-- **Berry–Esseen bound over convex sets.** For i.i.d. mean-zero random vectors in `ℝ^k`
with identity covariance and third absolute moment `β = E‖Y‖³`, the normal approximation
to the law of `n^{-1/2} ∑ᵢ Yᵢ` is accurate to `400 k^{1/4} β n^{-1/2}`, uniformly over
measurable convex sets.

DEFERRAL-ELIGIBLE (planned debt; proofless in the reference tradition, cf. Bentkus 2003):
this statement is quoted, not proved, and its proof is an independent project.

**UNUSED (wave 11).** This declaration now has no consumer anywhere in the repository, and no
downstream theorem rests on it. The convex-set normal approximation is available *proved* — at
the honest elementary rate `C_k (β/√n)^{1/4}` rather than the sharp `400 k^{1/4} β/√n` — as
`StatLean.HypothesisTesting.berryEsseen_convex_elementary` in
`ForMathlib.MultivariateBerryEsseen`, whose last missing ingredient (the Gaussian
boundary-shell bound `γ(Bᵋ) ≤ γ(B) + C_k ε` for convex `B`) is now proved in
`ForMathlib.GaussianShell`. The statement below is kept only as the quoted *sharp* reference
form; a human decides whether to remove it. -/
theorem bentkus_berry_esseen_convex {k n : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin k))}
    {B : Set (EuclideanSpace ℝ (Fin k))}
    -- USER-INPUT: a nonempty sample
    (hn : 0 < n)
    -- USER-INPUT: a nondegenerate dimension
    (hk : 0 < k)
    -- USER-INPUT: `ν` is the common law of the summands
    (hν : IsProbabilityMeasure ν)
    -- USER-INPUT: the summands are centred; Bentkus 2003
    (hmean : ∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0)
    -- USER-INPUT: the summands have identity covariance; Bentkus 2003
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin k),
      (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ)
    -- USER-INPUT: the third absolute moment is finite
    (hβ : Integrable (fun y => ‖y‖ ^ 3) ν)
    -- USER-INPUT: the comparison set is measurable (convexity does not imply it in
    -- dimension `≥ 2`)
    (hBmeas : MeasurableSet B)
    -- USER-INPUT: the comparison set is convex; Bentkus 2003
    (hBconv : Convex ℝ B) :
    |((((Measure.pi fun _ : Fin n => ν)).map
          fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) B).toReal
        - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) B).toReal|
      ≤ 400 * (k : ℝ) ^ ((1 : ℝ) / 4) * (∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ) := by
  -- TODO (RE-DERIVED AGAIN this batch; the deferral verdict is CONFIRMED once more, and
  -- this one honestly stays.  Nothing acquired in this batch touches it: the new material is
  -- the mixture–Neyman–Pearson closure of `AsymptoticMaximin.asymptotic_maximin_upper_bound`
  -- — a least-favourable spherical mixture, Cameron–Martin tilting of the standard Gaussian,
  -- and a Slutsky/weak-convergence limit passage — none of which produces a *quantitative*
  -- normal-approximation rate over convex bodies, which is the entire content here.)
  --
  -- The statement is the *sharp* Bentkus (2003) bound: rate `β/√n = n^{-1/2}` in the sample
  -- size, dimensional factor exactly `k^{1/4}`, absolute constant `400`, uniformly over all
  -- measurable convex sets.  Its proof is Fourier-analytic over convex bodies (surface-area
  -- / isoperimetric control of the `ε`-neighbourhood of `∂B` for the Gaussian measure) and
  -- is an independent project; nothing of that machinery exists in Mathlib v4.29.1.
  --
  -- It cannot be wired to the sibling `bentkus_berry_esseen_ball` below.  That one is
  -- discharged by `ForMathlib.MultivariateBerryEsseen.berryEsseen_ball_elementary`, whose
  -- honest rate is `C (β/√n)^{1/4} = C n^{-1/8}` — obtained by the elementary
  -- "smooth the indicator + Lindeberg swap" route, at the balance `ε⁻³ β/√n + Cε`.  (An
  -- earlier version of this comment called the exponent `1/4` "intrinsic"; that is FALSE,
  -- see the wave-13/16 amendment below — but the *ball* assembly has not been redone at the
  -- better exponent, so the sibling still quotes `1/4`.)  That rate is strictly
  -- weaker than `n^{-1/2}`, so it does not imply this statement in any regime; conversely
  -- this statement is not needed by any consumer in the file — the growing-`k` limit
  -- theorem below consumes only the *ball* version, and does so at the weaker rate, which
  -- still gives `→ 0` under the source's growth condition `k³/n → 0`.
  --
  -- So this declaration is a quoted reference statement with no downstream dependants, and
  -- stays as the planned, pre-agreed debt.
  --
  -- RE-CHECKED (wave 5), including the explicit question whether the consumer can be
  -- rerouted to the ball version or the statement weakened to a provable rate.
  -- • REROUTING IS ALREADY DONE.  A repository-wide search finds no consumer of this
  --   declaration at all — `smoothStat_largeK_weakConverges_gaussian` goes through
  --   `bentkus_berry_esseen_ball` (hence `berryEsseen_ball_elementary`, which is discharged),
  --   and the only other mentions of this name are in the docstrings of
  --   `ForMathlib/MultivariateBerryEsseen`.  So there is nothing downstream to amend.
  --   This is unchanged in wave 11: still zero consumers.
  --
  -- WAVE-11 AMENDMENT (the second wave-5 bullet is now WRONG and is corrected here).  That
  -- bullet claimed the *weakened* statement `≤ C_k (β/√n)^{1/4}` over convex sets was "the
  -- same open problem with a different exponent", on the ground that the elementary route
  -- only smooths radial indicators.  That was a mis-derivation: the mollification of
  -- `exists_smoothed_convex_indicator` smooths the indicator of an *arbitrary* set, and the
  -- only genuinely convex-specific input is the Gaussian boundary-shell bound
  -- `γ(Bᵋ) ≤ γ(B) + C_k ε`, which is now proved elementarily (no Ball, no isoperimetry) in
  -- `ForMathlib/GaussianShell`.  Consequently the weakened convex statement is PROVED, as
  -- `ForMathlib.MultivariateBerryEsseen.berryEsseen_convex_elementary`, 0-sorry and
  -- axiom-clean.  Any future consumer that tolerates the `1/4` exponent should be wired to
  -- that theorem rather than to this one.
  --
  -- What is *not* available, and is what this declaration still quotes, is the SHARP rate:
  -- `β/√n` with dimensional factor exactly `k^{1/4}` and absolute constant `400`.
  --
  -- WAVE-13 AMENDMENT (the previous sentence here was WRONG and is corrected).  That sentence
  -- claimed the elementary balance `ε⁻³ β/√n + C_k ε`, minimised at `ε ∼ (β/√n)^{1/4}`,
  -- "cannot do better whatever the shell constant is".  The arithmetic is right for that
  -- balance, but the balance is not forced: the `j`-th step of the hybrid telescope already
  -- carries an independent `N(0,(j/n)I_k)` summand, and for a Gaussian mollification the
  -- Lindeberg remainder costs `σ_j^{-3}`, not `‖D³f‖_∞`, because the shift can be moved onto
  -- the *density* (Cameron–Martin) instead of onto the test function.  Summing
  -- `min(A ε⁻³ n^{-3/2}, j^{-3/2})` over `j < n` turns `ε⁻³` into `ε⁻¹`, and the balance
  -- `ε⁻¹ β/√n + C_k ε` gives the strictly better elementary rate `(β/√n)^{1/2} = n^{-1/4}`.
  --
  -- WAVE-16: THAT IMPROVEMENT IS NOW PROVED IN FULL.  The last assembly brick — the hybrid
  -- telescope carrying its own Gaussian smoothing — is
  -- `abs_integral_smooth_sub_gaussian_improved`, and the headline it yields is
  -- `ForMathlib.MultivariateBerryEsseen.berryEsseen_convex_improved`,
  --   `|μₙ(B) − γ(B)| ≤ C (β/√n)^{1/2}` for measurable convex `B`, `C = C₀ + gaussianShellConst k`,
  -- 0-sorry and axiom-clean, together with its Lévy form `berryEsseen_convex_levy_improved`.
  -- So the convex side of the elementary route now stands at `n^{-1/4}`, not `n^{-1/8}`.
  -- The *ball* side too: `berryEsseen_ball_improved` gives `C (β/√n)^{1/2}` with the same
  -- dimension-free constant shape, the two exponents now sharing the `ε`-generic assembly
  -- `berryEsseen_ball_of_swap`.  The sibling `bentkus_berry_esseen_ball` below is left wired
  -- to the `1/4` version, since `(β/√n)^{1/2}` and `(β/√n)^{1/4}` are not comparable when
  -- `β/√n > 1` and no consumer needs the better exponent.
  --
  -- Even the improved elementary ceiling is `(β/√n)^{1/2}`, not `β/√n`, and THIS statement is
  -- still not implied by it.  RE-DERIVED (wave 16), concretely: the missing factor comes from
  -- the swap error being bounded *globally*, whereas `D³` of a mollified indicator lives on
  -- the `ε`-shell of `∂B`.  Localising replaces the uniform step bound by one weighted by
  -- `P(hybrid ∈ shell)`, which is an anti-concentration bound for the **hybrid** laws — not
  -- available from `gaussian_thickening_le`, which is about `γ` only.  Bentkus closes this by
  -- the self-improving induction `Δ ≤ A ε⁻³ δ (C_k ε + 2Δ) + C_k ε` (closing at
  -- `Δ ≲ C_k δ^{1/3}`, and at the sharp rate when iterated with the Gaussian smoothing).
  -- Formalising it needs a *weighted* version of `integral_abs_vecTiltRemainder_le` — the
  -- Cameron–Martin remainder integrated against `|G|` rather than bounded by `‖G‖_∞ = 1`,
  -- i.e. a Hölder/`L²` form of that lemma — plus an induction over `n` in which the bound
  -- being proved appears on both sides.
  --
  -- WAVE-19: BOTH OF THOSE TWO INGREDIENTS ARE NOW PROVED, and the deferral verdict is
  -- correspondingly narrowed — the gap is no longer "an independent project" but one
  -- precisely stated probabilistic step.
  -- • The weighted bound is `integral_abs_mul_vecTiltRemainder_le`, with the localised
  --   corollary `abs_integral_mul_vecTiltRemainder_le_of_support`: a test function with
  --   `|G| ≤ 1` supported on a set `S` pairs with the Cameron–Martin remainder at cost
  --   `√(γ S) · √tiltSqConst · ‖w‖³`.  It rests on the new `L²` remainder bound
  --   `integral_sq_vecTiltRemainder_le`, which is again DIMENSION-FREE (same
  --   one-dimensional-marginal reduction) and still cubic in the shift, so the telescope
  --   arithmetic is unchanged.  (It needs `‖w‖ ≤ 1`, which is exactly the regime the
  --   telescope uses; the `L²` statement is false for large tilts.)
  -- • The recursion is solved in the `SelfImproving` section of the same file, in all three
  --   shapes: `Δ ≤ A δ ε⁻³ (C_k ε + 2Δ) + C_k ε` closes at `Δ ≲ C_k δ^{1/3}`; the SMOOTHED
  --   recursion `Δ ≤ A δ ε⁻¹ (C_k ε + 2Δ) + C_k ε` — `ε⁻¹` being what the Gaussian smoothing
  --   of the hybrid telescope already buys — closes at `Δ ≤ 10 A C_k δ`, i.e. EXACTLY the
  --   sharp `β/√n` rate; and the Cauchy–Schwarz variant that the `L²` weighting actually
  --   supplies, `Δ ≤ A δ ε⁻¹ √(C_k ε + 2Δ) + C_k ε`, closes at `Δ ≲ (C_k β/√n)^{2/3}`,
  --   i.e. `O(n^{-1/3})`.
  -- WAVE-20: THE RECURSION IS NOW PRODUCED, and both structural obstacles are resolved.  The
  -- sharp headline `ForMathlib.MultivariateBerryEsseen.berryEsseen_convex_sharp` states
  --   `|μₙ(B) − γ(B)| ≤ 72 A C_k · β/√n` for measurable convex `B`,
  -- LINEAR in `β/√n`, proved from `exists_convexDiscrepancy_recursion` fed to
  -- `le_of_selfImproving_induction`.  It is NOT axiom-clean: it inherits exactly two named
  -- bricks, `hybridLaw_shell_le` and `exists_localised_swap_bound` (both `sorry` at the time;
  -- the first is proved in wave 22, see below).
  -- • Obstacle 1 (the class) is OVERTURNED, not solved.  The `ε`-shell is a difference of two
  --   convex sets, but the induction need not be enlarged to that class:
  --   `μ(B₁ \ B₂) = μ(B₁) − μ(B₂)` for `B₂ ⊆ B₁`, so two applications of the convex bound
  --   suffice (`measureReal_diff_le_of_convexDiscrepancy`); the difference structure survives
  --   only as the factor `2` in `C ε + 2Δ`.  The class is `convexDiscrepancy`, and it is
  --   affine-invariant (`measureReal_shell_preimage_aff_le`, proved).
  -- • Obstacle 2 (the family) is solved by the neighbour range `n/2 ≤ m ≤ n`.  `hybridLaw`
  --   makes the hybrid an explicit measure; for `2j ≥ n` its own Gaussian component (width
  --   `≥ 1/√2`) bounds the shell mass with NO induction
  --   (`gaussian_measureReal_shell_preimage_aff_le`, proved), and for `2j ≤ n` the sum part
  --   has `m = n − j ≥ n/2` summands.  `m = n` must be included (the `j = 0` hybrid IS `μₙ`),
  --   which `le_of_selfImproving_induction` handles with `Y = max (2Kδ) (D n)`, closing at
  --   `K = 18 A C` with no base case.
  -- WAVE-22: BRICK H IS PROVED (`hybridLaw_shell_le`, axiom-clean), so `berryEsseen_convex_sharp`
  -- now rests on exactly ONE brick, `exists_localised_swap_bound`.  Brick H came out of the two
  -- Fubini identities for `Measure.prod` applied to the explicit `hybridLaw` map, plus the
  -- wave-20 affine transport; the only non-formal ingredient was `map_sum_pi_dirac_drop`, that
  -- the `δ₀` factors of the hybrid product drop out of the law of the coordinate sum (proved by
  -- characteristic functions, no index surgery).  What is left is brick L: the rerun of
  -- `abs_integral_smooth_sub_gaussian_improved` with a shell-weighted Cameron–Martin remainder.
  -- Note that brick L as stated asks for the `L^∞` weight `W`, which is STRICTLY STRONGER than
  -- the wave-19 `L²`/Cauchy–Schwarz lemma `abs_integral_mul_vecTiltRemainder_le_of_support`
  -- (that one delivers `√W`, hence only `O(n^{-1/3})` through
  -- `cube_le_of_selfImproving_smoothed_sqrt`).  The `L^∞` form is not a corollary of the
  -- wave-19 lemma: it needs the shell weight to be carried by the HYBRID law rather than by `γ`.
  -- CONSTANT: WAVE-22 also improved the shell constant from `k^{3/2}` to `k^{1/2}`.
  -- `gaussianShellConst k` is now `4 e² √k` (`gaussian_le_of_gaussian_shift_cover`: one random
  -- Gaussian shift instead of the `2k`-fold coordinate cover), so the route gives `C ∼ k^{1/2}`,
  -- still not `400 k^{1/4}` — the residual `√k` is `E‖Z‖ ≤ √k` and closing it needs Ball's
  -- Gaussian-surface-area theorem, not anything in the recursion.  This declaration keeps its
  -- sharp Bentkus form with `400 k^{1/4}` and stays the pre-agreed, consumer-free debt of this
  -- file: wiring
  -- it to `berryEsseen_convex_sharp` would neither discharge it (the constant differs) nor
  -- reduce the project's `sorry` count (that theorem is itself brick-backed).
  --
  -- WAVE-24: BRICK L AS FROZEN IS FALSE, and is amended; its large-weight half is proved.  The
  -- wave-20 statement asked for `|∫f dμₙ − ∫f dγ| ≤ A (β/√n) ε⁻¹ W` with the BARE hybrid shell
  -- weight `W`.  Counterexample (in full at `exists_localised_swap_bound`): `k = 1`, `n = 1`,
  -- `ε = 1`, `ν` two-point with mass `p` at `−a`, `a = √((1−p)/p)`, `B = (−∞, −a/2]`.  The shell
  -- `[−a/2, −a/2+2)` misses both atoms of `ν`, so `W ≍ e^{−a²/8}` is admissible, while
  -- `∫f dν = p`; as `p ↓ 0` the left side is polynomially small and the right side
  -- exponentially small.  The mechanism: `W` may sit far BELOW the Gaussian shell scale
  -- `C_k ε`, which no swap estimate can exploit.  The amendment replaces the weight by
  -- `W + C_k ε`; it is free at the only call site, so `berryEsseen_convex_sharp` and its
  -- constant are unchanged.
  -- • PROVED, axiom-clean: `exists_smooth_swap_bound_of_one_le_weight` — the amended brick
  --   whenever `W + C_k ε ≥ 1`, with NO localisation at all.
  -- • The residue is one named brick, `localised_swap_bound_small_weight` (same statement under
  --   `W + C_k ε ≤ 1`), and the wave-22 claim that the localisation is a mechanical rerun of the
  --   telescope with the wave-19 `L²` lemma substituted is OVERTURNED.  Splitting
  --   `f = 1_{interior B} + g` leaves `∫ 1_K R_w dγ = γ(K − w) − Q_w(K)` with `K` convex, whose
  --   control by the shell mass wave 24 read as a Gaussian surface-area statement about convex
  --   bodies, i.e. Ball's input again.
  --
  -- WAVE-29: THAT LAST VERDICT IS OVERTURNED — no surface area is involved.  The tilt remainder
  -- has MEAN ZERO (`integral_vecTiltRemainder_eq_zero`), so a constant may be subtracted from
  -- the test function for free; a mollified convex indicator is CONSTANT on the ball of radius
  -- `r` about any `v` at distance `≥ r` from the shell; and Cauchy–Schwarz against the plain
  -- Gaussian tail `γ{‖z‖ ≥ r/σ}` (`stdGaussian_norm_ge_le`, Markov at any order) localises the
  -- indicator half.  New, proved, axiom-clean, dimension-free:
  -- `abs_integral_mul_vecTiltRemainder_le_of_const_off` and
  -- `abs_integral_shift_vecTiltRemainder_le_of_const_ball`.
  -- • Two corrections to the brick's interface, both forced and both FREE at the call site, so
  --   the recursion and `berryEsseen_convex_sharp` are again unchanged.  (i) The bad set is the
  --   TWO-SIDED shell `Bˢ \ B_{−s}`: the localisation also fails just INSIDE `B`, which the
  --   frozen outer-shell hypothesis could not see.  (ii) It must be controlled at EVERY width
  --   `s`, because step `j` is smoothed at `σⱼ = √(j/n)`, which for `j` near `n` is `≫ ε`.
  --   `hybridLaw_wideShell_le` (wave 29, proved) is brick H for exactly that, at every width;
  --   the conditioning shared with `hybridLaw_shell_le` is factored as
  --   `hybridLaw_le_of_affine_le`.
  -- • Two gaps neither wave 24 nor the wave-29 plan had seen: the `L²` tilt bound needs
  --   `‖w‖ = ‖y‖/√j ≤ 1`, so the wave-19 lemma does NOT apply verbatim to the `g` part either
  --   (the large-`‖y‖` region needs the tilt identity directly, and its `v`-average costs a
  --   two-sided shell at width `c‖y‖` — hence "every width"); and the summed weight is
  --   `δ(2 C_k log(1/ε) + W/ε)`, so this route will give the sharp rate UP TO ONE LOGARITHM,
  --   `C_k (β/√n)(1 + log(√n/β))`.  The log is intrinsic to a single mollification width.
  -- So THIS declaration is unchanged and stays the pre-agreed debt: the sharp `β/√n` route is
  -- still brick-backed, its eventual conclusion will carry a logarithm, and even then it gives
  -- `C ∼ √k`, not `400 k^{1/4}` — for the CONSTANT (not the rate) Ball's theorem is still what
  -- separates the two.
  sorry

/-- **Berry–Esseen bound over Euclidean balls, with a dimension-free constant (honest rate).**
There is an absolute constant `C` — independent of the dimension, of the sample size and of the
sampling law — such that the normal approximation to the law of `‖n^{-1/2} ∑ᵢ Yᵢ‖²`, over
half-lines `{‖z‖² ≤ t}`, is accurate to `C · (β/√n)^{1/4}` uniformly in the threshold, where
`β = ∫‖y‖³ dν`.

The absence of a dimensional factor is the entire content of the statement, and is what the
growing-`k` limit theorem below consumes; the constant is therefore quantified outside `k`, `n`
and the law.

**Honest deviation from the book.** Bentkus (2003) states the sharp rate `C β/√n = C n^{-1/2}`,
via Fourier analysis over convex bodies. What is proved here (`berryEsseen_ball_elementary`, in
`ForMathlib.MultivariateBerryEsseen`) is the strongest bound the *elementary* "smooth the
indicator + Lindeberg swap" route delivers honestly at the balance `ε⁻³ β/√n + C ε`, which is
minimised at `ε ~ (β/√n)^{1/4}`: `C · (β/√n)^{1/4} = C n^{-1/8}`.  (Wave-16 correction of an
earlier claim here that the exponent `1/4` is *intrinsic*: it is not.  The same elementary route
with the Gaussian-smoothed telescope gives `berryEsseen_ball_improved`, `C · (β/√n)^{1/2}`, also
with an absolute constant.  This declaration keeps the `1/4` form because the two are
incomparable when `β/√n > 1`, and because the growing-`k` consumer below only needs `→ 0` under
`k³/n → 0`, which the `1/4` form already gives.)  The sharp `n^{-1/2}` is not attempted.
This
weaker rate still suffices for every consumer here: with `β ≤ B k^{3/2}` the error is
`≤ C (B k^{3/2}/√n)^{1/4}`, which `→ 0` under exactly the source's growth condition `k³/n → 0`,
since `(k^{3/2}/√n)^{1/4} → 0 ⟺ k³/n → 0`. This statement is therefore *not* deferral-eligible;
it is discharged (modulo the elementary-route bricks named at `berryEsseen_ball_elementary`) by
`berryEsseen_ball_elementary`. -/
theorem bentkus_berry_esseen_ball :
    ∃ C : ℝ, 0 < C ∧ ∀ (k n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k))) (t : ℝ),
      0 < n → 0 < k → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k),
        (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν →
      |((((Measure.pi fun _ : Fin n => ν)).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) {z | ‖z‖ ^ 2 ≤ t}).toReal
          - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
              {z | ‖z‖ ^ 2 ≤ t}).toReal|
        ≤ C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) ^ ((1 : ℝ) / 4) :=
  berryEsseen_ball_elementary

/-! ### Private infrastructure for the growing-`k` limit

The reduction runs entirely through distribution functions: the Berry–Esseen ball bound
compares `P{Sₙ ≤ t}` with `χ²_{kₙ}(−∞, t]` uniformly in `t`, the standardising affine map
transports that comparison to the distribution functions of the standardised statistic, and
the CDF-to-weak-convergence inversion (`weakConverges_of_tendsto_cdf`) turns pointwise
convergence of the distribution functions back into weak convergence. -/

section GrowingK

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]

/-- **Helly–Bray / Lévy CDF inversion on the line.** If the distribution functions of a
sequence of probability measures on `ℝ` converge at *every* point to the distribution
function of a probability measure, then the measures converge weakly.

The proof is the π-system criterion `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`
applied to the half-open intervals: their measures are differences of values of the
distribution function, and every point of an open set has arbitrarily small half-open
neighbourhoods inside it. -/
private lemma weakConverges_of_tendsto_cdf {μs : ℕ → Measure ℝ} {ν : Measure ℝ}
    [hμs : ∀ n, IsProbabilityMeasure (μs n)] [IsProbabilityMeasure ν]
    (hcdf : ∀ x : ℝ, Tendsto (fun n => (μs n (Set.Iic x)).toReal) atTop
      (𝓝 ((ν (Set.Iic x)).toReal))) :
    WeakConverges μs ν := by
  classical
  set μs' : ℕ → ProbabilityMeasure ℝ := fun n => ⟨μs n, hμs n⟩ with hμs'
  set ν' : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩ with hν'
  -- the π-system of half-open intervals
  set S : Set (Set ℝ) := {s | ∃ a b : ℝ, a < b ∧ Set.Ioc a b = s} with hS
  have hpi : IsPiSystem S := isPiSystem_Ioc (f := (id : ℝ → ℝ)) (g := (id : ℝ → ℝ))
  have hmeas : ∀ s ∈ S, MeasurableSet s := by
    rintro s ⟨a, b, -, rfl⟩
    exact measurableSet_Ioc
  have hnhds : ∀ u : Set ℝ, IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u := by
    intro u hu x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hu x hx
    refine ⟨Set.Ioc (x - δ / 2) (x + δ / 2), ⟨x - δ / 2, x + δ / 2, by linarith, rfl⟩, ?_, ?_⟩
    · exact Filter.mem_of_superset
        (Ioo_mem_nhds (by linarith) (by linarith)) Set.Ioo_subset_Ioc_self
    · intro y hy
      refine hball ?_
      simp only [Metric.mem_ball, Real.dist_eq, abs_lt]
      obtain ⟨hy1, hy2⟩ := hy
      constructor <;> linarith
  -- the distribution-function difference formula
  have hdiff : ∀ (m : Measure ℝ), IsProbabilityMeasure m → ∀ a b : ℝ, a ≤ b →
      (m (Set.Ioc a b)).toReal = (m (Set.Iic b)).toReal - (m (Set.Iic a)).toReal := by
    intro m hm a b hab
    haveI := hm
    have hun : Set.Iic a ∪ Set.Ioc a b = Set.Iic b := Set.Iic_union_Ioc_eq_Iic hab
    have hsplit := measure_union (μ := m) (s₁ := Set.Iic a) (s₂ := Set.Ioc a b)
      (Set.Iic_disjoint_Ioc (le_refl a)) measurableSet_Ioc
    rw [hun] at hsplit
    rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    ring
  have htend : ∀ s ∈ S, Tendsto (fun n => μs' n s) atTop (𝓝 (ν' s)) := by
    rintro s ⟨a, b, hab, rfl⟩
    rw [← NNReal.tendsto_coe]
    simp only [hμs', hν', ← ProbabilityMeasure.measureReal_eq_coe_coeFn,
      ProbabilityMeasure.coe_mk, MeasureTheory.Measure.real]
    rw [hdiff ν inferInstance a b hab.le]
    refine Tendsto.congr' ?_ ((hcdf b).sub (hcdf a))
    filter_upwards with n
    exact (hdiff (μs n) (hμs n) a b hab.le).symm
  have key : Tendsto μs' atTop (𝓝 ν') :=
    hpi.tendsto_probabilityMeasure_of_tendsto_of_mem hmeas hnhds htend
  intro f
  have hI := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp key) f
  simpa only [hμs', hν', ProbabilityMeasure.coe_mk] using hI

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]

/-- The elementary `ℓ³ ⊂ ℓ²` bound `‖v‖³ ≤ √k ∑ⱼ|vⱼ|³`, with the *sharp* dimensional factor
`√k`. It is what turns the uniform third-moment bound `sup_j E|ψⱼ|³ ≤ B` into
`β = E‖Y‖³ ≤ B k^{3/2}`, and the sharpness of the exponent `1/2` is what makes the growth
condition `k³/n → 0` (rather than a stronger one) suffice.

Proof: Cauchy–Schwarz `(∑b²)² ≤ (∑b)(∑b³)` on `b = |v|` and Jensen `(∑b)³ ≤ k²∑b³` give
`(∑b²)⁶ ≤ k²(∑b³)⁴`; two square-root steps deliver `(∑b²)^{3/2} ≤ √k ∑b³`. -/
private lemma norm_cube_le_sqrt_card_mul {k : ℕ} (v : Fin k → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin k))‖ ^ 3
      ≤ Real.sqrt (k : ℝ) * ∑ j, |v j| ^ 3 := by
  classical
  set b : Fin k → ℝ := fun j => |v j| with hb
  have hbnn : ∀ j, 0 ≤ b j := fun j => abs_nonneg _
  set S1 : ℝ := ∑ j, b j with hS1
  set S2 : ℝ := ∑ j, b j ^ 2 with hS2
  set S3 : ℝ := ∑ j, b j ^ 3 with hS3
  have hS1nn : 0 ≤ S1 := Finset.sum_nonneg fun j _ => hbnn j
  have hS2nn : 0 ≤ S2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hS3nn : 0 ≤ S3 := Finset.sum_nonneg fun j _ => pow_nonneg (hbnn j) 3
  set N : ℝ := ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin k))‖ with hN
  have hNnn : 0 ≤ N := norm_nonneg _
  have hNsq : N ^ 2 = S2 := by
    rw [hN, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun j _ => by simp [hb, Real.norm_eq_abs]
  -- Cauchy–Schwarz
  have hCS : S2 ^ 2 ≤ S1 * S3 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k))
      (fun j => Real.sqrt (b j)) (fun j => b j * Real.sqrt (b j))
    have hprod : ∀ j : Fin k, Real.sqrt (b j) * (b j * Real.sqrt (b j)) = b j ^ 2 := by
      intro j
      have hms : Real.sqrt (b j) * Real.sqrt (b j) = b j := Real.mul_self_sqrt (hbnn j)
      calc Real.sqrt (b j) * (b j * Real.sqrt (b j))
          = b j * (Real.sqrt (b j) * Real.sqrt (b j)) := by ring
        _ = b j * b j := by rw [hms]
        _ = b j ^ 2 := by ring
    have hf2 : ∀ j : Fin k, Real.sqrt (b j) ^ 2 = b j := fun j => Real.sq_sqrt (hbnn j)
    have hg2 : ∀ j : Fin k, (b j * Real.sqrt (b j)) ^ 2 = b j ^ 3 := by
      intro j
      rw [mul_pow, Real.sq_sqrt (hbnn j)]
      ring
    simp only [hprod, hf2, hg2] at h
    exact h
  -- Jensen
  have hJ : S1 ^ 3 ≤ (k : ℝ) ^ 2 * S3 := by
    have h := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin k))) (f := b)
      (fun j _ => hbnn j) 2
    simpa using h
  -- combine
  have hstep : S2 ^ 3 ≤ (k : ℝ) * S3 ^ 2 := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hsq : (S2 ^ 3) ^ 2 ≤ ((k : ℝ) * S3 ^ 2) ^ 2 := by
      have h1 : (S2 ^ 2) ^ 3 ≤ (S1 * S3) ^ 3 := by
        exact pow_le_pow_left₀ (by positivity) hCS 3
      have h2 : (S1 * S3) ^ 3 = S1 ^ 3 * S3 ^ 3 := by ring
      have h3 : S1 ^ 3 * S3 ^ 3 ≤ ((k : ℝ) ^ 2 * S3) * S3 ^ 3 :=
        mul_le_mul_of_nonneg_right hJ (by positivity)
      calc (S2 ^ 3) ^ 2 = (S2 ^ 2) ^ 3 := by ring
        _ ≤ (S1 * S3) ^ 3 := h1
        _ = S1 ^ 3 * S3 ^ 3 := h2
        _ ≤ ((k : ℝ) ^ 2 * S3) * S3 ^ 3 := h3
        _ = ((k : ℝ) * S3 ^ 2) ^ 2 := by ring
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
  have hfin : N ^ 3 ≤ Real.sqrt (k : ℝ) * S3 := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hsq : (N ^ 3) ^ 2 ≤ (Real.sqrt (k : ℝ) * S3) ^ 2 := by
      have hsk : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hknn
      calc (N ^ 3) ^ 2 = (N ^ 2) ^ 3 := by ring
        _ = S2 ^ 3 := by rw [hNsq]
        _ ≤ (k : ℝ) * S3 ^ 2 := hstep
        _ = (Real.sqrt (k : ℝ) * S3) ^ 2 := by rw [mul_pow, hsk]
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
  exact hfin

/-- The per-observation score vector `x ↦ (ψ₁ x, …, ψ_k x)`. -/
private noncomputable def psiVecK {k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (x : 𝓧) :
    EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => ψ j x)

private lemma measurable_psiVecK {k : ℕ} {ψ : Fin k → 𝓧 → ℝ} (hψ : ∀ j, Measurable (ψ j)) :
    Measurable (psiVecK ψ) :=
  (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp (measurable_pi_lambda _ hψ)

private lemma inner_eucl_sum {k : ℕ} (u w : EuclideanSpace ℝ (Fin k)) :
    ⟪u, w⟫_ℝ = ∑ i, u i * w i := by
  simp only [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

private lemma inner_psiVecK {k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (u : EuclideanSpace ℝ (Fin k))
    (x : 𝓧) : ⟪u, psiVecK ψ x⟫_ℝ = ∑ j, u j * ψ j x := by
  rw [inner_eucl_sum]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- **The Berry–Esseen inputs for the score law.** The law `ν = P₀ ∘ psiVec⁻¹` of the
per-observation score vector is centred, has identity covariance, and its third absolute
moment is finite and bounded by `k^{3/2} B`. -/
private lemma scoreLaw_facts {k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} {B : ℝ}
    (hψmeas : ∀ j, Measurable (ψ j))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    (hthirdint : ∀ j, Integrable (fun x => |ψ j x| ^ 3) P₀)
    (hthird : ∀ j, (∫ x, |ψ j x| ^ 3 ∂P₀) ≤ B) :
    (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂(P₀.map (psiVecK ψ))) = 0)
    ∧ (∀ u v : EuclideanSpace ℝ (Fin k),
        (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂(P₀.map (psiVecK ψ))) = ⟪u, v⟫_ℝ)
    ∧ Integrable (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3) (P₀.map (psiVecK ψ))
    ∧ (∫ y, ‖y‖ ^ 3 ∂(P₀.map (psiVecK ψ))) ≤ Real.sqrt (k : ℝ) * ((k : ℝ) * B) := by
  classical
  have hgmeas : Measurable (psiVecK ψ) := measurable_psiVecK hψmeas
  -- `L²` facts, exactly as in the fixed-`k` file
  have hsqint : ∀ i, Integrable (fun x => ψ i x ^ 2) P₀ := by
    intro i
    have h1 : (∫ x, ψ i x * ψ i x ∂P₀) = 1 := by rw [hortho i i]; simp
    simpa [sq] using integrable_of_integral_eq_one h1
  have hψL2 : ∀ i, MemLp (ψ i) 2 P₀ := fun i =>
    (memLp_two_iff_integrable_sq (hψmeas i).aestronglyMeasurable).2 (hsqint i)
  have hψint : ∀ i, Integrable (ψ i) P₀ := fun i => (hψL2 i).integrable one_le_two
  have hψψint : ∀ i j, Integrable (fun x => ψ i x * ψ j x) P₀ := fun i j => by
    simpa using (hψL2 i).integrable_mul (hψL2 j)
  -- the third-moment domination
  have hdom : ∀ x : 𝓧, ‖psiVecK ψ x‖ ^ 3 ≤ Real.sqrt (k : ℝ) * ∑ j, |ψ j x| ^ 3 := by
    intro x
    exact norm_cube_le_sqrt_card_mul (fun j => ψ j x)
  have hRint : Integrable (fun x => Real.sqrt (k : ℝ) * ∑ j, |ψ j x| ^ 3) P₀ :=
    (integrable_finset_sum _ (fun j _ => hthirdint j)).const_mul _
  have hcubeint : Integrable (fun x => ‖psiVecK ψ x‖ ^ 3) P₀ := by
    refine hRint.mono' ((hgmeas.norm.pow_const 3).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hdom x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    rw [integral_map hgmeas.aemeasurable (by fun_prop : Continuous
      fun y : EuclideanSpace ℝ (Fin k) => ⟪u, y⟫_ℝ).aestronglyMeasurable]
    have hpt : (fun x => ⟪u, psiVecK ψ x⟫_ℝ) = (fun x => ∑ j, u j * ψ j x) := by
      funext x; exact inner_psiVecK ψ u x
    rw [hpt, integral_finset_sum _ (fun j _ => (hψint j).const_mul (u j))]
    simp_rw [integral_const_mul, hcentred, mul_zero, Finset.sum_const_zero]
  · intro u v
    rw [integral_map hgmeas.aemeasurable (by fun_prop : Continuous
      fun y : EuclideanSpace ℝ (Fin k) => ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ).aestronglyMeasurable]
    have hpt : (fun x => ⟪u, psiVecK ψ x⟫_ℝ * ⟪v, psiVecK ψ x⟫_ℝ)
        = (fun x => ∑ i, ∑ j, (u i * v j) * (ψ i x * ψ j x)) := by
      funext x
      rw [inner_psiVecK, inner_psiVecK, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
    rw [hpt, integral_finset_sum _
      (fun i _ => integrable_finset_sum _ (fun j _ => (hψψint i j).const_mul (u i * v j)))]
    have hRHS : ⟪u, v⟫_ℝ = ∑ i, u i * v i := inner_eucl_sum u v
    rw [hRHS]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finset_sum _ (fun j _ => (hψψint i j).const_mul (u i * v j))]
    simp_rw [integral_const_mul, hortho i]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [if_neg (Ne.symm hji), mul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [if_pos rfl, mul_one]
  · rw [integrable_map_measure ((by fun_prop : Continuous
      fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3)).aestronglyMeasurable hgmeas.aemeasurable]
    exact hcubeint
  · rw [integral_map hgmeas.aemeasurable ((by fun_prop : Continuous
      fun y : EuclideanSpace ℝ (Fin k) => ‖y‖ ^ 3)).aestronglyMeasurable]
    refine le_trans (integral_mono hcubeint hRint (fun x => hdom x)) ?_
    rw [integral_const_mul, integral_finset_sum _ (fun j _ => hthirdint j)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc (∑ j, ∫ x, |ψ j x| ^ 3 ∂P₀) ≤ ∑ _j : Fin k, B :=
          Finset.sum_le_sum (fun j _ => hthird j)
      _ = (k : ℝ) * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The standardised score vector, whose squared norm is the smooth statistic. -/
private noncomputable def scoreVecK {n k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (X : Fin n → Ω → 𝓧)
    (ω : Ω) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => smoothScore ψ X j ω)

private lemma smoothStat_eq_norm_sq {n k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (X : Fin n → Ω → 𝓧)
    (ω : Ω) : smoothStat ψ X ω = ‖scoreVecK ψ X ω‖ ^ 2 := by
  rw [scoreVecK, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun j _ => by simp [smoothStat, Real.norm_eq_abs, sq_abs]

private lemma scoreVecK_eq_smul_sum {n k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (X : Fin n → Ω → 𝓧)
    (ω : Ω) :
    scoreVecK ψ X ω = (Real.sqrt (n : ℝ))⁻¹ • ∑ i : Fin n, psiVecK ψ (X i ω) := by
  rw [scoreVecK]
  simp only [psiVecK]
  rw [← WithLp.toLp_sum, ← WithLp.toLp_smul]
  refine congrArg (WithLp.toLp 2) ?_
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [smoothScore, div_eq_inv_mul]

private lemma measurable_scoreVecK {n k : ℕ} {ψ : Fin k → 𝓧 → ℝ} {X : Fin n → Ω → 𝓧}
    (hψmeas : ∀ j, Measurable (ψ j)) (hX : ∀ i, Measurable (X i)) :
    Measurable (scoreVecK ψ X) := by
  have hg : Measurable fun ω => (fun j => smoothScore ψ X j ω) :=
    measurable_pi_lambda _ fun j => by
      simp only [smoothScore]
      exact (Finset.univ.measurable_sum fun i _ => (hψmeas j).comp (hX i)).div measurable_const
  exact (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp hg

/-- **The stage-`n` law of the score vector is the standardised product law.** -/
private lemma law_scoreVecK {n k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin n → Ω → 𝓧}
    (hψmeas : ∀ j, Measurable (ψ j)) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = P₀) :
    P.map (scoreVecK ψ X)
      = (Measure.pi fun _ : Fin n => P₀.map (psiVecK ψ)).map
          (fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) := by
  classical
  have hgmeas : Measurable (psiVecK ψ) := measurable_psiVecK hψmeas
  haveI : IsProbabilityMeasure (P₀.map (psiVecK ψ)) :=
    Measure.isProbabilityMeasure_map hgmeas.aemeasurable
  set Ψ : (Fin n → EuclideanSpace ℝ (Fin k)) → EuclideanSpace ℝ (Fin k) :=
    fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i with hΨ
  have hΨcont : Continuous Ψ :=
    (continuous_finset_sum _ fun i _ => continuous_apply i).const_smul _
  have hXmeas : Measurable (fun ω (i : Fin n) => X i ω) :=
    measurable_pi_lambda _ (fun i => hX i)
  have hpsimeas : Measurable (fun (d : Fin n → 𝓧) (i : Fin n) => psiVecK ψ (d i)) :=
    measurable_pi_lambda _ (fun i => hgmeas.comp (measurable_pi_apply i))
  have hpiX : P.map (fun ω (i : Fin n) => X i ω) = Measure.pi (fun _ : Fin n => P₀) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).1 hindep]
    congr 1; funext i; exact hlaw i
  have hcomp : scoreVecK ψ X
      = Ψ ∘ ((fun (d : Fin n → 𝓧) (i : Fin n) => psiVecK ψ (d i))
          ∘ (fun ω (i : Fin n) => X i ω)) := by
    funext ω
    rw [scoreVecK_eq_smul_sum ψ X ω]
    rfl
  rw [hcomp, ← Measure.map_map hΨcont.measurable (hpsimeas.comp hXmeas),
    ← Measure.map_map hpsimeas hXmeas, hpiX, Measure.pi_map_pi (fun _ => hgmeas.aemeasurable)]

/-- The Gaussian ball probability is the chi-squared distribution function. -/
private lemma gaussian_ball_eq_chiSquared {k : ℕ} (hk : 0 < k) (t : ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) {z | ‖z‖ ^ 2 ≤ t}
      = chiSquared k (Set.Iic t) := by
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Matrix (Fin k) (Fin k) ℝ)⁻¹ with hTdef
  set q : EuclideanSpace ℝ (Fin k) → ℝ := fun z => ⟪z, T z⟫_ℝ with hqdef
  have hq_cont : Continuous q := continuous_id.inner T.continuous
  have hqval : ∀ z : EuclideanSpace ℝ (Fin k), q z = ‖z‖ ^ 2 := by
    intro z
    simp only [hqdef, hTdef]
    rw [Matrix.inner_toEuclideanCLM, inv_one, Matrix.one_mulVec, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs, sq]
  have htarget : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
      (1 : Matrix (Fin k) (Fin k) ℝ)).map q = chiSquared k := by
    simp only [hqdef, hTdef]
    exact multivariateGaussian_map_inner_inv_eq_chiSquared hk Matrix.PosDef.one
  rw [← htarget, Measure.map_apply hq_cont.measurable measurableSet_Iic]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq, hqval]

/-- The distribution function of the standardised chi-squared law. -/
private lemma chiSquared_standardized_Iic {k : ℕ} (hk : 0 < k) (x : ℝ) :
    ((chiSquared k).map (fun s => (s - (k : ℝ)) / Real.sqrt (2 * (k : ℝ)))) (Set.Iic x)
      = chiSquared k (Set.Iic ((k : ℝ) + x * Real.sqrt (2 * (k : ℝ)))) := by
  have hsk : (0 : ℝ) < Real.sqrt (2 * (k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext s
  simp only [Set.mem_preimage, Set.mem_Iic, div_le_iff₀ hsk]
  constructor <;> intro h <;> linarith


private lemma measurable_smoothStat {n k : ℕ} {ψ : Fin k → 𝓧 → ℝ} {X : Fin n → Ω → 𝓧}
    (hψmeas : ∀ j, Measurable (ψ j)) (hX : ∀ i, Measurable (X i)) :
    Measurable (smoothStat ψ X) :=
  Finset.univ.measurable_sum fun j _ =>
    ((Finset.univ.measurable_sum fun i _ =>
      (hψmeas j).comp (hX i)).div measurable_const).pow_const 2

/-- **The stage-`n` Berry–Esseen comparison.** The distribution function of the standardised
smooth statistic differs from that of the standardised `χ²_k` by at most
`C (k^{3/2}B/√n)^{1/4}`. -/
private lemma cdf_close {n k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin n → Ω → 𝓧}
    {B C : ℝ} (hCnn : 0 ≤ C) (hn : 0 < n) (hk : 0 < k)
    (hψmeas : ∀ j, Measurable (ψ j))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    (hthirdint : ∀ j, Integrable (fun x => |ψ j x| ^ 3) P₀)
    (hthird : ∀ j, (∫ x, |ψ j x| ^ 3 ∂P₀) ≤ B)
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = P₀)
    (hBE : ∀ (k n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin k))) (t : ℝ),
      0 < n → 0 < k → IsProbabilityMeasure ν →
      (∀ u : EuclideanSpace ℝ (Fin k), (∫ y, ⟪u, y⟫_ℝ ∂ν) = 0) →
      (∀ u v : EuclideanSpace ℝ (Fin k),
        (∫ y, ⟪u, y⟫_ℝ * ⟪v, y⟫_ℝ ∂ν) = ⟪u, v⟫_ℝ) →
      Integrable (fun y => ‖y‖ ^ 3) ν →
      |((((Measure.pi fun _ : Fin n => ν)).map
            fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) {z | ‖z‖ ^ 2 ≤ t}).toReal
          - ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
              {z | ‖z‖ ^ 2 ≤ t}).toReal|
        ≤ C * ((∫ y, ‖y‖ ^ 3 ∂ν) / Real.sqrt (n : ℝ)) ^ ((1 : ℝ) / 4))
    (x : ℝ) :
    |((P.map (fun ω => (smoothStat ψ X ω - (k : ℝ)) / Real.sqrt (2 * (k : ℝ))))
          (Set.Iic x)).toReal
        - (chiSquared k (Set.Iic ((k : ℝ) + x * Real.sqrt (2 * (k : ℝ))))).toReal|
      ≤ C * ((Real.sqrt (k : ℝ) * ((k : ℝ) * B)) / Real.sqrt (n : ℝ)) ^ ((1 : ℝ) / 4) := by
  classical
  have hgmeas : Measurable (psiVecK ψ) := measurable_psiVecK hψmeas
  haveI hνprob : IsProbabilityMeasure (P₀.map (psiVecK ψ)) :=
    Measure.isProbabilityMeasure_map hgmeas.aemeasurable
  obtain ⟨hmean, hcov, hβint, hβle⟩ :=
    scoreLaw_facts (B := B) hψmeas hortho hcentred hthirdint hthird
  set t : ℝ := (k : ℝ) + x * Real.sqrt (2 * (k : ℝ)) with ht
  have hball : MeasurableSet {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have hsk : (0 : ℝ) < Real.sqrt (2 * (k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hSmeas : Measurable (smoothStat ψ X) := measurable_smoothStat hψmeas hX
  have hcdf : (P.map (fun ω => (smoothStat ψ X ω - (k : ℝ)) / Real.sqrt (2 * (k : ℝ))))
        (Set.Iic x)
      = ((Measure.pi fun _ : Fin n => P₀.map (psiVecK ψ)).map
          fun y => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i) {z | ‖z‖ ^ 2 ≤ t} := by
    rw [Measure.map_apply ((hSmeas.sub measurable_const).div measurable_const)
      measurableSet_Iic]
    have hset : (fun ω => (smoothStat ψ X ω - (k : ℝ)) / Real.sqrt (2 * (k : ℝ)))
          ⁻¹' Set.Iic x
        = (scoreVecK ψ X) ⁻¹' {z : EuclideanSpace ℝ (Fin k) | ‖z‖ ^ 2 ≤ t} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq, div_le_iff₀ hsk,
        ← smoothStat_eq_norm_sq]
      rw [ht]
      constructor <;> intro hh <;> linarith
    rw [hset, ← Measure.map_apply (measurable_scoreVecK hψmeas hX) hball,
      law_scoreVecK hψmeas hX hindep hlaw]
  rw [hcdf, ← gaussian_ball_eq_chiSquared hk t]
  refine le_trans (hBE k n (P₀.map (psiVecK ψ)) t hn hk hνprob hmean hcov hβint) ?_
  refine mul_le_mul_of_nonneg_left ?_ hCnn
  have hβnn : (0 : ℝ) ≤ ∫ y, ‖y‖ ^ 3 ∂(P₀.map (psiVecK ψ)) :=
    integral_nonneg fun y => by positivity
  have hsnpos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
  gcongr

end GrowingK

/-! ### The normal limit of the smooth statistic with `kₙ → ∞` -/

/-- **Normal limit of the smooth statistic with a growing number of score directions.**
Let `ψ₁, ψ₂, …` be an infinite orthonormal system in `L²(P₀)`, orthogonal to the constants,
with uniformly bounded third absolute moments `sup_j E_{P₀}|ψⱼ(X)|³ = B < ∞`. If
`kₙ → ∞` and `kₙ³/n → 0`, then under the null hypothesis
$$ \frac{S_{n,k_n} - k_n}{(2 k_n)^{1/2}} \;\Longrightarrow\; N(0,1). $$

Both growth conditions are the source's, transcribed unchanged; `kₙ³/n → 0` is exactly
what makes the ball Berry–Esseen error `C B kₙ^{3/2} n^{-1/2}` vanish, and `kₙ → ∞` is
what makes the chi-squared law with `kₙ` degrees of freedom normal in the limit. The proof
consumes `bentkus_berry_esseen_ball`.

**AMENDMENT (forced, minimal): `hthirdint` added.** The source hypothesis is
`sup_j E_{P₀}|ψⱼ(X)|³ = B < ∞`, which asserts *finiteness* of the third absolute moments.
Its frozen Lean transcription `hthird : ∀ j, ∫|ψⱼ|³ ∂P₀ ≤ B` does not: the Bochner
integral of a non-integrable function is the junk value `0`, so `hthird` is satisfied
vacuously (with `B = 0`) by a system with infinite third moments, for which the
Berry–Esseen bound — and, in all likelihood, the conclusion — fails. The integrability
hypothesis `hthirdint : ∀ j, Integrable (fun x => |ψⱼ x|³) P₀` restores exactly the content
of `E|ψⱼ|³ < ∞` and nothing more; it is what makes `Integrable (‖·‖³) ν` available, which
`bentkus_berry_esseen_ball` requires. `hthird` is kept unchanged.

**Proof.** Under the null the per-observation score vectors `psiVec x = (ψ₁x, …, ψ_{kₙ}x)`
are i.i.d. with law `ν = P₀ ∘ psiVec⁻¹`, centred with identity covariance
(`scoreLaw_facts`), and `β = ∫‖y‖³ dν ≤ kₙ^{3/2} B` by the sharp `ℓ³ ⊂ ℓ²` bound
`norm_cube_le_sqrt_card_mul` (Cauchy–Schwarz plus Jensen; the exponent `3/2` is what makes
`kₙ³/n → 0` suffice). The law of `scoreVec` is the standardised product law
(`law_scoreVecK`) and `Sₙ = ‖scoreVec‖²`, so `bentkus_berry_esseen_ball` compares the
distribution function of `Sₙ` with that of `χ²_{kₙ}` uniformly, with error
`C (β/√n)^{1/4} → 0`. The standardising affine map transports this to the distribution
functions of `(Sₙ − kₙ)/√(2kₙ)` and of the standardised `χ²_{kₙ}`, the latter converging to
`Φ` by `weakConverges_chiSquared_standardized` and portmanteau. Pointwise convergence of the
distribution functions is turned back into weak convergence by `weakConverges_of_tendsto_cdf`,
the Helly–Bray inversion built above from Mathlib's π-system criterion. -/
theorem smoothStat_largeK_weakConverges_gaussian {Ω 𝓧 : Type*} [MeasurableSpace Ω]
    [MeasurableSpace 𝓧] {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀] {ψ : ℕ → 𝓧 → ℝ}
    {kseq : ℕ → ℕ} {B : ℝ} {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → 𝓧}
    -- USER-INPUT: the score functions are measurable
    (hψmeas : ∀ j, Measurable (ψ j))
    -- USER-INPUT: the score functions are orthonormal in `L²(P₀)`; Neyman 1937
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    -- USER-INPUT: the score functions are orthogonal to the constants, i.e. `E₀ψⱼ = 0`
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    -- USER-INPUT: the third absolute moments are finite (see the AMENDMENT note in the
    -- docstring: `∫|ψⱼ|³ ≤ B` alone does not say so, because a non-integrable integrand
    -- makes the Bochner integral the junk value `0`)
    (hthirdint : ∀ j, Integrable (fun x => |ψ j x| ^ 3) P₀)
    -- USER-INPUT: uniformly bounded third absolute moments; Bentkus 2003 is applied
    -- through this bound
    (hthird : ∀ j, (∫ x, |ψ j x| ^ 3 ∂P₀) ≤ B)
    -- USER-INPUT: the number of score directions diverges
    (hkinf : Tendsto kseq atTop atTop)
    -- USER-INPUT: it diverges slowly enough: `kₙ³/n → 0`
    (hkgrowth : Tendsto (fun n => (kseq n : ℝ) ^ 3 / (n : ℝ)) atTop (nhds 0))
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the observations are i.i.d.; Neyman 1937
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: the null hypothesis: every observation has law `P₀`
    (hlaw : ∀ n, ∀ i, (P n).map (X n i) = P₀) :
    WeakConverges
      (fun n => (P n).map fun ω =>
        (smoothStat (fun j : Fin (kseq n) => ψ (j : ℕ)) (X n) ω - (kseq n : ℝ))
          / Real.sqrt (2 * (kseq n : ℝ)))
      (gaussianReal 0 1) := by
  classical
  obtain ⟨C, hCpos, hBE⟩ := bentkus_berry_esseen_ball
  have hmapmeas : ∀ n : ℕ, Measurable (fun ω =>
      (smoothStat (fun j : Fin (kseq n) => ψ (j : ℕ)) (X n) ω - (kseq n : ℝ))
        / Real.sqrt (2 * (kseq n : ℝ))) := fun n =>
    ((measurable_smoothStat (fun j => hψmeas (j : ℕ)) (hX n)).sub
      measurable_const).div measurable_const
  haveI hμprob : ∀ n : ℕ, IsProbabilityMeasure ((P n).map fun ω =>
      (smoothStat (fun j : Fin (kseq n) => ψ (j : ℕ)) (X n) ω - (kseq n : ℝ))
        / Real.sqrt (2 * (kseq n : ℝ))) := fun n =>
    Measure.isProbabilityMeasure_map (hmapmeas n).aemeasurable
  refine weakConverges_of_tendsto_cdf ?_
  intro x
  -- (1) the standardised chi-squared distribution function converges to `Φ`
  set ρ : ℕ → Measure ℝ := fun k => if k = 0 then gaussianReal 0 1
    else (chiSquared k).map (fun s => (s - (k : ℝ)) / Real.sqrt (2 * (k : ℝ))) with hρ
  have hρeq : ∀ k : ℕ, 0 < k →
      ρ k = (chiSquared k).map (fun s => (s - (k : ℝ)) / Real.sqrt (2 * (k : ℝ))) := by
    intro k hk; simp only [hρ, if_neg hk.ne']
  have hρprob : ∀ k, IsProbabilityMeasure (ρ k) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [hρ, if_pos rfl]; infer_instance
    · haveI : NeZero k := ⟨hk.ne'⟩
      rw [hρeq k hk]
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  set ρs : ℕ → ProbabilityMeasure ℝ := fun k => ⟨ρ k, hρprob k⟩ with hρs
  set ν' : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩ with hν'
  haveI hnoatom : NoAtoms (ν' : Measure ℝ) := by
    change NoAtoms (gaussianReal 0 1)
    exact noAtoms_gaussianReal one_ne_zero
  have htend : Tendsto ρs atTop (𝓝 ν') := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    have hA := weakConverges_chiSquared_standardized f
    simp only [hρs, hν', ProbabilityMeasure.coe_mk]
    refine hA.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    rw [hρeq k hk]
  have hfront : (ν' : Measure ℝ) (frontier (Set.Iic x)) = 0 := by
    rw [frontier_Iic]; exact measure_singleton x
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    htend (E := Set.Iic x) hfront
  have hportR : Tendsto (fun k => (ρ k (Set.Iic x)).toReal) atTop
      (𝓝 ((gaussianReal 0 1 (Set.Iic x)).toReal)) := by
    have := (ENNReal.tendsto_toReal (measure_ne_top (ν' : Measure ℝ) (Set.Iic x))).comp hport
    simpa only [hρs, hν', ProbabilityMeasure.coe_mk, Function.comp] using this
  have hGk : Tendsto (fun n : ℕ => (ρ (kseq n) (Set.Iic x)).toReal) atTop
      (𝓝 ((gaussianReal 0 1 (Set.Iic x)).toReal)) := hportR.comp hkinf
  have hGlim : Tendsto (fun n : ℕ => (chiSquared (kseq n)
        (Set.Iic ((kseq n : ℝ) + x * Real.sqrt (2 * (kseq n : ℝ))))).toReal) atTop
      (𝓝 ((gaussianReal 0 1 (Set.Iic x)).toReal)) := by
    refine hGk.congr' ?_
    filter_upwards [hkinf.eventually_gt_atTop 0] with n hn
    rw [hρeq (kseq n) hn]
    exact congrArg ENNReal.toReal (chiSquared_standardized_Iic hn x)
  -- (2) the Berry–Esseen error vanishes
  have hbase : Tendsto (fun n : ℕ =>
      (Real.sqrt (kseq n : ℝ) * ((kseq n : ℝ) * B)) / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt ((kseq n : ℝ) ^ 3 / (n : ℝ))) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hkgrowth
      rw [Real.sqrt_zero] at h
      exact h
    have h2 := h1.const_mul B
    rw [mul_zero] at h2
    refine h2.congr (fun n => ?_)
    have hsq : Real.sqrt ((kseq n : ℝ) ^ 3 / (n : ℝ))
        = Real.sqrt (kseq n : ℝ) * (kseq n : ℝ) / Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_div (by positivity),
        show ((kseq n : ℝ)) ^ 3 = ((kseq n : ℝ)) ^ 2 * (kseq n : ℝ) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      ring
    rw [hsq]; ring
  have he0 : Tendsto (fun n : ℕ => C *
      ((Real.sqrt (kseq n : ℝ) * ((kseq n : ℝ) * B)) / Real.sqrt (n : ℝ)) ^ ((1 : ℝ) / 4))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun y : ℝ => y ^ ((1 : ℝ) / 4)) (𝓝 0) (𝓝 0) := by
      have hct := (Real.continuousAt_rpow_const (0 : ℝ) ((1 : ℝ) / 4)
        (Or.inr (by norm_num))).tendsto
      rwa [Real.zero_rpow (by norm_num)] at hct
    have := (hc.comp hbase).const_mul C
    rwa [mul_zero] at this
  -- (3) the Berry–Esseen comparison, eventually
  have hclose : ∀ᶠ n : ℕ in atTop,
      ‖(((P n).map fun ω =>
            (smoothStat (fun j : Fin (kseq n) => ψ (j : ℕ)) (X n) ω - (kseq n : ℝ))
              / Real.sqrt (2 * (kseq n : ℝ))) (Set.Iic x)).toReal
        - (chiSquared (kseq n)
            (Set.Iic ((kseq n : ℝ) + x * Real.sqrt (2 * (kseq n : ℝ))))).toReal‖
      ≤ C * ((Real.sqrt (kseq n : ℝ) * ((kseq n : ℝ) * B))
          / Real.sqrt (n : ℝ)) ^ ((1 : ℝ) / 4) := by
    filter_upwards [eventually_gt_atTop 0, hkinf.eventually_gt_atTop 0] with n hn hkn
    rw [Real.norm_eq_abs]
    refine cdf_close hCpos.le hn hkn (fun j => hψmeas (j : ℕ)) ?_ (fun j => hcentred (j : ℕ))
      (fun j => hthirdint (j : ℕ)) (fun j => hthird (j : ℕ)) (hX n) (hindep n) (hlaw n) hBE x
    intro i j
    rw [hortho (i : ℕ) (j : ℕ)]
    simp [Fin.val_inj]
  -- (4) squeeze
  have hdiff : Tendsto (fun n : ℕ =>
      (((P n).map fun ω =>
          (smoothStat (fun j : Fin (kseq n) => ψ (j : ℕ)) (X n) ω - (kseq n : ℝ))
            / Real.sqrt (2 * (kseq n : ℝ))) (Set.Iic x)).toReal
        - (chiSquared (kseq n)
            (Set.Iic ((kseq n : ℝ) + x * Real.sqrt (2 * (kseq n : ℝ))))).toReal) atTop
      (𝓝 0) := squeeze_zero_norm' hclose he0
  have hsum := hGlim.add hdiff
  rw [add_zero] at hsum
  exact hsum.congr (fun n => by ring)


end StatLean.HypothesisTesting
