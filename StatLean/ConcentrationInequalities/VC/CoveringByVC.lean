import StatLean.ConcentrationInequalities.VC.SauerShelah
import StatLean.ConcentrationInequalities.VC.DimensionReduction
import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Covering numbers via VC dimension (Theorem 8.3.13)

For a class $\mathcal{C}$ of measurable sets with
$\mathrm{vc}(\mathcal{C}) \le d$ ($d \ge 1$), *every* probability measure
$\mu$, and every $0 < \varepsilon < 1$:
$$ \mathcal{N}\bigl(\mathcal{C}, L^2(\mu), \varepsilon\bigr)
   \;\le\; \Bigl(\frac{2}{\varepsilon}\Bigr)^{21 d}, $$
in the squared-distance encoding
$\|\mathbf{1}_S - \mathbf{1}_T\|_{L^2(\mu)}^2 = \mu(S \bigtriangleup T)$
(net radius $\varepsilon \iff$ measure $\le \varepsilon^2$, separation
$\iff > \varepsilon^2$). Packing form: any $\varepsilon$-separated
subfamily has at most $(2/\varepsilon)^{21d}$ members. Euclidean form: the
$(\sqrt n)^{-1}$-scaled empirical projection of $\mathcal{C}$ has covering
number at most $\lfloor(2/\varepsilon)^{21d}\rfloor$ — valid for the random
empirical measure precisely because the theorem holds for *every* $\mu$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.5, Theorem 8.3.13 (including footnote 4)
and the empirical-projection reading of §8.3.6.

**Proof formalization notes.** No `PseudoMetricSpace` instance is put on the
class for general `μ` (a Bochner integral of a non-`L²` difference is junk
`0`, breaking the triangle inequality), so the general-`μ` statements use
explicit `μ.real (S ∆ T)` nets/separation; the instance-based
`coveringNumber` appears only for the Euclidean `empProj`. Spine of the
packing bound: instantiate the CANONICAL i.i.d. witness
`Ξ := ℕ → Ω`, `P := Measure.infinitePi (fun _ => μ)`, `X i := Function.eval
i` (via `iIndepFun_infinitePi` / `infinitePi_map_eval`), apply
`dimension_reduction` (a good sample exists since `P(bad) ≤ 1/100 < 1`),
extract ≥ `N` distinct traces on the good sample, and count them by
Sauer–Shelah (`card_traceFamily_le_pow`). The by-contradiction algebra of
footnote 4 is isolated as the pure-real `card_le_pow_of_entropy_bound` with
a quantified-over-`n` hypothesis; assuming `N > (2/ε)^{21d}` also yields
`n > 1400·d ≥ d`, discharging the `d ≤ n` side condition — the book's
unstated regime assumption. The `21`: `N ≤ (400e·ε⁻⁴)^{2d}` (from
`n ≤ 2·100·ε⁻⁴·log N` and `log N ≤ 2d·N^{1/(2d)}`) plus `(400e)² ≤ 2^21`
and `ε < 1`; closable by `nlinarith` with `Real.exp_one_lt_d9`. The
class-level net form is a maximal-cardinality separated family (bounded by
the packing bound, so a maximum exists; maximality makes it a net by
insert-contradiction) — no Zorn, no `Metric.packingNumber`. The two
`private` lemmas duplicate ~15 lines of `AsymptoticStatistics` empirical-
measure content (deliberate: importing another area's concept layer is
forbidden); documented for future promotion to a shared `ForMathlib`.
Named-sorry fallback of this work item: `card_le_pow_of_entropy_bound`
(the footnote-4 algebra); the probabilistic/combinatorial spine
`sepFamily_card_le_of_vcDim_le` must close against it.

**Bibliographic comments.** Covering numbers of VC classes are due to
R. M. Dudley, "Central limit theorems for empirical measures," *Ann.
Probab.* 6 (1978), 899–929, with the sharp exponent later obtained by
D. Haussler, "Sphere packing numbers for subsets of the Boolean n-cube with
bounded Vapnik–Chervonenkis dimension," *J. Combin. Theory Ser. A* 69
(1995), 217–232; HDP §8.3.5 presents the (non-sharp) exponent-`Cd` version
formalized here. See HDP §8.3 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal symmDiff

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Footnote-4 algebra of Theorem 8.3.13 (HDP §8.3.5), isolated as pure real
analysis: if every `n ≥ 100·ε⁻⁴·log N` forces `N ≤ (e·n/d)^d`, then
`N ≤ (2/ε)^{21d}`. The `21` absorbs `(400e)² ≤ 2^21` and `ε < 1`. -/
lemma card_le_pow_of_entropy_bound {N d : ℕ} {ε : ℝ}
    -- USER-INPUT: 1 ≤ d (nondegenerate VC dimension); HDP §8.3.5,
    -- Theorem 8.3.13.
    (hd1 : 1 ≤ d)
    -- USER-INPUT: 0 < ε < 1 (the theorem's radius regime); HDP §8.3.5,
    -- Theorem 8.3.13.
    (hε : 0 < ε) (hε1 : ε < 1)
    -- LEAN-ONLY: the quantified-over-n Sauer–Shelah input, exactly what the
    -- probabilistic spine produces; isolates the footnote-4 algebra from
    -- probability and combinatorics.
    (hN : ∀ n : ℕ, 100 * ε⁻¹ ^ 4 * Real.log N ≤ n →
      (N : ℝ) ≤ (Real.exp 1 * n / d) ^ d) :
    (N : ℝ) ≤ (2 / ε) ^ (21 * d) := by
  sorry

/-- **Covering numbers via VC dimension, packing form** (HDP §8.3.5,
Theorem 8.3.13, the core): any `ε`-separated subfamily (squared form
`μ(S ∆ T) > ε²`) of a class with `vc ≤ d` has at most `(2/ε)^{21d}`
members, for every probability measure `μ`. -/
theorem sepFamily_card_le_of_vcDim_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {C : Set (Set Ω)}
    -- LEAN-ONLY: measurability of the class members (implicit in the book's
    -- Boolean functions on a probability space).
    (hCmeas : ∀ S ∈ C, MeasurableSet S)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.5, Theorem 8.3.13.
    (hd : vcDim C ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.3.5 (regime of Exercise 0.6 / Lemma 8.3.9).
    (hd1 : 1 ≤ d)
    {ε : ℝ}
    -- USER-INPUT: radius regime 0 < ε < 1; HDP §8.3.5, Theorem 8.3.13.
    (hε : 0 < ε) (hε1 : ε < 1)
    {F : Finset (Set Ω)}
    -- USER-INPUT: the separated subfamily lies in the class; HDP §8.3.5.
    (hFC : ↑F ⊆ C)
    -- USER-INPUT: ε-separation in L²(μ), squared form; HDP §8.3.5,
    -- Theorem 8.3.13.
    (hsep : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → ε ^ 2 < μ.real (S ∆ T)) :
    (F.card : ℝ) ≤ (2 / ε) ^ (21 * d) := by
  sorry

/-- **Covering numbers via VC dimension, net form** (HDP §8.3.5,
Theorem 8.3.13): `𝒩(C, L²(μ), ε) ≤ (2/ε)^{21d}` — an internal `ε`-net
(squared form `μ(S ∆ T) ≤ ε²`) of the stated cardinality exists. Proof: a
maximal-cardinality `ε`-separated subfamily (which exists since
cardinalities are bounded by the packing form) is a net by
insert-contradiction. -/
theorem exists_L2_net_of_vcDim_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {C : Set (Set Ω)}
    -- LEAN-ONLY: measurability of the class members; as in the packing form.
    (hCmeas : ∀ S ∈ C, MeasurableSet S)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.5, Theorem 8.3.13.
    (hd : vcDim C ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.3.5.
    (hd1 : 1 ≤ d)
    {ε : ℝ}
    -- USER-INPUT: radius regime 0 < ε < 1; HDP §8.3.5, Theorem 8.3.13.
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ N : Finset (Set Ω), ↑N ⊆ C ∧ (N.card : ℝ) ≤ (2 / ε) ^ (21 * d) ∧
      ∀ S ∈ C, ∃ T ∈ N, μ.real (S ∆ T) ≤ ε ^ 2 := by
  sorry

/-- **Empirical projection** (LEAN-ONLY carrier for the empirical `L²(μ_n)`
geometry of HDP §8.3.6): `v_S = (√n)⁻¹ · (𝟙_S(x_i))_{i < n} ∈ ℝⁿ`, built as
a sum of `EuclideanSpace.single`s (defeq-safe at the pin). Then
`dist(v_S, v_T)² = empFrac x (S ∆ T) = ‖𝟙_S − 𝟙_T‖²_{L²(μ_n)}` exactly.
Edge behavior: `n = 0` gives the empty vector; the `(√0)⁻¹ = 0` junk is
multiplied into an empty sum. -/
noncomputable def empProj {n : ℕ} (x : Fin n → Ω) (S : Set Ω) :
    EuclideanSpace ℝ (Fin n) :=
  ∑ i, EuclideanSpace.single i
    ((Real.sqrt n)⁻¹ * S.indicator (fun _ => (1 : ℝ)) (x i))

/-- Coordinates of the empirical projection (LEAN-ONLY:
`EuclideanSpace.single_apply` bookkeeping). -/
@[simp] lemma empProj_apply {n : ℕ} (x : Fin n → Ω) (S : Set Ω) (i : Fin n) :
    empProj x S i = (Real.sqrt n)⁻¹ * S.indicator (fun _ => (1 : ℝ)) (x i) := by
  sorry

/-- The empirical projection is an exact (squared) isometry onto the
empirical `L²` geometry (LEAN-ONLY: `EuclideanSpace.dist_eq` + indicator
algebra `(𝟙_S − 𝟙_T)² = 𝟙_{S ∆ T}`). -/
lemma dist_empProj_sq {n : ℕ} [NeZero n] (x : Fin n → Ω) (S T : Set Ω) :
    dist (empProj x S) (empProj x T) ^ 2 = empFrac x (S ∆ T) := by
  sorry

/-- The `(n : ℝ≥0∞)⁻¹ • ∑ dirac` empirical measure is a probability measure
(LEAN-ONLY: local duplicate of `AsymptoticStatistics` content — deliberate
non-import of another area's concept layer; candidate for promotion to a
shared `ForMathlib`). -/
private lemma isProbabilityMeasure_avg_dirac {n : ℕ} [NeZero n]
    (x : Fin n → Ω) :
    IsProbabilityMeasure
      ((n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (x i)) := by
  sorry

/-- On measurable sets, the averaged-dirac empirical measure evaluates to
`empFrac` (LEAN-ONLY bridge; see `isProbabilityMeasure_avg_dirac`). -/
private lemma avg_dirac_real_eq_empFrac {n : ℕ} [NeZero n] (x : Fin n → Ω)
    {S : Set Ω}
    -- LEAN-ONLY: measurability so `Measure.dirac` evaluates by membership.
    (hS : MeasurableSet S) :
    ((n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (x i)).real S
      = empFrac x S := by
  sorry

/-- **Covering number of the empirical projection** (HDP §8.3.5–8.3.6:
Theorem 8.3.13 applied to the empirical measure `μ_n` — the KEY SUBTLETY is
that the theorem holds for *every* probability measure, hence for the random
`μ_n(ω)` with a sample-independent right-hand side):
`𝒩(empProj x '' C, ε) ≤ ⌊(2/ε)^{21d}⌋` in `EuclideanSpace ℝ (Fin n)`.
Transported from `exists_L2_net_of_vcDim_le` at `μ := μ_n` via
`dist_empProj_sq` and `Metric.IsCover.coveringNumber_le_encard`. -/
theorem coveringNumber_empProj_le {n : ℕ} [NeZero n] (x : Fin n → Ω)
    {C : Set (Set Ω)}
    -- LEAN-ONLY: measurability of the class members; needed for the dirac
    -- `.real` evaluation, no scope change.
    (hCmeas : ∀ S ∈ C, MeasurableSet S)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.5, Theorem 8.3.13.
    (hd : vcDim C ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.3.5.
    (hd1 : 1 ≤ d)
    {ε : ℝ}
    -- USER-INPUT: radius regime 0 < ε < 1; HDP §8.3.5, Theorem 8.3.13.
    (hε : 0 < ε) (hε1 : ε < 1) :
    coveringNumber (empProj x '' C) ε ≤ (⌊(2 / ε) ^ (21 * d)⌋₊ : ℕ∞) := by
  sorry

end StatLean.ConcentrationInequalities
