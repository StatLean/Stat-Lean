import StatLean.ConcentrationInequalities.EmpiricalProcess.LipschitzNet
import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Lipschitz approximation by the grid net — Exercise 8.9, part 2

Every member $f$ of the Lipschitz class $\mathcal{F}$ (HDP Eq. (8.24)) is
within $L^\infty$-distance $3/m$ of the cone envelope built from its
floor-snapped knot values:
$$ \Bigl\| f - \mathrm{cone}\bigl(\lfloor m f(t_j) \rfloor / m\bigr)
   \Bigr\|_\infty \;\le\; \frac{3}{m},
   \qquad t_j = \frac{j}{m}, $$
packaged as: the grid net `lipschitzNet m` is an $\varepsilon$-net of
$\mathcal{F}$ whenever $m \ge 3/\varepsilon$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2, Exercise 8.9.

**Proof formalization notes.** Approximation error $3/m$ (not the optimal
$2/m$): floor-knot error $1/m$ (we snap $x$ to $\lfloor mx \rfloor / m$, a
simpler `Nat.floor` proof than nearest-knot) + value-snap error $1/m$
($k_j = \lfloor m f(t_j) \rfloor$, so $0 \le f(t_j) - k_j/m < 1/m$) + cone
offset $1/m$. The $\pm 1$-step property of the snapped values comes from
1-Lipschitz-ness + `Nat.floor_add_one`; the reconstruction of the snapped
values as a `gridPath` is a telescoping induction kept entirely in `ℤ` (no
truncated `ℕ`-subtraction). `snapStep` decodes the increment
$k_{i+1} - k_i + 1 \in \{0,1,2\}$ by trichotomy; on non-class members the
clamps make it total but carry no claim (`gridPath_snapStep_eq` is stated
only for class members). Covering is closed via our `IsEpsilonNet` bridge
(`IsEpsilonNet.isCover` + `Metric.IsCover.coveringNumber_le_encard`) — not
the packing route. Named-sorry fallback of the work item `hdp-emp-approx`:
`exists_mem_lipschitzNet_dist_le` (all downstream statements compile against
it).

**Bibliographic comments.** The knot-snapping argument is the classical
Kolmogorov–Tikhomirov (1959) upper bound for the ε-entropy of Lipschitz
balls; the exercise form is HDP Exercise 8.9 (see HDP §8 Notes).
-/

open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

/-- Every point of `[0,1]` is within `1/m` of a grid knot (take
`j = ⌊m·x⌋₊`); HDP Exercise 8.9. -/
theorem exists_gridKnot_dist_le (m : ℕ) [NeZero m] (x : unitInterval) :
    ∃ j : Fin (m + 1), |(x : ℝ) - (j : ℝ) / m| ≤ 1 / m := by
  sorry

/-- **Snapped knot values** `k_j = ⌊m·f(t_j)⌋₊` (HDP Exercise 8.9). Edge
behavior: `Nat.floor` sends negative reals to `0`, harmless since class
members are nonnegative; for `f ∉ 𝓕` the value is total garbage but never
used. -/
noncomputable def snapPath (m : ℕ) [NeZero m] (f : C(unitInterval, ℝ))
    (j : Fin (m + 1)) : ℕ :=
  ⌊(m : ℝ) * f (gridKnot m j)⌋₊

/-- The snapped start `k₀`, clamped into `Fin (m+1)` (LEAN-ONLY total clamp;
the clamp is the identity on class members since `k₀ ≤ m` by `snapPath_le`). -/
noncomputable def snapStart (m : ℕ) [NeZero m] (f : C(unitInterval, ℝ)) :
    Fin (m + 1) :=
  ⟨min (snapPath m f 0) m, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The snapped step sequence: encodes `k_{i+1} − k_i + 1 ∈ {0,1,2}` by
trichotomy in `ℤ` (HDP Exercise 8.9). Edge behavior: total on all of
`C(unitInterval, ℝ)`; increments of magnitude `≥ 2` (impossible on class
members by `snapPath_step_le`) are clamped to the extreme codes `0` / `2`. -/
noncomputable def snapStep (m : ℕ) [NeZero m] (f : C(unitInterval, ℝ))
    (i : Fin m) : Fin 3 :=
  if (snapPath m f i.succ : ℤ) < (snapPath m f i.castSucc : ℤ) then 0
  else if (snapPath m f i.succ : ℤ) = (snapPath m f i.castSucc : ℤ) then 1
  else 2

/-- Snapped values stay in `{0, …, m}` on the class (from `f ≤ 1`);
HDP Exercise 8.9. -/
theorem snapPath_le (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership; HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (j : Fin (m + 1)) :
    snapPath m f j ≤ m := by
  sorry

/-- Value-snap error: `|f(t_j) − k_j/m| ≤ 1/m` (HDP Exercise 8.9). -/
theorem abs_snapPath_sub_le (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership (nonnegativity feeds `Nat.floor`); HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (j : Fin (m + 1)) :
    |f (gridKnot m j) - (snapPath m f j : ℝ) / m| ≤ 1 / m := by
  sorry

/-- **±1-step property**: consecutive snapped values differ by at most `1`
(1-Lipschitz on a `1/m` grid + `Nat.floor_add_one`); HDP Exercise 8.9. -/
theorem snapPath_step_le (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership (the 1-Lipschitz bound); HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (i : Fin m) :
    |((snapPath m f i.succ : ℤ) - (snapPath m f i.castSucc : ℤ))| ≤ 1 := by
  sorry

/-- **Path reconstruction**: the grid path driven by the snapped start and
steps recovers the snapped values exactly (telescoping induction in `ℤ`);
HDP Exercise 8.9. -/
theorem gridPath_snapStep_eq (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership (rules out clamping in `snapStart`/`snapStep`); HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (j : Fin (m + 1)) :
    gridPath m (snapStart m f) (snapStep m f) j = (snapPath m f j : ℤ) := by
  sorry

/-- Lower envelope bound: the snapped cone envelope sits below `f`
(each cone `v_j − |x − t_j|` is under the graph of a 1-Lipschitz `f` with
`v_j ≤ f(t_j)`); HDP Exercise 8.9. -/
theorem coneFun_snap_le (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership; HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (x : unitInterval) :
    coneFun m (snapStart m f) (snapStep m f) x ≤ f x := by
  sorry

/-- Upper envelope bound: `f ≤ cone + 3/m` (floor-knot `1/m` + value-snap
`1/m` + cone offset `1/m`); HDP Exercise 8.9. -/
theorem le_coneFun_snap_add (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership; HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (x : unitInterval) :
    f x ≤ coneFun m (snapStart m f) (snapStep m f) x + 3 / m := by
  sorry

/-- **Approximation lemma** (HDP Exercise 8.9): every class member is within
`L∞`-distance `3/m` of a net member (via `ContinuousMap.dist_le`).
Named-sorry fallback of `hdp-emp-approx`. -/
theorem exists_mem_lipschitzNet_dist_le (m : ℕ) [NeZero m]
    {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership; HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) :
    ∃ g ∈ lipschitzNet m, dist f g ≤ 3 / m := by
  sorry

/-- **ε-net form** (HDP Exercise 8.9): for `m ≥ 3/ε` the grid net is an
internal ε-net of the Lipschitz class. -/
theorem isEpsilonNet_lipschitzNet {ε : ℝ}
    -- USER-INPUT: positive radius; HDP Exercise 8.9
    (hε : 0 < ε) {m : ℕ} [NeZero m]
    -- LEAN-ONLY: mesh fine enough for the 3/m approximation; no scope change
    (hm : 3 / ε ≤ (m : ℝ)) :
    IsEpsilonNet (↑(lipschitzNet m)) lipschitzUnitClass ε := by
  sorry

end StatLean.ConcentrationInequalities
