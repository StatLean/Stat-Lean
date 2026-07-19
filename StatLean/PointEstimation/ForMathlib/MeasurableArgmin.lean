import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# A measurable selection of minimizers of a parametrized convex scan

Given a family `f : Ω → ℝ → ℝ≥0∞` of convex, continuous, coercive functions of a real scan
variable, depending measurably on a parameter `ω`, there is a **measurable** map
`u : Ω → ℝ` picking a minimizer of `f ω` for every `ω`.

* `iInf_eq_iInf_rat_of_continuous` — a continuous `ℝ≥0∞`-valued function has the same
  infimum over `ℝ` as over `ℚ`;
* `exists_forall_le_of_continuous_of_coercive` — a continuous coercive function attains its
  infimum;
* `exists_measurable_argmin` — the measurable selection.

This is the brick that makes "minimize the conditional risk pointwise, then read the answer
off as an estimator" legitimate: the pointwise minimizer must be a *measurable* function of
the conditioning variable before it can be called an estimator at all.

**Reference.** Classical measurable-selection theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* **Continuity, not lower semicontinuity — deliberate.** The natural hypothesis for a
  measurable-argmin theorem is lower semicontinuity in the scan variable, and the statement
  below does hold in that generality. Continuity is assumed instead because it keeps the
  selection *elementarily* provable: the relaxed sublevel sets can be tested on rationals
  (see the next item), whereas the lower semicontinuous version routes through a genuine
  selection theorem. Weakening `hcont` to `LowerSemicontinuous (f ω)` is a strengthening that
  can be made later without touching any call site.
* **Rational-relaxed-sublevel selection.** Take `u ω` to be the *leftmost* minimizer,
  `u ω = sInf {v | f ω v = ⨅ w, f ω w}` (nonempty by
  `exists_forall_le_of_continuous_of_coercive`, closed by continuity, bounded below by
  coercivity, and an interval by convexity). Measurability follows from
  `u ω < r ↔ ∃ q : ℚ, (q : ℝ) < r ∧ ⨅ v ∈ Set.Iic (q : ℝ), f ω v = ⨅ v, f ω v`, where each
  relativized infimum is again a countable infimum over rationals by the density argument of
  `iInf_eq_iInf_rat_of_continuous`. Every set on the right is measurable because `f` is
  jointly measurable, and the union is countable.
* `iInf_eq_iInf_rat_of_continuous` is stated globally over `ℝ`; the selection proof uses the
  same density argument relativized to `Set.Iic q`, which is the special case of
  `⨅ x ∈ closure s, g x = ⨅ x ∈ s, g x` for continuous `g`.
* **Convexity is `ConvexOn ℝ≥0 Set.univ`.** For an `ℝ≥0∞`-valued function this is the only
  convexity predicate that typechecks at this pin: `ConvexOn 𝕜` needs `SMul 𝕜 ℝ≥0∞`, and
  `ℝ≥0∞` is a module over `ℝ≥0` but not over `ℝ`. On `[0, ∞]`-valued functions of a real
  variable the `ℝ≥0`-coefficient definition is the usual midpoint-convexity condition, so
  nothing is lost.
* **Coercivity is `Tendsto (f ω) (cocompact ℝ) (𝓝 ⊤)`, not `… atTop`.** In `ℝ≥0∞`,
  `Filter.atTop = pure ⊤` (`OrderTop.atTop_eq`), so the `atTop` phrasing would read "`f ω`
  equals `⊤` off a compact set" — true but useless. The `𝓝 ⊤` form is the intended "`f ω`
  blows up at infinity"; for `ℝ`-valued scans (see `ForMathlib/ConvexMinimizers.lean`) the
  two coincide and `atTop` is used there.
* **Attainment is derived, never hypothesized.** The conclusion asserts
  `f ω (u ω) = ⨅ v, f ω v`, i.e. that the infimum *is attained at the selected point*; it is
  forced by continuity plus coercivity and so must not appear as a hypothesis.

**Bibliographic comments.** Measurable selections of set-valued maps are due to
K. Kuratowski and C. Ryll-Nardzewski ("A general theorem on selectors," *Bull. Acad. Polon.
Sci. Sér. Sci. Math. Astronom. Phys.* **13** (1965), 397–403); the special case of an
argmin selection for a Carathéodory integrand is the standard application of that theorem,
here replaced by the elementary leftmost-minimizer construction.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.PointEstimation

/-- The infimum of a continuous `ℝ≥0∞`-valued function over `ℝ` is already attained as an
infimum over the rationals. -/
theorem iInf_eq_iInf_rat_of_continuous
    -- USER-INPUT: the function to be minimized; free choice
    {g : ℝ → ℝ≥0∞}
    -- USER-INPUT: continuity; the density argument fails for a merely measurable `g`
    (hg : Continuous g) :
    (⨅ x : ℝ, g x) = ⨅ q : ℚ, g (q : ℝ) := by
  refine le_antisymm (le_iInf fun q => iInf_le _ _) (le_iInf fun x => ?_)
  haveI hnb : (𝓝[Set.range ((↑) : ℚ → ℝ)] x).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (Rat.denseRange_cast x)
  have htend : Tendsto g (𝓝[Set.range ((↑) : ℚ → ℝ)] x) (𝓝 (g x)) :=
    (hg.tendsto x).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  obtain ⟨q, rfl⟩ := hy
  exact iInf_le _ q

/-- A continuous coercive `ℝ≥0∞`-valued function on `ℝ` attains its infimum. -/
theorem exists_forall_le_of_continuous_of_coercive
    -- USER-INPUT: the function to be minimized; free choice
    {g : ℝ → ℝ≥0∞}
    -- USER-INPUT: continuity; closedness of sublevel sets
    (hg : Continuous g)
    -- USER-INPUT: coercivity; compactness of a nontrivial sublevel set. See the header for
    -- why the target filter is `𝓝 ⊤` rather than `atTop`.
    (hcoer : Tendsto g (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞))) :
    ∃ x : ℝ, ∀ y : ℝ, g x ≤ g y := by
  set s : ℝ≥0∞ := ⨅ y, g y with hs
  by_cases hstop : s = ⊤
  · exact ⟨0, fun y => by rw [iInf_eq_top.mp hstop y]; exact le_top⟩
  · -- choose a finite level `c` strictly above the infimum
    have hslt : s < ⊤ := lt_top_iff_ne_top.mpr hstop
    set c : ℝ≥0∞ := s + 1 with hc
    have hctop : c < ⊤ := by
      rw [hc]; exact ENNReal.add_lt_top.mpr ⟨hslt, ENNReal.one_lt_top⟩
    have hsc : s < c := by rw [hc]; exact ENNReal.lt_add_right hstop one_ne_zero
    obtain ⟨y₀, hy₀⟩ := iInf_lt_iff.mp hsc
    -- the sublevel set `{y | g y ≤ c}` is compact and nonempty
    have hmem : g ⁻¹' Set.Ioi c ∈ cocompact ℝ := hcoer (Ioi_mem_nhds hctop)
    obtain ⟨t, ht_comp, ht_sub⟩ := mem_cocompact.mp hmem
    have hclosed : IsClosed {y | g y ≤ c} := isClosed_Iic.preimage hg
    have hsub : {y | g y ≤ c} ⊆ t := by
      intro y hy
      by_contra hyt
      exact absurd (ht_sub hyt) (by simpa using hy)
    have hcompact : IsCompact {y | g y ≤ c} := ht_comp.of_isClosed_subset hclosed hsub
    have hne : {y | g y ≤ c}.Nonempty := ⟨y₀, hy₀.le⟩
    obtain ⟨x, hx_mem, hx_min⟩ := hcompact.exists_isMinOn hne hg.continuousOn
    refine ⟨x, fun y => ?_⟩
    by_cases hy : g y ≤ c
    · exact isMinOn_iff.mp hx_min y hy
    · exact le_trans hx_mem (not_le.mp hy).le

/-- The infimum over `Iic q` equals the infimum of `v ↦ g (min v q)` over all of `ℝ`. -/
private theorem iInf_Iic_eq_iInf_comp_min (g : ℝ → ℝ≥0∞) (q : ℝ) :
    (⨅ v ∈ Set.Iic q, g v) = ⨅ v : ℝ, g (min v q) := by
  apply le_antisymm
  · exact le_iInf fun v => iInf₂_le (min v q) (min_le_right v q)
  · refine le_iInf₂ fun w hw => ?_
    calc ⨅ v : ℝ, g (min v q) ≤ g (min w q) := iInf_le _ w
      _ = g w := by rw [min_eq_left hw]

/-- A continuous coercive function attains its infimum over a lower half-line `Iic q`. -/
private theorem exists_argmin_Iic {g : ℝ → ℝ≥0∞} (hg : Continuous g)
    (hcoer : Tendsto g (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞))) (q : ℝ) :
    ∃ w ≤ q, g w = ⨅ v ∈ Set.Iic q, g v := by
  set mq : ℝ≥0∞ := ⨅ v ∈ Set.Iic q, g v with hmq
  by_cases hmqtop : mq = ⊤
  · refine ⟨q, le_refl q, ?_⟩
    have h : mq ≤ g q := by
      rw [hmq]; exact iInf₂_le q (Set.mem_Iic.mpr le_rfl)
    rw [hmqtop] at h ⊢
    exact top_le_iff.mp h
  · have hmqlt : mq < ⊤ := lt_top_iff_ne_top.mpr hmqtop
    set c : ℝ≥0∞ := mq + 1 with hc
    have hctop : c < ⊤ := by
      rw [hc]; exact ENNReal.add_lt_top.mpr ⟨hmqlt, ENNReal.one_lt_top⟩
    have hmc : mq < c := by rw [hc]; exact ENNReal.lt_add_right hmqtop one_ne_zero
    obtain ⟨v₀, hv₀q, hv₀c⟩ : ∃ v₀ ≤ q, g v₀ < c := by
      have h : (⨅ v ∈ Set.Iic q, g v) < c := hmc
      rw [iInf_lt_iff] at h
      obtain ⟨v, hv⟩ := h
      rw [iInf_lt_iff] at hv
      obtain ⟨hvq, hvc⟩ := hv
      exact ⟨v, hvq, hvc⟩
    have hmem : g ⁻¹' Set.Ioi c ∈ cocompact ℝ := hcoer (Ioi_mem_nhds hctop)
    obtain ⟨t, ht_comp, ht_sub⟩ := mem_cocompact.mp hmem
    have hclosed : IsClosed (Set.Iic q ∩ {v | g v ≤ c}) :=
      isClosed_Iic.inter (isClosed_Iic.preimage hg)
    have hsub : (Set.Iic q ∩ {v | g v ≤ c}) ⊆ t := by
      intro v hv
      by_contra hvt
      exact absurd (ht_sub hvt) (by simpa using hv.2)
    have hcompact : IsCompact (Set.Iic q ∩ {v | g v ≤ c}) :=
      ht_comp.of_isClosed_subset hclosed hsub
    have hne : (Set.Iic q ∩ {v | g v ≤ c}).Nonempty := ⟨v₀, hv₀q, hv₀c.le⟩
    obtain ⟨w, hw_mem, hw_min⟩ := hcompact.exists_isMinOn hne hg.continuousOn
    refine ⟨w, hw_mem.1, ?_⟩
    rw [hmq]
    refine le_antisymm ?_ (iInf₂_le w hw_mem.1)
    refine le_iInf₂ fun v hv => ?_
    by_cases hvc : g v ≤ c
    · exact isMinOn_iff.mp hw_min v ⟨hv, hvc⟩
    · exact le_trans hw_mem.2 (not_le.mp hvc).le

/-- **Measurable argmin.** A jointly measurable family of convex, continuous, coercive
functions of a real scan variable admits a measurable minimizer selection. -/
theorem exists_measurable_argmin {Ω : Type*} [MeasurableSpace Ω]
    -- USER-INPUT: the parametrized objective (a conditional risk in applications)
    {f : Ω → ℝ → ℝ≥0∞}
    -- USER-INPUT: joint measurability; without it no selection can be measurable
    (hf : Measurable (Function.uncurry f))
    -- USER-INPUT: continuity in the scan variable; see the header on the LSC strengthening
    (hcont : ∀ ω, Continuous (f ω))
    -- USER-INPUT: convexity in the scan variable; makes the minimizer set an interval
    (hconv : ∀ ω, ConvexOn ℝ≥0 Set.univ (f ω))
    -- USER-INPUT: coercivity in the scan variable; forces attainment
    (hcoer : ∀ ω, Tendsto (f ω) (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞))) :
    ∃ u : Ω → ℝ, Measurable u ∧ ∀ ω, f ω (u ω) = ⨅ v : ℝ, f ω v := by
  classical
  -- pointwise minimum value; measurable through a rational infimum
  have hfq : ∀ q : ℚ, Measurable (fun ω => f ω (q : ℝ)) := fun q =>
    hf.comp (measurable_id.prodMk measurable_const)
  set M : Ω → ℝ≥0∞ := fun ω => ⨅ v : ℝ, f ω v with hMdef
  have hM_meas : Measurable M := by
    have hEq : M = fun ω => ⨅ q : ℚ, f ω (q : ℝ) := by
      funext ω; exact iInf_eq_iInf_rat_of_continuous (hcont ω)
    rw [hEq]; exact Measurable.iInf hfq
  -- restricted minimum value over `Iic q`; measurable through the `min`-trick
  have hLq_meas : ∀ q : ℚ, Measurable (fun ω => ⨅ v ∈ Set.Iic (q : ℝ), f ω v) := by
    intro q
    have hEq : (fun ω => ⨅ v ∈ Set.Iic (q : ℝ), f ω v)
        = fun ω => ⨅ p : ℚ, f ω (min (p : ℝ) (q : ℝ)) := by
      funext ω
      rw [iInf_Iic_eq_iInf_comp_min (f ω) (q : ℝ)]
      exact iInf_eq_iInf_rat_of_continuous
        ((hcont ω).comp (continuous_id.min continuous_const))
    rw [hEq]
    exact Measurable.iInf fun p => hf.comp (measurable_id.prodMk measurable_const)
  -- the minimizer set and its leftmost point
  set S : Ω → Set ℝ := fun ω => {v | f ω v = M ω} with hSdef
  set u : Ω → ℝ := fun ω => sInf (S ω) with hudef
  have hclosedS : ∀ ω, IsClosed (S ω) := fun ω =>
    isClosed_singleton.preimage (hcont ω)
  have hneS : ∀ ω, (S ω).Nonempty := by
    intro ω
    obtain ⟨x, hx⟩ := exists_forall_le_of_continuous_of_coercive (hcont ω) (hcoer ω)
    exact ⟨x, le_antisymm (le_iInf hx) (iInf_le _ x)⟩
  have hbddS : ∀ ω, M ω < ⊤ → BddBelow (S ω) := by
    intro ω hlt
    have hmem : f ω ⁻¹' Set.Ioi (M ω) ∈ cocompact ℝ := (hcoer ω) (Ioi_mem_nhds hlt)
    obtain ⟨t, ht_comp, ht_sub⟩ := mem_cocompact.mp hmem
    have hSsub : S ω ⊆ t := by
      intro v hv
      by_contra hvt
      have hlt2 : M ω < f ω v := ht_sub hvt
      rw [show f ω v = M ω from hv] at hlt2
      exact lt_irrefl _ hlt2
    exact ht_comp.bddBelow.mono hSsub
  -- attainment
  have hattain : ∀ ω, f ω (u ω) = M ω := by
    intro ω
    by_cases hMtop : M ω = ⊤
    · have h1 : M ω ≤ f ω (u ω) := iInf_le _ (u ω)
      rw [hMtop] at h1 ⊢
      exact top_le_iff.mp h1
    · have hlt : M ω < ⊤ := lt_top_iff_ne_top.mpr hMtop
      exact (hclosedS ω).csInf_mem (hneS ω) (hbddS ω hlt)
  -- leftmost-point characterisation of `{u ≤ q}`
  have hMle_biInf : ∀ ω (q : ℚ), M ω ≤ ⨅ v ∈ Set.Iic (q : ℝ), f ω v := fun ω q =>
    le_iInf₂ fun v _ => iInf_le _ v
  have hchar : ∀ ω (q : ℚ), u ω ≤ (q : ℝ) ↔
      (M ω = ⊤ ∧ (0 : ℝ) ≤ (q : ℝ)) ∨
      (M ω < ⊤ ∧ (⨅ v ∈ Set.Iic (q : ℝ), f ω v) = M ω) := by
    intro ω q
    by_cases hMtop : M ω = ⊤
    · -- here every point is a minimiser and `u ω = 0`
      have hSuniv : S ω = Set.univ := by
        ext v
        refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
        show f ω v = M ω
        exact le_antisymm (by rw [hMtop]; exact le_top) (iInf_le _ v)
      have hu0 : u ω = 0 := by
        show sInf (S ω) = 0
        rw [hSuniv]
        exact Real.sInf_of_not_bddBelow
          (not_bddBelow_iff.mpr fun x => ⟨x - 1, Set.mem_univ _, by linarith⟩)
      rw [hu0]
      constructor
      · intro h; exact Or.inl ⟨hMtop, h⟩
      · rintro (⟨_, h⟩ | ⟨hlt, _⟩)
        · exact h
        · exact absurd hMtop (ne_of_lt hlt)
    · have hlt : M ω < ⊤ := lt_top_iff_ne_top.mpr hMtop
      have hmem : u ω ∈ S ω := (hclosedS ω).csInf_mem (hneS ω) (hbddS ω hlt)
      constructor
      · intro h
        refine Or.inr ⟨hlt, le_antisymm ?_ (hMle_biInf ω q)⟩
        calc ⨅ v ∈ Set.Iic (q : ℝ), f ω v
            ≤ f ω (u ω) := iInf₂_le (u ω) (Set.mem_Iic.mpr h)
          _ = M ω := hmem
      · rintro (⟨hcontra, _⟩ | ⟨_, hbi⟩)
        · exact absurd hcontra hMtop
        · obtain ⟨w, hwq, hfw⟩ := exists_argmin_Iic (hcont ω) (hcoer ω) (q : ℝ)
          have hwS : w ∈ S ω := by show f ω w = M ω; rw [hfw, hbi]
          exact le_trans (csInf_le (hbddS ω hlt) hwS) hwq
  -- measurability of the selection
  refine ⟨u, ?_, fun ω => (hattain ω)⟩
  apply measurable_of_Iic
  intro r
  -- `{u ≤ r} = ⋂ (q:ℚ) (_ : r < q), {u ≤ q}`
  have hset : u ⁻¹' Set.Iic r
      = ⋂ (q : ℚ) (_ : r < (q : ℝ)), {ω | u ω ≤ (q : ℝ)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h q _; exact le_trans h (le_of_lt ‹r < (q : ℝ)›)
    · intro h
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨q, hrq, hqu⟩ := exists_rat_btwn hlt
      exact absurd (h q hrq) (not_le.mpr hqu)
  rw [hset]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => ?_
  have hqset : {ω | u ω ≤ (q : ℝ)}
      = ((M ⁻¹' {⊤}) ∩ {ω | (0 : ℝ) ≤ (q : ℝ)}) ∪
        ((M ⁻¹' Set.Iio ⊤) ∩ {ω | (⨅ v ∈ Set.Iic (q : ℝ), f ω v) = M ω}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_Iio]
    rw [hchar ω q]
  rw [hqset]
  refine MeasurableSet.union (MeasurableSet.inter ?_ ?_) (MeasurableSet.inter ?_ ?_)
  · exact hM_meas (measurableSet_singleton ⊤)
  · by_cases h : (0 : ℝ) ≤ (q : ℝ)
    · simp only [h, Set.setOf_true]; exact MeasurableSet.univ
    · simp only [h, Set.setOf_false]; exact MeasurableSet.empty
  · exact hM_meas measurableSet_Iio
  · exact measurableSet_eq_fun (hLq_meas q) hM_meas

end StatLean.PointEstimation
