import StatLean.HypothesisTesting.MLR.OneSided
import StatLean.HypothesisTesting.NeymanPearson.Generalized

/-!
# Two-sided hypotheses in a one-parameter exponential family

Uniformly most powerful tests survive one step beyond the one-sided problem: for
`H : θ ≤ θ₁ or θ ≥ θ₂` against `K : θ₁ < θ < θ₂` in a one-parameter exponential family
there is a UMP test, which rejects on a *bounded* interval of the natural statistic,
$$ \varphi(x) = 1 \ \text{ if } C_1 < T(x) < C_2, \qquad \gamma_i \ \text{ if } T(x) = C_i,
\qquad 0 \ \text{ otherwise}, $$
with the four constants pinned down by the two size conditions
`E_{θ₁}φ = E_{θ₂}φ = α`. Two constraints, hence the generalized fundamental lemma with
`m = 2` rather than the plain one.

Contents:
* `twoSidedTest T C₁ C₂ γ₁ γ₂` — the test displayed above;
* `isUMP_twoSided` — existence of the four constants and uniform optimality;
* `power_min_twoSided` — outside `[θ₁, θ₂]` the same test *minimizes* the rejection
  probability among all tests meeting the two size conditions;
* `power_lt_of_twoSided_right` — comparison of two such tests with a common size at `θ₁`:
  shifting the rejection interval to the right raises the power above `θ₁` and lowers it
  below;
* `twoSided_ae_unique` — the two size conditions determine the test almost everywhere.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.7 (Two-Sided Hypotheses), Theorem 3.7.1 (the UMP two-sided test `C₁ < T <
C₂` in a one-parameter exponential family) and Lemma 3.7.1 (the comparison/uniqueness step).
(`TSH4 §3.7 Thm 3.7.1, Lem 3.7.1`.)

**Proof formalization notes.**
* The rejection region is an interval of the natural statistic, so the test cannot be
  obtained from a single likelihood-ratio comparison; the two size conditions are handled
  by the two-constraint form of the generalized fundamental lemma, whose multipliers
  produce the two boundaries.
* The order of branches in `twoSidedTest` puts the two boundary cases first, so the
  definition is unambiguous even for degenerate constants: at `C₁ = C₂` the value is `γ₁`,
  and for `C₂ ≤ C₁` the test rejects nowhere except possibly at the two boundary points.
  The theorems all produce or assume `C₁ < C₂`.
* The comparison lemma requires the *strict* form of the monotone likelihood ratio
  together with strictly positive densities. Both are transcribed explicitly: the strict
  ratio condition is written division-free as `p_{θ'}(x)·p_θ(y) < p_θ(x)·p_{θ'}(y)` for
  `T x < T y`, matching the frozen non-strict `HasMLR`.
* "`φ*` lies to the right of `φ`" is transcribed as the lexicographic condition on the
  left boundary: either `C₁ < C₁'`, or the boundaries agree and the randomization weight
  there is smaller, `γ₁' < γ₁`.
* Uniqueness is stated as `μ`-a.e. equality. Since the densities are strictly positive,
  this coincides with almost-sure equality under every member of the family.
* The unimodality clause of the classical statement — for `0 < α < 1` the power function
  has an interior maximum and decreases strictly away from it, unless the statistic is
  supported on two points — is not stated here.

**Bibliographic comments.** Two-sided problems and the tests solving them appear in
J. Neyman and E. S. Pearson ("Contributions to the theory of testing statistical
hypotheses," *Stat. Res. Mem.* **1** (1936), 1–37); the two-constraint fundamental lemma
they rest on is due to G. B. Dantzig and A. Wald ("On the fundamental lemma of Neyman and
Pearson," *Ann. Math. Statist.* **22** (1951), 87–93), and the underlying monotonicity
properties of exponential families to S. Karlin and H. Rubin ("The theory of decision
procedures for distributions with monotone likelihood ratio," *Ann. Math. Statist.* **27**
(1956), 272–299).
-/

open MeasureTheory

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **two-sided test** based on the statistic `T`: reject when `C₁ < T < C₂`, reject
with probability `γᵢ` when `T = Cᵢ`, accept outside. The boundary branches are tested
first, so the definition is total and unambiguous: at `C₁ = C₂` the value is `γ₁`, and for
`C₂ ≤ C₁` the test rejects only (possibly) at the two boundary points. All theorems below
produce or assume `C₁ < C₂` and `γᵢ ∈ [0,1]`. -/
noncomputable def twoSidedTest (T : 𝓧 → ℝ) (C₁ C₂ γ₁ γ₂ : ℝ) : 𝓧 → ℝ := fun x =>
  if T x = C₁ then γ₁
  else if T x = C₂ then γ₂
  else if C₁ < T x ∧ T x < C₂ then 1
  else 0

/-- The scalar value of the two-sided test as a function of the statistic level `t`,
written with nested `if`s (so `split_ifs` produces atomic order conditions). -/
private noncomputable def twoSidedVal (C₁ C₂ γ₁ γ₂ t : ℝ) : ℝ :=
  if t = C₁ then γ₁ else if t = C₂ then γ₂ else if C₁ < t then if t < C₂ then 1 else 0 else 0

/-- `twoSidedTest` factors through the statistic via `twoSidedVal`. -/
private lemma twoSidedTest_eq_val (T : 𝓧 → ℝ) (C₁ C₂ γ₁ γ₂ : ℝ) (x : 𝓧) :
    twoSidedTest T C₁ C₂ γ₁ γ₂ x = twoSidedVal C₁ C₂ γ₁ γ₂ (T x) := by
  unfold twoSidedTest twoSidedVal
  by_cases h1 : T x = C₁
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : T x = C₂
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : C₁ < T x
      · rw [if_pos h3]; by_cases h4 : T x < C₂
        · rw [if_pos ⟨h3, h4⟩, if_pos h4]
        · rw [if_neg (fun h => h4 h.2), if_neg h4]
      · rw [if_neg h3, if_neg (fun h => h3 h.1)]

/-- With `γᵢ ∈ [0,1]` and `C₁ < C₂`, the scalar value lies in `[0,1]`. -/
private lemma twoSidedVal_mem_Icc {C₁ C₂ γ₁ γ₂ : ℝ}
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    twoSidedVal C₁ C₂ γ₁ γ₂ t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold twoSidedVal
  split_ifs
  · exact hγ₁
  · exact hγ₂
  · exact ⟨zero_le_one, le_refl 1⟩
  · exact ⟨le_refl 0, zero_le_one⟩
  · exact ⟨le_refl 0, zero_le_one⟩

set_option maxHeartbeats 1000000 in
/-- **Separation of the difference of two right-shifted two-sided values.** Write
`D t = twoSidedVal C₁' C₂' γ₁' γ₂' t − twoSidedVal C₁ C₂ γ₁ γ₂ t`. If the second rejection
interval lies to the right of the first (`hright`), then every level `s` at which `D s > 0`
lies strictly to the right of every level `t` at which `D t < 0`: the positive part of the
difference sits above the negative part. This is the single sign-change structure that
drives the Lehmann comparison. -/
private lemma twoSidedVal_sub_sep {C₁ C₂ C₁' C₂' γ₁ γ₂ γ₁' γ₂' : ℝ}
    (hC : C₁ < C₂) (hC' : C₁' < C₂')
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1)
    (hγ₁' : γ₁' ∈ Set.Icc (0 : ℝ) 1) (hγ₂' : γ₂' ∈ Set.Icc (0 : ℝ) 1)
    (hright : C₁ < C₁' ∨ (C₁ = C₁' ∧ γ₁' < γ₁)) {s t : ℝ}
    (hs : 0 < twoSidedVal C₁' C₂' γ₁' γ₂' s - twoSidedVal C₁ C₂ γ₁ γ₂ s)
    (ht : twoSidedVal C₁' C₂' γ₁' γ₂' t - twoSidedVal C₁ C₂ γ₁ γ₂ t < 0) :
    t < s := by
  obtain ⟨hγ₁0, hγ₁1⟩ := hγ₁; obtain ⟨hγ₂0, hγ₂1⟩ := hγ₂
  obtain ⟨hγ₁'0, hγ₁'1⟩ := hγ₁'; obtain ⟨hγ₂'0, hγ₂'1⟩ := hγ₂'
  by_contra hst
  push_neg at hst
  -- `s ≤ t`; derive a contradiction with `D s > 0`, `D t < 0`.
  unfold twoSidedVal at hs ht
  rcases hright with hr | ⟨hrEq, hrγ⟩
  · split_ifs at hs ht <;>
      first
        | linarith
        | (exfalso; subst_vars; simp_all <;>
            exact absurd (le_antisymm hst (by assumption : t ≤ s)) (by assumption : ¬ s = t))
        | (exfalso; subst_vars; linarith)
        | (exfalso; have : s = t := le_antisymm hst ‹t ≤ s›; subst this; simp_all)
  · subst hrEq
    split_ifs at hs ht <;>
      first
        | linarith
        | (exfalso; subst_vars; simp_all <;>
            exact absurd (le_antisymm hst (by assumption : t ≤ s)) (by assumption : ¬ s = t))
        | (exfalso; subst_vars; linarith)
        | (exfalso; have : s = t := le_antisymm hst ‹t ≤ s›; subst this; simp_all)

/-- **UMP test of a two-sided hypothesis.** In a one-parameter exponential family, with the
parametrization strictly increasing, there are constants `C₁ < C₂` and boundary weights
`γ₁, γ₂ ∈ [0,1]` for which the two-sided test has size exactly `α` at both `θ₁` and `θ₂`
and is uniformly most powerful at level `α` for `H : θ ≤ θ₁ or θ₂ ≤ θ` against
`K : θ₁ < θ < θ₂`. -/
theorem isUMP_twoSided
    -- USER-INPUT: the exponential family, with σ-finite reference measure
    (E : ExpFamily 𝓧 ℝ) [SigmaFinite E.base]
    -- USER-INPUT: the model, a family of probability measures on a real parameter
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: the parametrization, strictly increasing (the printed hypothesis on `Q`)
    {ηmap : ℝ → ℝ} (hη : StrictMono ηmap)
    -- USER-INPUT: the model is the canonical family read through `ηmap`
    (hrepr : IsCanonicalRepr P E ηmap)
    -- USER-INPUT: every parameter value lies in the natural parameter set, so no member
    -- degenerates to the junk zero measure
    (hnat : ∀ θ, ηmap θ ∈ E.natSet)
    -- USER-INPUT: the two null boundaries, in order
    {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    -- USER-INPUT: nondegenerate level
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C₁ C₂ γ₁ γ₂ : ℝ, C₁ < C₂ ∧ γ₁ ∈ Set.Icc (0 : ℝ) 1 ∧ γ₂ ∈ Set.Icc (0 : ℝ) 1 ∧
      power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₁ = α ∧
      power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₂ = α ∧
      IsUMP P {θ : ℝ | θ ≤ θ₁ ∨ θ₂ ≤ θ} (Set.Ioo θ₁ θ₂) α
        (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) := by
  -- BLOCKED upstream, on two distinct open sorries of `NeymanPearson/Generalized.lean`.
  -- ROADMAP (TSH4 Thm 3.7.1): apply the `m = 2` generalized fundamental lemma with
  -- `f₁ = p_{θ₁}`, `f₂ = p_{θ₂}`, `f₃ = p_θ` for `θ ∈ (θ₁, θ₂)` and constraint vector
  -- `c = (α, α)`. Two ingredients are needed and both are `sorry` there:
  --   • `exists_test_with_prescribed_sizes` — produces a test meeting the two size
  --     conditions with multipliers; it is `sorry` (Generalized.lean:567);
  --   • `exists_test_max_integral_of_constraints` — existence of a maximizer over the
  --     constraint class; `sorry` (Generalized.lean:127), and genuinely a compactness
  --     statement (weak-* sequential compactness of the unit ball of `L∞(μ)`).
  -- NOTE: the previously recorded obstruction "momentSet closedness" is now only partly
  -- relevant — `isClosed_momentSet`/`convex_isClosed_momentSet` are proven and
  -- `ForMathlib/TestsWeakCompact` is 0-sorry — but `exists_multipliers_of_max`
  -- (Generalized.lean:540) and the two above are still open, so no honest reduction exists
  -- yet. `isMax_of_multiplier_form` (proven) only certifies a *given* candidate.
  -- A THIRD gap is specific to this file and is NOT covered by the generalized lemma: the
  -- multiplier shape `{p_θ > k₁p_{θ₁} + k₂p_{θ₂}}` must be identified with an *interval*
  -- `C₁ < T < C₂` of the natural statistic. In canonical form this is the strict convexity
  -- of `t ↦ exp(η₁ t) ` combinations — `k₁e^{a₁t} + k₂e^{a₂t} < e^{a₃t}` on an interval and
  -- `>` outside it, for `a₁ < a₃ < a₂` — which has no Mathlib brick and needs its own
  -- development (a strictly-convex-crossing lemma for exponential sums).
  -- TODO: close `exists_test_with_prescribed_sizes` upstream, then add the
  -- exponential-sum two-crossing lemma here.
  sorry

/-- **Minimum rejection probability outside the interval.** Among all tests whose size is
exactly `α` at both `θ₁` and `θ₂`, the two-sided test minimizes the rejection probability
at every parameter value below `θ₁` or above `θ₂`. -/
theorem power_min_twoSided
    -- USER-INPUT: the exponential family, with σ-finite reference measure
    (E : ExpFamily 𝓧 ℝ) [SigmaFinite E.base]
    -- USER-INPUT: the model, and its canonical presentation through a strictly
    -- increasing parametrization
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {ηmap : ℝ → ℝ} (hη : StrictMono ηmap) (hrepr : IsCanonicalRepr P E ηmap)
    (hnat : ∀ θ, ηmap θ ∈ E.natSet)
    -- USER-INPUT: the two null boundaries and the level
    {θ₁ θ₂ α : ℝ} (hθ : θ₁ < θ₂)
    -- USER-INPUT: the constants of the test under study
    {C₁ C₂ γ₁ γ₂ : ℝ} (hC : C₁ < C₂)
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the test satisfies the two size conditions
    (hsize₁ : power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₁ = α)
    (hsize₂ : power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₂ = α) :
    ∀ ψ, IsCriticalFn ψ → power P ψ θ₁ = α → power P ψ θ₂ = α →
      ∀ θ : ℝ, θ < θ₁ ∨ θ₂ < θ →
        power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ ≤ power P ψ θ := by
  -- BLOCKED upstream. ROADMAP (TSH4 Thm 3.7.1, minimizing clause): outside `[θ₁, θ₂]` apply
  -- the `m = 2` generalized fundamental lemma to the CO-test `1 − φ` — i.e. maximize
  -- `∫(1 − φ)p_θ` subject to the same two size conditions, which by
  -- `isMax_le_of_multiplier_form_nonneg` needs multipliers of the right sign. The
  -- multipliers come from `exists_multipliers_of_max` (`sorry`, Generalized.lean:540), which
  -- rests on the inner-point condition for `momentSet`, and the maximizer they are attached
  -- to comes from `exists_test_max_integral_of_constraints` (`sorry`,
  -- Generalized.lean:127). Unlike the one-sided case there is no single-likelihood-ratio
  -- shortcut: `power_min_oneSided` could reduce to the plain NP lemma because one constraint
  -- means one multiplier, whereas here the sign pattern of `(k₁, k₂)` outside `[θ₁, θ₂]` is
  -- exactly what the undetermined-multiplier existence theorem supplies.
  -- TODO: close `exists_multipliers_of_max` / `exists_test_max_integral_of_constraints`
  -- upstream, then this is the `isMax_le_of_multiplier_form_nonneg` assembly.
  sorry

/-- **Comparison of two two-sided tests with a common size at `θ₁`.** If the rejection
interval of the second test lies to the right of that of the first — a larger left
boundary, or the same boundary with a smaller randomization weight there — then the second
test is strictly more powerful above `θ₁` and strictly less powerful below it. -/
theorem power_lt_of_twoSided_right
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic
    (T : 𝓧 → ℝ) (hT : Measurable T)
    -- USER-INPUT: densities strictly positive everywhere
    (hpos : ∀ θ x, 0 < p θ x)
    -- USER-INPUT: *strict* monotone likelihood ratio, division-free: the ratio
    -- `p_{θ'}/p_θ` is strictly increasing in `T` for `θ < θ'`
    (hstrict : ∀ θ θ' : ℝ, θ < θ' → ∀ x y, T x < T y → p θ' x * p θ y < p θ x * p θ' y)
    -- USER-INPUT: the constants of the two tests, each an honest rejection interval
    {C₁ C₂ C₁' C₂' γ₁ γ₂ γ₁' γ₂' : ℝ} (hC : C₁ < C₂) (hC' : C₁' < C₂')
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1)
    (hγ₁' : γ₁' ∈ Set.Icc (0 : ℝ) 1) (hγ₂' : γ₂' ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the reference parameter value
    {θ₁ : ℝ}
    -- USER-INPUT: the two tests have the same size at `θ₁`
    (hsize : power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ₁ =
      power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ₁)
    -- USER-INPUT: the second rejection interval lies to the right of the first
    (hright : C₁ < C₁' ∨ (C₁ = C₁' ∧ γ₁' < γ₁)) :
    (∀ θ : ℝ, θ₁ < θ → power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ <
        power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ) ∧
      ∀ θ : ℝ, θ < θ₁ → power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ <
        power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ := by
  -- FALSE AS STATED (verified counterexample). The conclusion is a STRICT inequality, but
  -- nothing forces the statistic to be non-degenerate: `hstrict` is vacuous when `T` is
  -- constant, since it only constrains pairs with `T x < T y`.
  --
  -- COUNTEREXAMPLE. `𝓧 = ℝ`, `μ = volume`, `p θ x = ϕ(x − θ)` (so `hpos : 0 < p θ x` holds),
  -- and `T = fun _ => 0`, a measurable constant. Then `hstrict` holds vacuously. Take
  -- `C₁ = -2 < C₂ = -1`, `C₁' = 1 < C₂' = 2`, all four `γ = 0`; `hright` holds as
  -- `C₁ = -2 < 1 = C₁'`. Both tests are identically `0`: for `t = 0` neither `t = Cᵢ` nor
  -- `Cᵢ < t < Cᵢ₊₁` holds in either configuration. So `hsize` holds (`0 = 0`), and the
  -- conclusion demands `0 < 0` at every `θ > θ₁`. False.
  --
  -- The counterexample is not an artefact of the constant statistic: the same failure occurs
  -- whenever both rejection intervals miss the (essential) range of `T`.
  -- TODO(statement-bug): add a non-degeneracy hypothesis putting `T`-mass strictly inside
  -- both rejection intervals — e.g. `0 < power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ₁ < 1` — or
  -- assume `T` surjective. Under such a hypothesis the proof is the Lehmann comparison:
  -- `twoSidedVal_sub_sep` (already proven in this file) says the positive part of
  -- `D = φ' − φ` sits strictly above its negative part in `T`, so strict MLR gives a
  -- separating ratio constant `k` with `∫D p_θ = ∫D(p_θ/p_{θ₁} − k)p_{θ₁} + k∫D p_{θ₁}`,
  -- the first term being strictly signed for `θ ≠ θ₁` and the second vanishing by `hsize`.
  sorry

/-- **The size conditions determine the test.** Two two-sided tests with size exactly `α`
at both `θ₁` and `θ₂` agree almost everywhere. -/
theorem twoSided_ae_unique
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic
    (T : 𝓧 → ℝ) (hT : Measurable T)
    -- USER-INPUT: densities strictly positive everywhere
    (hpos : ∀ θ x, 0 < p θ x)
    -- USER-INPUT: *strict* monotone likelihood ratio, division-free
    (hstrict : ∀ θ θ' : ℝ, θ < θ' → ∀ x y, T x < T y → p θ' x * p θ y < p θ x * p θ' y)
    -- USER-INPUT: the constants of the two tests
    {C₁ C₂ C₁' C₂' γ₁ γ₂ γ₁' γ₂' : ℝ} (hC : C₁ < C₂) (hC' : C₁' < C₂')
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1)
    (hγ₁' : γ₁' ∈ Set.Icc (0 : ℝ) 1) (hγ₂' : γ₂' ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the two null boundaries, in order, and the level
    {θ₁ θ₂ α : ℝ} (hθ : θ₁ < θ₂)
    -- USER-INPUT: both tests meet both size conditions
    (hsize₁ : power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ₁ = α)
    (hsize₂ : power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ₂ = α)
    (hsize₁' : power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ₁ = α)
    (hsize₂' : power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ₂ = α) :
    twoSidedTest T C₁ C₂ γ₁ γ₂ =ᵐ[μ] twoSidedTest T C₁' C₂' γ₁' γ₂' := by
  -- TRUE (unlike its sibling `power_lt_of_twoSided_right`, which is FALSE as stated: the
  -- degenerate constant-`T` configuration that kills the strict power comparison is harmless
  -- here, because it forces the two tests to take the same constant value once their sizes
  -- agree). Not closed; the argument below is complete but long, and is left as debt.
  --
  -- ROADMAP. Write `D t = twoSidedVal C₁' C₂' γ₁' γ₂' t − twoSidedVal C₁ C₂ γ₁ γ₂ t` and
  -- `r x = p_{θ₂} x / p_{θ₁} x` (well defined: `hpos`). By `hsize₁`/`hsize₁'` and
  -- `hsize₂`/`hsize₂'`, `∫ D(T x) p_{θ₁} x dμ = ∫ D(T x) p_{θ₂} x dμ = 0`.
  --  (1) SIGN CHANGE. `twoSidedVal_sub_sep` (proven above) gives, under
  --      `hright : C₁ < C₁' ∨ (C₁ = C₁' ∧ γ₁' < γ₁)`, that `D t < 0 < D s → t < s`. The
  --      trichotomy on the left data splits into: `hright`; its mirror (swap the two tests,
  --      which negates `D`); and `C₁ = C₁' ∧ γ₁ = γ₁'`, in which case `D` has CONSTANT sign
  --      (compare `C₂` with `C₂'`), so both separation statements hold vacuously. A helper
  --      `twoSidedVal_sub_sep_eqLeft` covering that third case is missing.
  --  (2) SEPARATING RATIO. If `{x : D (T x) < 0}` is empty then `D ∘ T ≥ 0`, and
  --      `∫ D(T x) p_{θ₁} x dμ = 0` with `p_{θ₁} > 0` forces `D ∘ T = 0` a.e., done;
  --      likewise if `{x : 0 < D (T x)}` is empty. Otherwise `k = sSup {r x : D (T x) < 0}`
  --      exists (bounded above by `r y` for any `y` with `D (T y) > 0`, via (1) and
  --      `hstrict`), and `r ≤ k` on `{D ∘ T < 0}`, `k ≤ r` on `{D ∘ T > 0}`.
  --  (3) VANISHING. `g x = D (T x) · (p_{θ₂} x − k · p_{θ₁} x) ≥ 0` pointwise by (2), and
  --      `∫ g dμ = ∫ D(T x) p_{θ₂} − k ∫ D(T x) p_{θ₁} = 0`, so `g = 0` a.e.
  --  (4) LEVEL SET. Where `D ∘ T ≠ 0` and `g = 0` one has `r x = k`; `hstrict` makes `r`
  --      strictly increasing along `T`, so all such `x` share one value `T x = c`. Hence
  --      `D ∘ T = 0` a.e. off `{T = c}`, and then `D c · ∫_{T = c} p_{θ₁} dμ = 0` with
  --      `p_{θ₁} > 0` gives `D c = 0` whenever `μ {T = c} > 0`. Either way `D ∘ T = 0` a.e.,
  --      which is the conclusion via `twoSidedTest_eq_val`.
  -- TODO: add `twoSidedVal_sub_sep_eqLeft` (the equal-left-data constant-sign case) and
  -- formalize steps (2)–(4) as a private lemma taking the separation of (1) as a hypothesis,
  -- so it can be applied twice (once per orientation).
  sorry

end StatLean.HypothesisTesting
