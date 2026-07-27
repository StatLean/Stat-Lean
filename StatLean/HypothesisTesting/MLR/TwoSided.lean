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
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation

/-- The real inner product on `ℝ` is multiplication (local copy: the `MLR/OneSided`
version is `private` to that file). -/
private lemma ts_real_inner_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  have h1 : ⟪(1 : ℝ), b⟫_ℝ = b := by
    have h := real_inner_smul_right (1 : ℝ) 1 b
    simpa [real_inner_self_eq_norm_mul_norm] using h
  have h2 := real_inner_smul_left (1 : ℝ) b a
  simpa [h1] using h2

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

/-- Widening the rejection interval on the right can only raise the test: with a common left
boundary and `C₂ < C₂'`, the value is pointwise nondecreasing. -/
private lemma twoSidedVal_le_of_lt_right {C₁ C₂ C₂' γ₁ γ₂ γ₂' : ℝ} (hC : C₁ < C₂)
    (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1) (hγ₂' : 0 ≤ γ₂') (hlt : C₂ < C₂') (u : ℝ) :
    twoSidedVal C₁ C₂ γ₁ γ₂ u ≤ twoSidedVal C₁ C₂' γ₁ γ₂' u := by
  obtain ⟨hγ₂0, hγ₂1⟩ := hγ₂
  unfold twoSidedVal
  split_ifs <;> linarith

/-- Raising the right boundary weight can only raise the test. -/
private lemma twoSidedVal_le_of_le_gamma₂ {C₁ C₂ γ₁ γ₂ γ₂' : ℝ} (hle : γ₂ ≤ γ₂') (u : ℝ) :
    twoSidedVal C₁ C₂ γ₁ γ₂ u ≤ twoSidedVal C₁ C₂ γ₁ γ₂' u := by
  unfold twoSidedVal
  split_ifs <;> linarith

/-- **The equal-left-data case of the separation.** When the two rejection intervals share
their left boundary *and* its randomization weight, the difference of the two values has a
constant sign, so it can never be both positive somewhere and negative somewhere. This is
the case `twoSidedVal_sub_sep` does not cover (its `hright` requires the left data to
differ), and together the two exhaust the trichotomy on `(C₁, γ₁)`. -/
private lemma twoSidedVal_sub_sep_eqLeft {C₁ C₂ C₂' γ₁ γ₂ γ₂' : ℝ}
    (hC : C₁ < C₂) (hC' : C₁ < C₂')
    (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1) (hγ₂' : γ₂' ∈ Set.Icc (0 : ℝ) 1) {s t : ℝ}
    (hs : 0 < twoSidedVal C₁ C₂' γ₁ γ₂' s - twoSidedVal C₁ C₂ γ₁ γ₂ s)
    (ht : twoSidedVal C₁ C₂' γ₁ γ₂' t - twoSidedVal C₁ C₂ γ₁ γ₂ t < 0) :
    False := by
  rcases lt_trichotomy C₂ C₂' with h | h | h
  · linarith [twoSidedVal_le_of_lt_right (γ₁ := γ₁) hC hγ₂ hγ₂'.1 h t]
  · subst h
    rcases le_total γ₂ γ₂' with hg | hg
    · linarith [twoSidedVal_le_of_le_gamma₂ (C₁ := C₁) (C₂ := C₂) (γ₁ := γ₁) hg t]
    · linarith [twoSidedVal_le_of_le_gamma₂ (C₁ := C₁) (C₂ := C₂) (γ₁ := γ₁) hg s]
  · linarith [twoSidedVal_le_of_lt_right (γ₁ := γ₁) hC' hγ₂' hγ₂.1 h s]

/-- **The analytic core of the two-sided uniqueness theorem.** Let `D` be a function of the
statistic `T` whose negative part lies strictly below its positive part along `T` (the
single-sign-change structure produced by `twoSidedVal_sub_sep`), and let `p₁, p₂` be
strictly positive densities whose likelihood ratio is strictly increasing along `T`. If `D`
integrates to zero against both densities, then `D` vanishes `μ`-almost everywhere.

The mechanism: the sign change gives a real `k` separating the ratio `p₂/p₁` across the sign
change, so `D·(p₂ − k·p₁) ≥ 0` pointwise while its integral is `0 − k·0 = 0`; hence
`D = 0` or `p₂ = k·p₁` a.e. Strict monotonicity of the ratio confines `{p₂ = k·p₁}` to a
single level set of `T`, on which `D` is constant, and the vanishing of `∫ D·p₁` kills that
last constant too. -/
private lemma ae_eq_zero_of_sep {μ : Measure 𝓧} {T D p₁ p₂ : 𝓧 → ℝ}
    (hp₁ : ∀ x, 0 < p₁ x) (hp₁int : Integrable p₁ μ)
    (hstrict : ∀ x y, T x < T y → p₂ x * p₁ y < p₁ x * p₂ y)
    (hsep : ∀ x y, D x < 0 → 0 < D y → T x < T y)
    (hDT : ∀ x y, T x = T y → D x = D y)
    (hint₁ : Integrable (fun x => D x * p₁ x) μ)
    (hint₂ : Integrable (fun x => D x * p₂ x) μ)
    (h₁ : ∫ x, D x * p₁ x ∂μ = 0) (h₂ : ∫ x, D x * p₂ x ∂μ = 0) :
    D =ᵐ[μ] 0 := by
  have hcancel : ∀ x, D x * p₁ x = 0 → D x = 0 := fun x hx =>
    (mul_eq_zero.mp hx).resolve_right (ne_of_gt (hp₁ x))
  by_cases hneg : ∃ x, D x < 0
  swap
  · -- `D ≥ 0` everywhere: a nonnegative integrand with zero integral.
    push_neg at hneg
    have hnn : 0 ≤ᵐ[μ] fun x => D x * p₁ x :=
      Filter.Eventually.of_forall fun x => mul_nonneg (hneg x) (hp₁ x).le
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint₁).mp h₁] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    exact hcancel x hx
  by_cases hpos : ∃ y, 0 < D y
  swap
  · -- `D ≤ 0` everywhere: the same, applied to `−D·p₁`.
    push_neg at hpos
    have hnn : 0 ≤ᵐ[μ] fun x => -(D x * p₁ x) :=
      Filter.Eventually.of_forall fun x => by
        change (0 : ℝ) ≤ -(D x * p₁ x)
        nlinarith [mul_nonneg (neg_nonneg.mpr (hpos x)) (hp₁ x).le]
    have hz : ∫ x, -(D x * p₁ x) ∂μ = 0 := by rw [integral_neg, h₁, neg_zero]
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint₁.neg).mp hz] with x hx
    simp only [Pi.zero_apply, neg_eq_zero] at hx ⊢
    exact hcancel x hx
  obtain ⟨x₀, hx₀⟩ := hneg
  obtain ⟨y₀, hy₀⟩ := hpos
  -- The likelihood ratio is strictly larger on `{D > 0}` than on `{D < 0}`.
  have hratio : ∀ x y, D x < 0 → 0 < D y → p₂ x / p₁ x < p₂ y / p₁ y := by
    intro x y hx hy
    rw [div_lt_div_iff₀ (hp₁ x) (hp₁ y), mul_comm (p₂ y) (p₁ x)]
    exact hstrict x y (hsep x y hx hy)
  have hSne : {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x}.Nonempty :=
    ⟨p₂ x₀ / p₁ x₀, x₀, hx₀, rfl⟩
  have hSub : ∀ y, 0 < D y →
      ∀ c ∈ {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x}, c ≤ p₂ y / p₁ y := by
    rintro y hy c ⟨x, hx, rfl⟩
    exact (hratio x y hx hy).le
  have hbdd : BddAbove {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x} :=
    ⟨p₂ y₀ / p₁ y₀, hSub y₀ hy₀⟩
  set k := sSup {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x} with hkdef
  have hkle : ∀ x, D x < 0 → p₂ x / p₁ x ≤ k := fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  have hkge : ∀ y, 0 < D y → k ≤ p₂ y / p₁ y := fun y hy => csSup_le hSne (hSub y hy)
  -- `D·(p₂ − k·p₁) ≥ 0` pointwise, with zero integral.
  have hg : ∀ x, 0 ≤ D x * p₂ x - k * (D x * p₁ x) := by
    intro x
    rcases lt_trichotomy (D x) 0 with h | h | h
    · have h2 := hkle x h
      rw [div_le_iff₀ (hp₁ x)] at h2
      nlinarith [mul_nonneg (neg_nonneg.mpr h.le) (sub_nonneg.mpr h2)]
    · rw [h]; simp
    · have h2 := hkge x h
      rw [le_div_iff₀ (hp₁ x)] at h2
      nlinarith [mul_nonneg h.le (sub_nonneg.mpr h2)]
  have hkint : Integrable (fun x => k * (D x * p₁ x)) μ := hint₁.const_mul k
  have hgint : Integrable (fun x => D x * p₂ x - k * (D x * p₁ x)) μ := hint₂.sub hkint
  have hgzero : ∫ x, (D x * p₂ x - k * (D x * p₁ x)) ∂μ = 0 := by
    rw [integral_sub hint₂ hkint, integral_const_mul, h₁, h₂]
    ring
  have hdisj : ∀ᵐ x ∂μ, D x = 0 ∨ p₂ x = k * p₁ x := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall hg) hgint).mp hgzero] with x hx
    simp only [Pi.zero_apply] at hx
    have hrw : D x * (p₂ x - k * p₁ x) = 0 := by linear_combination hx
    rcases mul_eq_zero.mp hrw with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  by_cases hexc : ∃ x, D x ≠ 0 ∧ p₂ x = k * p₁ x
  swap
  · push_neg at hexc
    filter_upwards [hdisj] with x hx
    simp only [Pi.zero_apply]
    rcases hx with h | h
    · exact h
    · by_contra hD
      exact hexc x hD h
  obtain ⟨x₁, hx₁D, hx₁r⟩ := hexc
  -- Strict monotonicity of the ratio pins `{p₂ = k·p₁} ∩ {D ≠ 0}` to one level of `T`.
  have hlevel : ∀ x, D x ≠ 0 → p₂ x = k * p₁ x → T x = T x₁ := by
    intro x hxD hxr
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hlt := hstrict x x₁ h
      rw [hxr, hx₁r] at hlt; linarith
    · have hlt := hstrict x₁ x h
      rw [hxr, hx₁r] at hlt; linarith
  have hDzero : ∀ᵐ x ∂μ, x ∉ {y : 𝓧 | T y = T x₁} → D x = 0 := by
    filter_upwards [hdisj] with x hx hxE
    rcases hx with h | h
    · exact h
    · by_contra hD
      exact hxE (hlevel x hD h)
  -- Multiplying by the CONSTANT `D x₁` makes `D·p₁` a.e. nonnegative — a.e. either `D`
  -- vanishes or `D = D x₁` — while its integral is `0 · D x₁ = 0`. So a.e. either `D x = 0`
  -- or `D x₁ ^ 2 · p₁ x = 0`, and the latter is impossible since `p₁ > 0` and `D x₁ ≠ 0`.
  have hqnn : 0 ≤ᵐ[μ] fun x => D x * p₁ x * D x₁ := by
    filter_upwards [hDzero] with x hx
    change (0 : ℝ) ≤ D x * p₁ x * D x₁
    by_cases hxE : x ∈ {y : 𝓧 | T y = T x₁}
    · rw [hDT x x₁ hxE]
      nlinarith [mul_nonneg (mul_self_nonneg (D x₁)) (hp₁ x).le]
    · rw [hx hxE]; simp
  have hqint : Integrable (fun x => D x * p₁ x * D x₁) μ := hint₁.mul_const (D x₁)
  have hqz : ∫ x, D x * p₁ x * D x₁ ∂μ = 0 := by rw [integral_mul_const, h₁, zero_mul]
  filter_upwards [hDzero, (integral_eq_zero_iff_of_nonneg_ae hqnn hqint).mp hqz] with x hx hq
  simp only [Pi.zero_apply] at hq ⊢
  by_cases hxE : x ∈ {y : 𝓧 | T y = T x₁}
  · rw [hDT x x₁ hxE] at hq ⊢
    have h0 : D x₁ * D x₁ * p₁ x = 0 := by linear_combination hq
    exact absurd (mul_self_eq_zero.mp
      ((mul_eq_zero.mp h0).resolve_right (ne_of_gt (hp₁ x)))) hx₁D
  · exact hx hxE

/-- The two orientations of the sign change are handled at once: replacing `D` by `−D` turns
the second alternative into the first. -/
private lemma ae_eq_zero_of_sep_or {μ : Measure 𝓧} {T D p₁ p₂ : 𝓧 → ℝ}
    (hp₁ : ∀ x, 0 < p₁ x) (hp₁int : Integrable p₁ μ)
    (hstrict : ∀ x y, T x < T y → p₂ x * p₁ y < p₁ x * p₂ y)
    (hsep : (∀ x y, D x < 0 → 0 < D y → T x < T y) ∨
      (∀ x y, 0 < D x → D y < 0 → T x < T y))
    (hDT : ∀ x y, T x = T y → D x = D y)
    (hint₁ : Integrable (fun x => D x * p₁ x) μ)
    (hint₂ : Integrable (fun x => D x * p₂ x) μ)
    (h₁ : ∫ x, D x * p₁ x ∂μ = 0) (h₂ : ∫ x, D x * p₂ x ∂μ = 0) :
    D =ᵐ[μ] 0 := by
  rcases hsep with h | h
  · exact ae_eq_zero_of_sep hp₁ hp₁int hstrict h hDT hint₁ hint₂ h₁ h₂
  · have hneg : ∀ (q : 𝓧 → ℝ), Integrable (fun x => D x * q x) μ →
        Integrable (fun x => (-D x) * q x) μ := by
      intro q hq
      have h0 : Integrable (fun x => (-1 : ℝ) * (D x * q x)) μ := hq.const_mul (-1)
      refine h0.congr (Filter.Eventually.of_forall fun x => ?_)
      change (-1 : ℝ) * (D x * q x) = (-D x) * q x
      ring
    have hnegz : ∀ (q : 𝓧 → ℝ), ∫ x, D x * q x ∂μ = 0 → ∫ x, (-D x) * q x ∂μ = 0 := by
      intro q hq
      rw [show (fun x => (-D x) * q x) = fun x => -(D x * q x) from funext fun x => by ring,
        integral_neg, hq, neg_zero]
    have hres := ae_eq_zero_of_sep (D := fun x => -D x) hp₁ hp₁int hstrict
      (fun x y hx hy => by
        have hx' : -D x < 0 := hx
        have hy' : (0 : ℝ) < -D y := hy
        exact h x y (by linarith) (by linarith))
      (fun x y hxy => by simp only [hDT x y hxy])
      (hneg p₁ hint₁) (hneg p₂ hint₂) (hnegz p₁ h₁) (hnegz p₂ h₂)
    filter_upwards [hres] with x hx
    have hx' : -D x = 0 := hx
    simp only [Pi.zero_apply]
    linarith

/-- **The strict form of the analytic core.** Same single-sign-change structure as
`ae_eq_zero_of_sep`, but the second vanishing integral is replaced by the *nondegeneracy*
hypothesis `¬ D =ᵐ[μ] 0`, and the conclusion is upgraded from `≥ 0` to `> 0`: a difference
whose negative part lies strictly below its positive part along `T`, which integrates to
zero against the lower member and does not vanish almost everywhere, has a strictly positive
integral against the upper member.

The mechanism is the same separating constant `k` for the ratio `p₂/p₁`, giving
`D·(p₂ − k·p₁) ≥ 0` pointwise with integral `∫D p₂ − k·0`. Strictness is where the
nondegeneracy is consumed: were that integral zero, the set `{p₂ = k·p₁}` would have to
carry both a point with `D < 0` and a point with `D > 0`, while strict monotonicity of the
ratio confines it to a single level set of `T` — contradicting the sign change. -/
private lemma integral_pos_of_sep {μ : Measure 𝓧} {T D p₁ p₂ : 𝓧 → ℝ}
    (hp₁ : ∀ x, 0 < p₁ x)
    (hstrict : ∀ x y, T x < T y → p₂ x * p₁ y < p₁ x * p₂ y)
    (hsep : ∀ x y, D x < 0 → 0 < D y → T x < T y)
    (hint₁ : Integrable (fun x => D x * p₁ x) μ)
    (hint₂ : Integrable (fun x => D x * p₂ x) μ)
    (h₁ : ∫ x, D x * p₁ x ∂μ = 0) (hne : ¬ D =ᵐ[μ] 0) :
    0 < ∫ x, D x * p₂ x ∂μ := by
  have hcancel : ∀ x, D x * p₁ x = 0 → D x = 0 := fun x hx =>
    (mul_eq_zero.mp hx).resolve_right (ne_of_gt (hp₁ x))
  -- Both signs occur: a one-signed `D` with `∫D p₁ = 0` and `p₁ > 0` vanishes a.e.
  have hnegex : ¬ (∀ᵐ x ∂μ, 0 ≤ D x) := by
    intro h
    refine hne ?_
    have hnn : 0 ≤ᵐ[μ] fun x => D x * p₁ x := by
      filter_upwards [h] with x hx
      exact mul_nonneg hx (hp₁ x).le
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint₁).mp h₁] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    exact hcancel x hx
  have hposex : ¬ (∀ᵐ x ∂μ, D x ≤ 0) := by
    intro h
    refine hne ?_
    have hnn : 0 ≤ᵐ[μ] fun x => -(D x * p₁ x) := by
      filter_upwards [h] with x hx
      change (0 : ℝ) ≤ -(D x * p₁ x)
      nlinarith [mul_nonneg (neg_nonneg.mpr hx) (hp₁ x).le]
    have hz : ∫ x, -(D x * p₁ x) ∂μ = 0 := by rw [integral_neg, h₁, neg_zero]
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint₁.neg).mp hz] with x hx
    simp only [Pi.zero_apply, neg_eq_zero] at hx ⊢
    exact hcancel x hx
  obtain ⟨x₀, hx₀⟩ : ∃ x, D x < 0 := by
    by_contra hc
    push_neg at hc
    exact hnegex (Filter.Eventually.of_forall hc)
  obtain ⟨y₀, hy₀⟩ : ∃ y, 0 < D y := by
    by_contra hc
    push_neg at hc
    exact hposex (Filter.Eventually.of_forall hc)
  -- The separating ratio constant.
  have hratio : ∀ x y, D x < 0 → 0 < D y → p₂ x / p₁ x < p₂ y / p₁ y := by
    intro x y hx hy
    rw [div_lt_div_iff₀ (hp₁ x) (hp₁ y), mul_comm (p₂ y) (p₁ x)]
    exact hstrict x y (hsep x y hx hy)
  have hSne : {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x}.Nonempty :=
    ⟨p₂ x₀ / p₁ x₀, x₀, hx₀, rfl⟩
  have hSub : ∀ y, 0 < D y →
      ∀ c ∈ {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x}, c ≤ p₂ y / p₁ y := by
    rintro y hy c ⟨x, hx, rfl⟩
    exact (hratio x y hx hy).le
  have hbdd : BddAbove {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x} :=
    ⟨p₂ y₀ / p₁ y₀, hSub y₀ hy₀⟩
  set k := sSup {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x} with hkdef
  have hkle : ∀ x, D x < 0 → p₂ x / p₁ x ≤ k := fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  have hkge : ∀ y, 0 < D y → k ≤ p₂ y / p₁ y := fun y hy => csSup_le hSne (hSub y hy)
  have hg : ∀ x, 0 ≤ D x * p₂ x - k * (D x * p₁ x) := by
    intro x
    rcases lt_trichotomy (D x) 0 with h | h | h
    · have h2 := hkle x h
      rw [div_le_iff₀ (hp₁ x)] at h2
      nlinarith [mul_nonneg (neg_nonneg.mpr h.le) (sub_nonneg.mpr h2)]
    · rw [h]; simp
    · have h2 := hkge x h
      rw [le_div_iff₀ (hp₁ x)] at h2
      nlinarith [mul_nonneg h.le (sub_nonneg.mpr h2)]
  have hkint : Integrable (fun x => k * (D x * p₁ x)) μ := hint₁.const_mul k
  have hgint : Integrable (fun x => D x * p₂ x - k * (D x * p₁ x)) μ := hint₂.sub hkint
  have hgval : ∫ x, (D x * p₂ x - k * (D x * p₁ x)) ∂μ = ∫ x, D x * p₂ x ∂μ := by
    rw [integral_sub hint₂ hkint, integral_const_mul, h₁, mul_zero, sub_zero]
  have hnn : 0 ≤ ∫ x, (D x * p₂ x - k * (D x * p₁ x)) ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall hg)
  rcases eq_or_lt_of_le hnn with heq | hlt
  · exfalso
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall hg) hgint).mp heq.symm
    have hdisj : ∀ᵐ x ∂μ, D x = 0 ∨ p₂ x = k * p₁ x := by
      filter_upwards [hae] with x hx
      simp only [Pi.zero_apply] at hx
      have hrw : D x * (p₂ x - k * p₁ x) = 0 := by linear_combination hx
      rcases mul_eq_zero.mp hrw with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    obtain ⟨x, hxD, hxr⟩ : ∃ x, D x < 0 ∧ p₂ x = k * p₁ x := by
      by_contra hc
      push_neg at hc
      refine hnegex ?_
      filter_upwards [hdisj] with x hx
      rcases hx with h | h
      · exact le_of_eq h.symm
      · by_contra hlt0
        push_neg at hlt0
        exact absurd h (hc x hlt0)
    obtain ⟨y, hyD, hyr⟩ : ∃ y, 0 < D y ∧ p₂ y = k * p₁ y := by
      by_contra hc
      push_neg at hc
      refine hposex ?_
      filter_upwards [hdisj] with x hx
      rcases hx with h | h
      · exact le_of_eq h
      · by_contra hlt0
        push_neg at hlt0
        exact absurd h (hc x hlt0)
    have hcmp := hstrict x y (hsep x y hxD hyD)
    rw [hxr, hyr] at hcmp
    have hid : k * p₁ x * p₁ y = p₁ x * (k * p₁ y) := by ring
    linarith
  · rw [hgval] at hlt
    exact hlt

/-- Expectation against a density-carrying measure equals the integral against the density
(local copy: the `MLR/OneSided` version is `private` to that file). -/
private lemma ts_integral_density_eq {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    (h : HasDensity μ p P) (ψ : 𝓧 → ℝ) : ∫ x, ψ x ∂P = ∫ x, ψ x * p x ∂μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  rw [hPeq, integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hnn x)]; ring

/-- A density of a probability measure is integrable (local copy). -/
private lemma ts_density_integrable {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    [IsProbabilityMeasure P] (h : HasDensity μ p P) : Integrable p μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  have h1 : (μ.withDensity fun x => ENNReal.ofReal (p x)) Set.univ = 1 := by
    rw [← hPeq]; exact measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [h1]; exact ENNReal.one_lt_top

/-- If `ψ` is `P`-integrable and `P` has density `p`, then `ψ·p` is `μ`-integrable
(local copy). -/
private lemma ts_density_mul_integrable {μ : Measure 𝓧} {p ψ : 𝓧 → ℝ} {P : Measure 𝓧}
    (h : HasDensity μ p P) (hψ : Integrable ψ P) : Integrable (fun x => ψ x * p x) μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  rw [hPeq] at hψ
  refine ((integrable_withDensity_iff hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hψ).congr ?_
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (hnn x)]

/-- The density integrates to `1` (local copy). -/
private lemma ts_density_integral_one {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    [IsProbabilityMeasure P] (h : HasDensity μ p P) : ∫ x, p x ∂μ = 1 := by
  have h1 : ∫ x, (1 : ℝ) ∂P = ∫ x, (1 : ℝ) * p x ∂μ := ts_integral_density_eq h (fun _ => 1)
  simp only [one_mul] at h1
  rw [← h1]; simp

/-! ### Two exponentials crossing a constant twice

The multiplier shape produced by the generalized fundamental lemma is
`{p_θ > k₁p_{θ₁} + k₂p_{θ₂}}`; in canonical form this is `{S(T) < 1}` for
`S(t) = A e^{b₁t} + B e^{b₂t}`. The three lemmas below identify the shape with an interval
of the statistic when the two exponents have the same sign — the configuration that occurs
for `θ` *outside* `[θ₁, θ₂]`. No calculus is used: after multiplying by the appropriate
`e^{-b_j t}` the function `1 - S` becomes a positive combination of two exponentials plus a
constant, hence strictly convex, and a strictly convex function with two zeros has a forced
sign pattern. -/

/-- A positive combination of two exponentials of nonconstant affine arguments, plus a
constant, is strictly convex. -/
private lemma strictConvexOn_two_exp {c₁ c₂ a₁ a₂ d : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    StrictConvexOn ℝ Set.univ
      fun t : ℝ => c₁ * Real.exp (a₁ * t) + c₂ * Real.exp (a₂ * t) + d := by
  refine ⟨convex_univ, fun x _ y _ hxy q r hq hr hqr => ?_⟩
  have hne₁ : a₁ * x ≠ a₁ * y := fun h => hxy (mul_left_cancel₀ ha₁ h)
  have hne₂ : a₂ * x ≠ a₂ * y := fun h => hxy (mul_left_cancel₀ ha₂ h)
  have h₁ := strictConvexOn_exp.2 (Set.mem_univ (a₁ * x)) (Set.mem_univ (a₁ * y)) hne₁ hq hr hqr
  have h₂ := strictConvexOn_exp.2 (Set.mem_univ (a₂ * x)) (Set.mem_univ (a₂ * y)) hne₂ hq hr hqr
  simp only [smul_eq_mul] at h₁ h₂ ⊢
  have e₁ : a₁ * (q * x + r * y) = q * (a₁ * x) + r * (a₁ * y) := by ring
  have e₂ : a₂ * (q * x + r * y) = q * (a₂ * x) + r * (a₂ * y) := by ring
  rw [e₁, e₂]
  have g₁ := mul_lt_mul_of_pos_left h₁ hc₁
  have g₂ := mul_lt_mul_of_pos_left h₂ hc₂
  have hd : q * d + r * d = d := by rw [← add_mul, hqr, one_mul]
  nlinarith [g₁, g₂, hd]

/-- A strictly convex function vanishing at two points is negative strictly between them
and positive strictly outside. -/
private lemma sign_of_strictConvexOn_two_zeros {g : ℝ → ℝ}
    (hg : StrictConvexOn ℝ Set.univ g) {C₁ C₂ : ℝ} (hC : C₁ < C₂)
    (h1 : g C₁ = 0) (h2 : g C₂ = 0) :
    (∀ t : ℝ, C₁ < t → t < C₂ → g t < 0) ∧ (∀ t : ℝ, t < C₁ → 0 < g t) ∧
      (∀ t : ℝ, C₂ < t → 0 < g t) := by
  have hkey : ∀ x y z : ℝ, x < y → y < z →
      g y < ((z - y) / (z - x)) * g x + ((y - x) / (z - x)) * g z := by
    intro x y z hxy hyz
    have hxz : x < z := hxy.trans hyz
    have hden : 0 < z - x := by linarith
    have ha : 0 < (z - y) / (z - x) := div_pos (by linarith) hden
    have hb : 0 < (y - x) / (z - x) := div_pos (by linarith) hden
    have hab : (z - y) / (z - x) + (y - x) / (z - x) = 1 := by field_simp; ring
    have hcomb : ((z - y) / (z - x)) * x + ((y - x) / (z - x)) * z = y := by
      field_simp; ring
    have hcx := hg.2 (Set.mem_univ x) (Set.mem_univ z) (ne_of_lt hxz) ha hb hab
    simp only [smul_eq_mul] at hcx
    rwa [hcomb] at hcx
  refine ⟨fun t ht1 ht2 => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have := hkey C₁ t C₂ ht1 ht2
    rw [h1, h2] at this
    linarith
  · have hlt := hkey t C₁ C₂ ht hC
    rw [h1, h2] at hlt
    have ha : 0 < (C₂ - C₁) / (C₂ - t) := div_pos (by linarith) (by linarith)
    by_contra hcon
    push_neg at hcon
    nlinarith
  · have hlt := hkey C₁ C₂ t hC ht
    rw [h1, h2] at hlt
    have hb : 0 < (C₂ - C₁) / (t - C₁) := div_pos (by linarith) (by linarith)
    by_contra hcon
    push_neg at hcon
    nlinarith

/-- **Two exponentials crossing a constant twice.** For exponents `b₁ < b₂` of the same
nonzero sign and points `C₁ < C₂` there are coefficients `A, B` for which
`S(t) = A e^{b₁t} + B e^{b₂t}` equals `1` at `C₁` and `C₂`, exceeds `1` strictly between
them, and falls strictly below `1` outside. The coefficients are the solution of the `2×2`
interpolation system, and their signs (`A` of the sign of `b₂`, `B` of the opposite sign to
`b₁`) are exactly what makes the rescaled function `e^{-b_jt}(1 - S(t))` a positive
combination of exponentials. -/
private lemma exists_exp_pair_sign {b₁ b₂ C₁ C₂ : ℝ} (hb : b₁ < b₂) (hbb : 0 < b₁ * b₂)
    (hC : C₁ < C₂) :
    ∃ A B : ℝ,
      A * Real.exp (b₁ * C₁) + B * Real.exp (b₂ * C₁) = 1 ∧
      A * Real.exp (b₁ * C₂) + B * Real.exp (b₂ * C₂) = 1 ∧
      (∀ t : ℝ, C₁ < t → t < C₂ → 1 < A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t)) ∧
      (∀ t : ℝ, t < C₁ → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) ∧
      (∀ t : ℝ, C₂ < t → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) := by
  have hΔ : 0 < Real.exp (b₁ * C₁) * Real.exp (b₂ * C₂)
      - Real.exp (b₁ * C₂) * Real.exp (b₂ * C₁) := by
    rw [← Real.exp_add, ← Real.exp_add, sub_pos, Real.exp_lt_exp]
    nlinarith [mul_pos (sub_pos.mpr hb) (sub_pos.mpr hC)]
  set Δ := Real.exp (b₁ * C₁) * Real.exp (b₂ * C₂)
    - Real.exp (b₁ * C₂) * Real.exp (b₂ * C₁) with hΔdef
  set A := (Real.exp (b₂ * C₂) - Real.exp (b₂ * C₁)) / Δ with hAdef
  set B := (Real.exp (b₁ * C₁) - Real.exp (b₁ * C₂)) / Δ with hBdef
  have hΔne : Δ ≠ 0 := ne_of_gt hΔ
  have hv₁ : A * Real.exp (b₁ * C₁) + B * Real.exp (b₂ * C₁) = 1 := by
    rw [hAdef, hBdef, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_iff hΔne, one_mul, hΔdef]
    ring
  have hv₂ : A * Real.exp (b₁ * C₂) + B * Real.exp (b₂ * C₂) = 1 := by
    rw [hAdef, hBdef, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_iff hΔne, one_mul, hΔdef]
    ring
  -- The sign pattern, from strict convexity of the rescaled `1 - S`.
  have hmain : (∀ t : ℝ, C₁ < t → t < C₂ →
        1 < A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t)) ∧
      (∀ t : ℝ, t < C₁ → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) ∧
      (∀ t : ℝ, C₂ < t → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) := by
    -- A rescaling factor `e^{-m t}` and a strictly convex `g = e^{-m t}(1 - S)`.
    have hgen : ∀ m : ℝ, ∀ g : ℝ → ℝ, StrictConvexOn ℝ Set.univ g →
        (∀ t : ℝ, g t
          = Real.exp (-m * t) * (1 - (A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t)))) →
        (∀ t : ℝ, C₁ < t → t < C₂ → 1 < A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t)) ∧
          (∀ t : ℝ, t < C₁ → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) ∧
          (∀ t : ℝ, C₂ < t → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) := by
      intro m g hgc hgrel
      have hg1 : g C₁ = 0 := by rw [hgrel C₁, hv₁]; ring
      have hg2 : g C₂ = 0 := by rw [hgrel C₂, hv₂]; ring
      obtain ⟨hin, hlo, hhi⟩ := sign_of_strictConvexOn_two_zeros hgc hC hg1 hg2
      refine ⟨fun t h1 h2 => ?_, fun t h => ?_, fun t h => ?_⟩
      · have hgt := hin t h1 h2
        rw [hgrel t] at hgt
        nlinarith [Real.exp_pos (-m * t)]
      · have hgt := hlo t h
        rw [hgrel t] at hgt
        nlinarith [Real.exp_pos (-m * t)]
      · have hgt := hhi t h
        rw [hgrel t] at hgt
        nlinarith [Real.exp_pos (-m * t)]
    rcases lt_trichotomy b₁ 0 with hb₁ | hb₁ | hb₁
    · -- Both exponents negative: rescale by `e^{-b₂t}`; then `A < 0` supplies the
      -- positive coefficient.
      have hb₂ : b₂ < 0 := by nlinarith
      have hAneg : A < 0 := by
        rw [hAdef]
        apply div_neg_of_neg_of_pos _ hΔ
        rw [sub_neg]
        exact Real.exp_lt_exp.mpr (by nlinarith)
      refine hgen b₂ (fun t => Real.exp (-b₂ * t) + (-A) * Real.exp ((b₁ - b₂) * t) + (-B))
        ?_ ?_
      · have h := strictConvexOn_two_exp (c₁ := 1) (c₂ := -A) (a₁ := -b₂) (a₂ := b₁ - b₂)
          (d := -B) one_pos (by linarith) (by intro h; nlinarith) (by intro h; nlinarith)
        refine h.congr ?_
        intro t _
        simp only [one_mul]
      · intro t
        rw [mul_sub, mul_one]
        have e₁ : Real.exp (-b₂ * t) * (A * Real.exp (b₁ * t))
            = -((-A) * Real.exp ((b₁ - b₂) * t)) := by
          rw [show (-A) * Real.exp ((b₁ - b₂) * t) = -(A * Real.exp ((b₁ - b₂) * t)) by ring]
          rw [neg_neg]
          rw [show Real.exp (-b₂ * t) * (A * Real.exp (b₁ * t))
              = A * (Real.exp (-b₂ * t) * Real.exp (b₁ * t)) by ring, ← Real.exp_add]
          congr 2
          ring
        have e₂ : Real.exp (-b₂ * t) * (B * Real.exp (b₂ * t)) = B := by
          rw [show Real.exp (-b₂ * t) * (B * Real.exp (b₂ * t))
              = B * (Real.exp (-b₂ * t) * Real.exp (b₂ * t)) by ring, ← Real.exp_add,
            show -b₂ * t + b₂ * t = 0 by ring, Real.exp_zero, mul_one]
        rw [mul_add, e₁, e₂]
        ring
    · exact absurd hbb (by rw [hb₁]; simp)
    · -- Both exponents positive: rescale by `e^{-b₁t}`; then `B < 0` supplies the
      -- positive coefficient.
      have hb₂ : 0 < b₂ := by linarith
      have hBneg : B < 0 := by
        rw [hBdef]
        apply div_neg_of_neg_of_pos _ hΔ
        rw [sub_neg]
        exact Real.exp_lt_exp.mpr (by nlinarith)
      refine hgen b₁ (fun t => Real.exp (-b₁ * t) + (-B) * Real.exp ((b₂ - b₁) * t) + (-A))
        ?_ ?_
      · have h := strictConvexOn_two_exp (c₁ := 1) (c₂ := -B) (a₁ := -b₁) (a₂ := b₂ - b₁)
          (d := -A) one_pos (by linarith) (by intro h; nlinarith) (by intro h; nlinarith)
        refine h.congr ?_
        intro t _
        simp only [one_mul]
      · intro t
        rw [mul_sub, mul_one]
        have e₁ : Real.exp (-b₁ * t) * (A * Real.exp (b₁ * t)) = A := by
          rw [show Real.exp (-b₁ * t) * (A * Real.exp (b₁ * t))
              = A * (Real.exp (-b₁ * t) * Real.exp (b₁ * t)) by ring, ← Real.exp_add,
            show -b₁ * t + b₁ * t = 0 by ring, Real.exp_zero, mul_one]
        have e₂ : Real.exp (-b₁ * t) * (B * Real.exp (b₂ * t))
            = -((-B) * Real.exp ((b₂ - b₁) * t)) := by
          rw [show (-B) * Real.exp ((b₂ - b₁) * t) = -(B * Real.exp ((b₂ - b₁) * t)) by ring]
          rw [neg_neg]
          rw [show Real.exp (-b₁ * t) * (B * Real.exp (b₂ * t))
              = B * (Real.exp (-b₁ * t) * Real.exp (b₂ * t)) by ring, ← Real.exp_add]
          congr 2
          ring
        rw [mul_add, e₁, e₂]
        ring
  exact ⟨A, B, hv₁, hv₂, hmain.1, hmain.2.1, hmain.2.2⟩

/-- The two-sided test is measurable when the statistic is. -/
private lemma measurable_twoSidedTest {T : 𝓧 → ℝ} (hT : Measurable T) (C₁ C₂ γ₁ γ₂ : ℝ) :
    Measurable (twoSidedTest T C₁ C₂ γ₁ γ₂) := by
  unfold twoSidedTest
  refine Measurable.ite (measurableSet_eq_fun hT measurable_const) measurable_const
    (Measurable.ite (measurableSet_eq_fun hT measurable_const) measurable_const
      (Measurable.ite ?_ measurable_const measurable_const))
  exact (measurableSet_lt measurable_const hT).inter (measurableSet_lt hT measurable_const)

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
  -- OBSTRUCTION (re-derived; the previously recorded upstream blockers are largely obsolete).
  -- ROADMAP (TSH4 Thm 3.7.1): apply the `m = 2` generalized fundamental lemma with
  -- `f₁ = p_{θ₁}`, `f₂ = p_{θ₂}`, `f₃ = p_θ` for `θ ∈ (θ₁, θ₂)` and constraint vector
  -- `c = (α, α)`. Upstream status is now:
  --   • `exists_test_max_integral_of_constraints` — PROVEN (existence of a maximizer);
  --   • `convex_isClosed_momentSet` — PROVEN (both halves);
  --   • `exists_multipliers_of_max` — PROVEN (supporting hyperplane at the top of the fibre);
  --   • `exists_test_with_prescribed_sizes` — still `sorry`, on a finite-dimensional duality
  --     step (see its docstring).
  -- Two gaps remain for THIS theorem, and neither is upstream:
  --   (1) INNER-POINT. `exists_multipliers_of_max` needs `(α, α) ∈ interior (momentSet μ
  --       ![p_{θ₁}, p_{θ₂}])` in `ℝ²`. That holds iff `p_{θ₁}, p_{θ₂}` are a.e. linearly
  --       independent, which is true here (strictly increasing `η` in a nondegenerate
  --       exponential family) but is not recorded anywhere and needs its own proof: from
  --       independence one must still deduce that the moment map is locally open at `α·𝟙`.
  --   (2) SHAPE-TO-INTERVAL. The multiplier shape `{p_θ > k₁p_{θ₁} + k₂p_{θ₂}}` must be
  --       identified with an *interval* `C₁ < T < C₂` of the natural statistic. In canonical
  --       form this is a strictly-convex-crossing statement for exponential sums —
  --       `k₁e^{a₁t} + k₂e^{a₂t} < e^{a₃t}` on an interval and `>` outside it, for
  --       `a₁ < a₃ < a₂` — with no Mathlib brick.
  -- TODO: prove (1) as a moment-set openness lemma and (2) as an exponential two-crossing
  -- lemma; the assembly is then `exists_multipliers_of_max` + `isMax_of_multiplier_form`.
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
  -- OBSTRUCTION (re-derived). ROADMAP (TSH4 Thm 3.7.1, minimizing clause): outside `[θ₁, θ₂]`
  -- apply the `m = 2` generalized fundamental lemma to the CO-test `1 − φ` — i.e. maximize
  -- `∫(1 − φ)p_θ` subject to the same two size conditions, which by
  -- `isMax_le_of_multiplier_form_nonneg` needs multipliers of the right sign.
  -- Upstream is no longer the blocker: `exists_multipliers_of_max` and
  -- `exists_test_max_integral_of_constraints` are both PROVEN now. What remains is exactly
  -- what this file must supply on its own:
  --   (1) the inner-point hypothesis `(α, α) ∈ interior (momentSet μ ![p_{θ₁}, p_{θ₂}])`
  --       (see the note on `isUMP_twoSided`), and
  --   (2) the SIGN of the multipliers `(k₁, k₂)` outside `[θ₁, θ₂]`. `exists_multipliers_of_max`
  --       delivers a `k`, but not `0 ≤ kᵢ`, and `isMax_le_of_multiplier_form_nonneg` needs
  --       nonnegativity to upgrade the competitor class from equality to inequality
  --       constraints. Deriving the sign is the exponential-family computation of TSH4
  --       Thm 3.7.1 and has no brick here yet.
  -- Unlike the one-sided case there is no single-likelihood-ratio shortcut:
  -- `power_min_oneSided` could reduce to the plain NP lemma because one constraint means one
  -- multiplier.
  -- TODO: moment-set openness lemma + the multiplier-sign computation, then the
  -- `isMax_le_of_multiplier_form_nonneg` assembly.
  sorry

/-- **Comparison of two two-sided tests with a common size at `θ₁`.** If the rejection
interval of the second test lies to the right of that of the first — a larger left
boundary, or the same boundary with a smaller randomization weight there — then the second
test is strictly more powerful above `θ₁` and strictly less powerful below it.

**Repaired statement (`hne`).** As printed — i.e. without `hne` — the theorem is FALSE, and
`hne` is the minimal repair. The conclusion is a *strict* inequality, but nothing in the
printed hypotheses forces the two tests to differ: `hstrict` is vacuous when `T` is
constant, since it only constrains pairs with `T x < T y`.

*Counterexample to the printed form.* `𝓧 = ℝ`, `μ = volume`, `p θ x = ϕ(x − θ)` (so
`hpos : 0 < p θ x` holds), and `T = fun _ => 0`, a measurable constant, so `hstrict` holds
vacuously. Take `C₁ = -2 < C₂ = -1`, `C₁' = 1 < C₂' = 2` and all four `γ = 0`; `hright`
holds as `C₁ = -2 < 1 = C₁'`. Both tests are identically `0`: at `t = 0` neither `t = Cᵢ`
nor `Cᵢ < t < Cᵢ₊₁` holds in either configuration. So `hsize` holds (`0 = 0`) while the
conclusion demands `0 < 0` at every `θ > θ₁`. The failure is not an artefact of the constant
statistic: it occurs whenever both rejection intervals miss the essential range of `T`, and
in every such configuration the two tests coincide `μ`-a.e.

*Repair.* Assume the two tests are not `μ`-a.e. equal (`hne`). This is exactly the
negation of the conclusion of the sibling theorem `twoSided_ae_unique`, so it adds no new
notion; since the densities are strictly positive it is equivalent to the two tests
differing on a set of positive `P θ`-probability for one — equivalently every — `θ`. It
cannot be weakened away: whenever the two tests *are* a.e. equal all four powers coincide
and both strict inequalities fail.

*Proof.* The Lehmann comparison in its strict form. `twoSidedVal_sub_sep` says the positive
part of `D = φ' − φ` sits strictly above its negative part along `T`; `hsize` makes
`∫D p_{θ₁} dμ = 0`; and `integral_pos_of_sep` turns strict MLR plus `hne` into
`∫D p_θ dμ > 0` for `θ₁ < θ`. Below `θ₁` the same lemma is applied to `−D` and `−T`, whose
sign change and ratio monotonicity are both reversed. -/
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
    (hright : C₁ < C₁' ∨ (C₁ = C₁' ∧ γ₁' < γ₁))
    -- REPAIR (see the docstring): the two tests are not `μ`-a.e. equal. Without it the
    -- printed statement is FALSE — a rejection interval missing the essential range of `T`
    -- makes both tests a.e. `0` and both strict inequalities fail
    (hne : ¬ twoSidedTest T C₁ C₂ γ₁ γ₂ =ᵐ[μ] twoSidedTest T C₁' C₂' γ₁' γ₂') :
    (∀ θ : ℝ, θ₁ < θ → power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ <
        power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ) ∧
      ∀ θ : ℝ, θ < θ₁ → power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ <
        power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ := by
  set φ := twoSidedTest T C₁ C₂ γ₁ γ₂ with hφdef
  set φ' := twoSidedTest T C₁' C₂' γ₁' γ₂' with hφ'def
  have hφc : IsCriticalFn φ := by
    refine ⟨measurable_twoSidedTest hT C₁ C₂ γ₁ γ₂, fun x => ?_⟩
    rw [hφdef, twoSidedTest_eq_val]
    exact twoSidedVal_mem_Icc hγ₁ hγ₂ (T x)
  have hφ'c : IsCriticalFn φ' := by
    refine ⟨measurable_twoSidedTest hT C₁' C₂' γ₁' γ₂', fun x => ?_⟩
    rw [hφ'def, twoSidedTest_eq_val]
    exact twoSidedVal_mem_Icc hγ₁' hγ₂' (T x)
  have hcrit_int : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → ∀ ϑ : ℝ, Integrable ψ (P ϑ) := by
    intro ψ hψ ϑ
    refine (integrable_const (1 : ℝ)).mono' hψ.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ.2 x).1]
    exact (hψ.2 x).2
  have hmul : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → ∀ ϑ : ℝ,
      Integrable (fun x => ψ x * p ϑ x) μ := fun ψ hψ ϑ =>
    ts_density_mul_integrable (hp ϑ) (hcrit_int ψ hψ ϑ)
  have hpow : ∀ (ψ : 𝓧 → ℝ) (ϑ : ℝ), power P ψ ϑ = ∫ x, ψ x * p ϑ x ∂μ := by
    intro ψ ϑ
    unfold power
    exact ts_integral_density_eq (hp ϑ) ψ
  have hDval : ∀ x, φ' x - φ x
      = twoSidedVal C₁' C₂' γ₁' γ₂' (T x) - twoSidedVal C₁ C₂ γ₁ γ₂ (T x) := by
    intro x
    rw [hφdef, hφ'def, twoSidedTest_eq_val, twoSidedTest_eq_val]
  have hDint : ∀ ϑ : ℝ, Integrable (fun x => (φ' x - φ x) * p ϑ x) μ := by
    intro ϑ
    refine ((hmul φ' hφ'c ϑ).sub (hmul φ hφc ϑ)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  -- The two size conditions at `θ₁` make the difference integrate to zero there.
  have h₁ : ∫ x, (φ' x - φ x) * p θ₁ x ∂μ = 0 := by
    have hcg : ∫ x, (φ' x - φ x) * p θ₁ x ∂μ
        = ∫ x, (φ' x * p θ₁ x - φ x * p θ₁ x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hcg, integral_sub (hmul φ' hφ'c θ₁) (hmul φ hφc θ₁), ← hpow φ' θ₁, ← hpow φ θ₁,
      hsize, sub_self]
  -- Nondegeneracy, transported to the difference.
  have hDne : ¬ (fun x => φ' x - φ x) =ᵐ[μ] 0 := by
    intro h
    refine hne ?_
    filter_upwards [h] with x hx
    have hx' : φ' x - φ x = 0 := hx
    linarith
  -- The single sign change: the negative part of `φ' − φ` lies strictly below its
  -- positive part along `T`.
  have hsep : ∀ x y, φ' x - φ x < 0 → 0 < φ' y - φ y → T x < T y := fun x y hx hy =>
    twoSidedVal_sub_sep hC hC' hγ₁ hγ₂ hγ₁' hγ₂' hright
      (by linarith [hDval y]) (by linarith [hDval x])
  constructor
  · intro θ hθ
    have hcore := integral_pos_of_sep (T := T) (D := fun x => φ' x - φ x)
      (p₁ := p θ₁) (p₂ := p θ) (hpos θ₁) (hstrict θ₁ θ hθ) hsep (hDint θ₁) (hDint θ) h₁ hDne
    have hsplit : ∫ x, (φ' x - φ x) * p θ x ∂μ = power P φ' θ - power P φ θ := by
      rw [hpow φ' θ, hpow φ θ, ← integral_sub (hmul φ' hφ'c θ) (hmul φ hφc θ)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hsplit] at hcore
    linarith
  · intro θ hθ
    -- Below `θ₁` both the sign change and the ratio monotonicity reverse; apply the same
    -- lemma to `−D` along `−T`.
    have hstrict' : ∀ x y, -T x < -T y → p θ x * p θ₁ y < p θ₁ x * p θ y := by
      intro x y hxy
      have hTy : T y < T x := by linarith
      have hs := hstrict θ θ₁ hθ y x hTy
      linarith [hs]
    have hsep' : ∀ x y, -(φ' x - φ x) < 0 → 0 < -(φ' y - φ y) → -T x < -T y := by
      intro x y hx hy
      have h1 : 0 < φ' x - φ x := by linarith
      have h2 : φ' y - φ y < 0 := by linarith
      have h3 := hsep y x h2 h1
      linarith
    have hnegint : ∀ ϑ : ℝ, Integrable (fun x => -(φ' x - φ x) * p ϑ x) μ := by
      intro ϑ
      refine (hDint ϑ).neg.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.neg_apply]
      ring
    have hnegzero : ∫ x, -(φ' x - φ x) * p θ₁ x ∂μ = 0 := by
      rw [show (fun x => -(φ' x - φ x) * p θ₁ x) = fun x => -((φ' x - φ x) * p θ₁ x) from
        funext fun x => by ring, integral_neg, h₁, neg_zero]
    have hnegne : ¬ (fun x => -(φ' x - φ x)) =ᵐ[μ] 0 := by
      intro h
      refine hDne ?_
      filter_upwards [h] with x hx
      have hx' : -(φ' x - φ x) = 0 := hx
      simp only [Pi.zero_apply]
      linarith
    have hcore := integral_pos_of_sep (T := fun x => -T x) (D := fun x => -(φ' x - φ x))
      (p₁ := p θ₁) (p₂ := p θ) (hpos θ₁) hstrict' hsep' (hnegint θ₁) (hnegint θ)
      hnegzero hnegne
    have hsplit : ∫ x, -(φ' x - φ x) * p θ x ∂μ = power P φ θ - power P φ' θ := by
      rw [hpow φ' θ, hpow φ θ, ← integral_sub (hmul φ hφc θ) (hmul φ' hφ'c θ)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hsplit] at hcore
    linarith

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
  -- Unlike its sibling `power_lt_of_twoSided_right` (which is FALSE as stated), the
  -- degenerate constant-`T` configuration is harmless here: it forces the two tests to take
  -- the same constant value once their sizes agree. The proof is the Lehmann comparison in
  -- its equality form: the difference of the two tests changes sign at most once along `T`
  -- (`twoSidedVal_sub_sep` and `twoSidedVal_sub_sep_eqLeft`, exhausting the trichotomy on
  -- the left data), and a difference with a single sign change that integrates to zero
  -- against two members with a strict monotone likelihood ratio vanishes a.e.
  -- (`ae_eq_zero_of_sep_or`).
  set φ := twoSidedTest T C₁ C₂ γ₁ γ₂ with hφdef
  set φ' := twoSidedTest T C₁' C₂' γ₁' γ₂' with hφ'def
  have hφc : IsCriticalFn φ := by
    refine ⟨measurable_twoSidedTest hT C₁ C₂ γ₁ γ₂, fun x => ?_⟩
    rw [hφdef, twoSidedTest_eq_val]
    exact twoSidedVal_mem_Icc hγ₁ hγ₂ (T x)
  have hφ'c : IsCriticalFn φ' := by
    refine ⟨measurable_twoSidedTest hT C₁' C₂' γ₁' γ₂', fun x => ?_⟩
    rw [hφ'def, twoSidedTest_eq_val]
    exact twoSidedVal_mem_Icc hγ₁' hγ₂' (T x)
  have hcrit_int : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → ∀ ϑ : ℝ, Integrable ψ (P ϑ) := by
    intro ψ hψ ϑ
    refine (integrable_const (1 : ℝ)).mono' hψ.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ.2 x).1]
    exact (hψ.2 x).2
  have hmul : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → ∀ ϑ : ℝ,
      Integrable (fun x => ψ x * p ϑ x) μ := fun ψ hψ ϑ =>
    ts_density_mul_integrable (hp ϑ) (hcrit_int ψ hψ ϑ)
  have hpow : ∀ (ψ : 𝓧 → ℝ) (ϑ : ℝ), power P ψ ϑ = ∫ x, ψ x * p ϑ x ∂μ := by
    intro ψ ϑ
    unfold power
    exact ts_integral_density_eq (hp ϑ) ψ
  -- The difference of the two tests is a function of the statistic.
  have hDval : ∀ x, φ' x - φ x
      = twoSidedVal C₁' C₂' γ₁' γ₂' (T x) - twoSidedVal C₁ C₂ γ₁ γ₂ (T x) := by
    intro x
    rw [hφdef, hφ'def, twoSidedTest_eq_val, twoSidedTest_eq_val]
  have hDT : ∀ x y, T x = T y → φ' x - φ x = φ' y - φ y := by
    intro x y h
    rw [hDval x, hDval y, h]
  have hDint : ∀ ϑ : ℝ, Integrable (fun x => (φ' x - φ x) * p ϑ x) μ := by
    intro ϑ
    refine ((hmul φ' hφ'c ϑ).sub (hmul φ hφc ϑ)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  -- Equal sizes at a parameter value make the difference integrate to zero there.
  have hDzero : ∀ ϑ : ℝ, power P φ ϑ = power P φ' ϑ →
      ∫ x, (φ' x - φ x) * p ϑ x ∂μ = 0 := by
    intro ϑ heq
    have hcg : ∫ x, (φ' x - φ x) * p ϑ x ∂μ = ∫ x, (φ' x * p ϑ x - φ x * p ϑ x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hcg, integral_sub (hmul φ' hφ'c ϑ) (hmul φ hφc ϑ), ← hpow φ' ϑ, ← hpow φ ϑ, heq,
      sub_self]
  have h₁ := hDzero θ₁ (hsize₁.trans hsize₁'.symm)
  have h₂ := hDzero θ₂ (hsize₂.trans hsize₂'.symm)
  -- The single sign change, in whichever of its two orientations applies.
  have hsep : (∀ x y, φ' x - φ x < 0 → 0 < φ' y - φ y → T x < T y) ∨
      (∀ x y, 0 < φ' x - φ x → φ' y - φ y < 0 → T x < T y) := by
    rcases lt_trichotomy C₁ C₁' with hc | hc | hc
    · exact Or.inl fun x y hx hy => twoSidedVal_sub_sep hC hC' hγ₁ hγ₂ hγ₁' hγ₂'
        (Or.inl hc) (by linarith [hDval y]) (by linarith [hDval x])
    · rcases lt_trichotomy γ₁' γ₁ with hg | hg | hg
      · exact Or.inl fun x y hx hy => twoSidedVal_sub_sep hC hC' hγ₁ hγ₂ hγ₁' hγ₂'
          (Or.inr ⟨hc, hg⟩) (by linarith [hDval y]) (by linarith [hDval x])
      · subst hc
        subst hg
        exact Or.inl fun x y hx hy => (twoSidedVal_sub_sep_eqLeft hC hC' hγ₂ hγ₂'
          (by linarith [hDval y]) (by linarith [hDval x])).elim
      · exact Or.inr fun x y hx hy => twoSidedVal_sub_sep hC' hC hγ₁' hγ₂' hγ₁ hγ₂
          (Or.inr ⟨hc.symm, hg⟩) (by linarith [hDval y]) (by linarith [hDval x])
    · exact Or.inr fun x y hx hy => twoSidedVal_sub_sep hC' hC hγ₁' hγ₂' hγ₁ hγ₂
        (Or.inl hc) (by linarith [hDval y]) (by linarith [hDval x])
  have hcore := ae_eq_zero_of_sep_or (D := fun x => φ' x - φ x) (hpos θ₁)
    (ts_density_integrable (hp θ₁)) (hstrict θ₁ θ₂ hθ) hsep hDT (hDint θ₁) (hDint θ₂) h₁ h₂
  filter_upwards [hcore] with x hx
  have hx' : φ' x - φ x = 0 := hx
  linarith

end StatLean.HypothesisTesting
