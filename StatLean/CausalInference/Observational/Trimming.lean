import StatLean.CausalInference.Observational.ATT

/-!
# Overlap and trimming — bounded weights, and the estimand you actually get

Limited overlap is the practical failure mode of weighting: as `e(X)` approaches `0` or
`1` the inverse-probability weights explode. Two responses, and their consequences:

* **Strict overlap** `η ≤ e(X) ≤ 1 - η` bounds every weight by `1/η`, which is what makes
  weighting estimators stable.
* **Trimming** — discarding units outside a propensity range — restores stability but
  **changes the estimand**: what is identified afterwards is the average causal effect
  *over the retained subpopulation*, not `τ`. The overlap-weighted estimand `τ_O` is the
  smooth version of the same idea.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §11.2.3 (pp. 160–161: the strong overlap condition
`0 < α_L ≤ e(X) ≤ α_U < 1`, stated as an unlabeled display, and the weight blow-up with
truncation/trimming as remedies); ch. 20 (*Overlap in Observational Studies*),
**Assumption 20.1** (§20.1, p. 267: strict overlap `η ≤ e(X) ≤ 1 - η`, `η ∈ (0, 1/2)`);
**Theorem 13.4** and its table (p. 188: the `h`-weighted estimands, whose overlap row is
`h(X) = e(X){1 - e(X)}`, giving
`τ_O = E[e(1-e)τ(X)]/E[e(1-e)]`, with the noted reduction to `τ` when `τ(X)` is constant).
(`Ding §11.2.3; Assumption 20.1; Theorem 13.4`.) Assessing overlap and trimming are chs. 14
and 16 of G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and
Biomedical Sciences*, Cambridge University Press, 2015. (`IR chs. 14, 16`.)

**Scope.** That "trimming changes the estimand" is **prose** in both references (Ding
§11.2.3 p. 161 and §20.1.1 p. 268 discuss it and cite Crump et al. (2009) and Yang–Ding
(2018) rather than proving an in-book theorem). What is formalized here is the precise
version of that statement: the trimmed identification formula equals the average causal
effect *conditional on the retained set* (`trimmedEstimand_eq_cate_of_trimmedSet`), which
differs from `τ` unless the conditional effect is constant. Ding's **Theorem 20.1** (the
covariate-imbalance bound under strict overlap) is not formalized: it depends on
distributional constants imported from D'Amour et al. (2021) that the book does not develop.

**Proof formalization notes.** The trimmed population is the union of the covariate cells
whose propensity lies in `[η, 1-η]`; conditioning on it is `ProbabilityTheory.cond` on that
union, so the "changed estimand" statement is an application of
`Standardization.ate_eq_sum_cate` restricted to those cells. The weight bounds are pointwise
arithmetic from `StronglyOverlapping`.

**Bibliographic comments.** The optimal trimming rule is R. K. Crump, V. J. Hotz,
G. W. Imbens and O. A. Mitnik, "Dealing with limited overlap in estimation of average
treatment effects," *Biometrika* **96** (2009), 187–199; overlap weights are F. Li,
K. L. Morgan and A. M. Zaslavsky, *J. Amer. Statist. Assoc.* **113** (2018), 390–400;
the strict-overlap critique is A. D'Amour, P. Ding, A. Feller, L. Lei and J. Sekhon,
"Overlap in observational studies with high-dimensional covariates," *J. Econometrics*
**221** (2021), 644–654.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-- The **retained (trimmed) population**: the units whose covariate cell has propensity
score in `[η, 1 - η]` (Ding §11.2.3, Assumption 20.1). -/
def trimmedSet (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (η : ℝ) : Set Ω :=
  {ω | η ≤ propensity μ Z X (X ω) ∧ propensity μ Z X (X ω) ≤ 1 - η}

/-- **Strict overlap bounds the treated weight** (Ding Assumption 20.1): under
`η ≤ e(X) ≤ 1 - η` every inverse-probability weight is at most `1/η`. -/
theorem inv_propensity_le_of_mem_trimmedSet {η : ℝ}
    -- LEAN-ONLY: a positive trimming threshold, so `1/η` is finite
    (hη : 0 < η) {ω : Ω} (hω : ω ∈ trimmedSet μ Z X η) :
    1 / propensity μ Z X (X ω) ≤ 1 / η := by
  sorry

/-- **Strict overlap bounds the control weight** (Ding Assumption 20.1). -/
theorem inv_one_sub_propensity_le_of_mem_trimmedSet {η : ℝ} (hη : 0 < η) {ω : Ω}
    (hω : ω ∈ trimmedSet μ Z X η) :
    1 / (1 - propensity μ Z X (X ω)) ≤ 1 / η := by
  sorry

/-- Strict overlap in the sense of `StronglyOverlapping` means every unit that carries mass
is retained by trimming at the same threshold. -/
theorem stronglyOverlapping_iff_trimmedSet {η : ℝ} (hX : Measurable X) :
    StronglyOverlapping μ Z X η ↔ ∀ x : 𝒳, μ (cell X x) ≠ 0 → cell X x ⊆ trimmedSet μ Z X η := by
  sorry

/-- The **trimmed estimand**: the average causal effect over the retained population. -/
noncomputable def trimmedATE (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (y1 y0 : Ω → ℝ)
    (η : ℝ) : ℝ :=
  ∫ ω, (y1 ω - y0 ω) ∂(μ[|trimmedSet μ Z X η])

/-- **Trimming changes the estimand** (Ding §11.2.3, §20.1.1 — the precise form of the
book's prose warning): what the trimmed analysis identifies is the average causal effect
*conditional on the retained set*, i.e. the cell-weighted average of the conditional
effects over retained cells only. -/
theorem trimmedATE_eq_sum_cate [IsProbabilityMeasure μ] [DecidableEq 𝒳] {η : ℝ}
    (hZ : Measurable Z) (hX : Measurable X)
    -- USER-INPUT: integrability of the individual effect
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ)
    -- USER-INPUT: the retained population is nonnull, else the estimand is a junk value
    (hne : μ (trimmedSet μ Z X η) ≠ 0) :
    trimmedATE μ Z X y1 y0 η
      = (∑ x ∈ Finset.univ.filter fun x =>
            η ≤ propensity μ Z X x ∧ propensity μ Z X x ≤ 1 - η,
          (μ (cell X x)).toReal * cate μ X y1 y0 x)
        / (μ (trimmedSet μ Z X η)).toReal := by
  sorry

/-- **Trimming is harmless exactly when the effect is homogeneous**: if the conditional
average causal effect is constant, the trimmed estimand is the average causal effect. This
is the precise sense in which trimming "does not change the estimand" only under effect
homogeneity. -/
theorem trimmedATE_eq_ate_of_constant_cate [IsProbabilityMeasure μ] [DecidableEq 𝒳] {η τ : ℝ}
    (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ)
    (hne : μ (trimmedSet μ Z X η) ≠ 0)
    -- USER-INPUT: a homogeneous conditional effect; Ding Theorem 13.4's remark
    (hconst : ∀ x : 𝒳, μ (cell X x) ≠ 0 → cate μ X y1 y0 x = τ) :
    trimmedATE μ Z X y1 y0 η = ate μ y1 y0 := by
  sorry

/-- The **overlap-weighted estimand** `τ_O` (Ding Theorem 13.4's table, p. 188): the
smooth alternative to hard trimming, with weight `h(x) = e(x)(1 - e(x))` that downweights
extreme propensity scores. -/
noncomputable def overlapATE (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳)
    (y1 y0 : Ω → ℝ) : ℝ :=
  weightedATE μ X y1 y0 fun x => propensity μ Z X x * (1 - propensity μ Z X x)

/-- **The overlap-weighted estimand reduces to the average causal effect under a
homogeneous conditional effect** (Ding p. 188, the remark following Theorem 13.4's table).
-/
theorem overlapATE_eq_ate_of_constant_cate [IsProbabilityMeasure μ] {τ : ℝ}
    (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ)
    -- USER-INPUT: a homogeneous conditional effect; Ding p. 188
    (hconst : ∀ x : 𝒳, μ (cell X x) ≠ 0 → cate μ X y1 y0 x = τ)
    -- USER-INPUT: the overlap weight is not degenerate (some cell has `0 < e(x) < 1`)
    (hw : ∫ ω, propensity μ Z X (X ω) * (1 - propensity μ Z X (X ω)) ∂μ ≠ 0) :
    overlapATE μ Z X y1 y0 = ate μ y1 y0 := by
  sorry

end StatLean.CausalInference
