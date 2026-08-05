import StatLean.TimeSeries.Mixing.Inequalities
import StatLean.TimeSeries.Mixing.Relations
import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Limit theorems for α-mixing processes (FY §2.6.3, pp. 74–76)

* **Theorem 2.20(ii)** (in-text proof): bounded zero-mean strictly stationary with
  `Σ α(j) < ∞` ⇒ the ACVF is absolutely summable and
  `n⁻¹ Var(S_n) → γ(0) + 2 Σ_{j≥1} γ(j)` (eq. (2.63)). **Erratum**: the book's display
  bounds `|γ(j)| ≤ 4α(j){E|X_1|}²`; the correct Billingsley bound is `4α(j)C²` — we
  state and use the corrected form.
* **Theorem 2.21(ii)** (FULL in-text proof, pp. 75–76): additionally `σ² > 0` ⇒
  `S_n/√n →d N(0, σ²)`, `σ² = γ(0) + 2Σγ(j)` — the Bernstein-block scheme: big blocks
  of length `l_n`, small blocks `s_n` (`s_n → ∞`, `s_n/l_n → 0`, `l_n/n → 0`);
  small-block negligibility via the fourth-moment bound; characteristic-function
  factorization via Volkonskii–Rozanov (`16(k_n − 1)α(s_n) → 0`, using
  `α(n) = o(1/n)` from monotone + summable); big-block array CLT via the Lindeberg
  double-array theorem.
* **Theorem 2.20(i)/2.21(i)** — the `δ`-moment versions (cited Bosq / Peligrad):
  literature DEBTS.
* **Proposition 2.8 (SLLN)** — α-mixing + `E|X| < ∞` ⇒ `S_n/n → EX` a.s.: literature
  DEBT (the cited route is "α-mixing ⇒ ergodic" + Birkhoff; Mathlib has no pointwise
  ergodic theorem in the pin).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.3,
Prop 2.8, Thms 2.20–2.21, eq. (2.63) (pp. 74–76). (`FY §2.6.3`.)

**Proof formalization notes.**
* Summability statements are spelled inline (`Summable fun k : ℤ => |acvf X μ k|`)
  rather than through `Spectral/SpectralDensity.HasSummableACVF` — this concept-layer
  file must not import the spectral assembly.
* `σ²` is packaged as `acvf X μ 0 + 2 * Σ'_{j : ℕ} acvf X μ (j + 1)`.
* The α-coefficient of the blocks is controlled through
  `IsStrictlyStationary.alphaMixCoeff_shift` (Relations) + `alphaMixCoeff_mono`.

**Bibliographic comments.** The Bernstein small-block/large-block method is
S. N. Bernstein (1927); Theorem 2.21's proof follows Ibragimov–Linnik (1971) Thm 18.4.1
as streamlined by FY. The δ-moment CLT (i) is M. Peligrad (*Invariance principles for
mixing sequences*, Ann. Probab. 1982-adjacent); Thm 2.20(i) is Bosq (1998) §1.5. The
SLLN via ergodicity is Doob (1953) ch. X / Ibragimov–Linnik (1971) ch. 17.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Private toolbox for the bounded α-mixing limit theorems

Shared bricks for Theorems 2.20(ii) and 2.21(ii): the Billingsley bound on the ACVF,
absolute summability of the ACVF, the `Λ·|D|` bound on the second moment of a partial sum
over an arbitrary index set, and the exact "triangular-weight" expansion of a double sum
`∑_{s,t<n} f(s−t)`. -/

section Toolbox

variable {X : ℤ → Ω → ℝ} {C : ℝ}

/-- Boundedness on a probability space forces `0 ≤ C`. -/
private lemma bound_nonneg [IsProbabilityMeasure μ]
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) : 0 ≤ C := by
  obtain ⟨ω, hω⟩ := (hbdd 0).exists
  exact le_trans (abs_nonneg _) hω

/-- A bounded measurable coordinate lies in every `L^p`. -/
private lemma memLp_of_bdd [IsProbabilityMeasure μ] (hmeas : ∀ t, Measurable (X t))
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (t : ℤ) (p : ℝ≥0∞) : MemLp (X t) p μ := by
  refine MemLp.mono_exponent ?_ le_top
  refine memLp_top_of_bound (hmeas t).aestronglyMeasurable C ?_
  filter_upwards [hbdd t] with ω hω
  simpa [Real.norm_eq_abs] using hω

private lemma sigmaLE_le (hmeas : ∀ t, Measurable (X t)) (n : ℤ) :
    sigmaLE X n ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

private lemma sigmaGE_le (hmeas : ∀ t, Measurable (X t)) (n : ℤ) :
    sigmaGE X n ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

omit [MeasurableSpace Ω] in
private lemma measurable_comap_self (X : ℤ → Ω → ℝ) (s : ℤ) :
    Measurable[MeasurableSpace.comap (X s) inferInstance] (X s) :=
  fun _ hs => ⟨_, hs, rfl⟩

omit [MeasurableSpace Ω] in
private lemma comap_le_sigmaLE (X : ℤ → Ω → ℝ) {s n : ℤ} (h : s ≤ n) :
    MeasurableSpace.comap (X s) inferInstance ≤ sigmaLE X n :=
  le_iSup₂ (f := fun (s : ℤ) (_ : s ∈ Set.Iic n) =>
    MeasurableSpace.comap (X s) inferInstance) s h

omit [MeasurableSpace Ω] in
private lemma comap_le_sigmaGE (X : ℤ → Ω → ℝ) {s n : ℤ} (h : n ≤ s) :
    MeasurableSpace.comap (X s) inferInstance ≤ sigmaGE X n :=
  le_iSup₂ (f := fun (s : ℤ) (_ : s ∈ Set.Ici n) =>
    MeasurableSpace.comap (X s) inferInstance) s h

/-- **Billingsley bound on the ACVF** (FY Thm 2.20(ii), corrected constant `4α(n)C²`):
`γ(n) = Cov(X_n, X_0)` pairs the anchored past `σ{X_s : s ≤ 0}` (holding `X_0`) with the
future `σ{X_s : s ≥ n}` (holding `X_n`). -/
private lemma abs_acvf_le_alphaCoeff [IsProbabilityMeasure μ] (hmeas : ∀ t, Measurable (X t))
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (n : ℕ) :
    |acvf X μ (n : ℤ)| ≤ 4 * alphaCoeff X μ n * C ^ 2 := by
  have h1 : sigmaLE X 0 ≤ (inferInstance : MeasurableSpace Ω) := sigmaLE_le hmeas 0
  have h2 : sigmaGE X (n : ℤ) ≤ (inferInstance : MeasurableSpace Ω) := sigmaGE_le hmeas _
  have hf : Measurable[sigmaLE X 0] (X 0) :=
    (measurable_comap_self X 0).mono (comap_le_sigmaLE X le_rfl) le_rfl
  have hg : Measurable[sigmaGE X (n : ℤ)] (X (n : ℤ)) :=
    (measurable_comap_self X _).mono (comap_le_sigmaGE X le_rfl) le_rfl
  have key := abs_covariance_le_of_bounded h1 h2 hf hg (hbdd 0) (hbdd (n : ℤ))
  rw [acvf, covariance_comm]
  calc |cov[X 0, X (n : ℤ); μ]|
      ≤ 4 * alphaMixCoeff μ (sigmaLE X 0) (sigmaGE X (n : ℤ)) * C * C := key
    _ = 4 * alphaCoeff X μ n * C ^ 2 := by rw [alphaCoeff]; ring

/-- The ACVF of a (weakly) stationary process is even. -/
private lemma acvf_neg (hws : IsStationary X μ) (k : ℤ) : acvf X μ (-k) = acvf X μ k := by
  have h1 := hws.cov_shift k (-k)
  rw [add_neg_cancel] at h1
  rw [acvf, acvf, ← h1, covariance_comm]

/-- Absolute summability of the ACVF (first half of FY Thm 2.20(ii)). -/
private lemma summable_abs_acvf' [IsProbabilityMeasure μ] (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ) (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n) :
    Summable fun k : ℤ => |acvf X μ k| := by
  have hws : IsStationary X μ := hstat.isStationary hmeas (memLp_of_bdd hmeas hbdd 0 2)
  have hpos : Summable fun n : ℕ => |acvf X μ (n : ℤ)| := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      ((((summable_nat_add_iff 1).mpr hα).mul_left 4).mul_right (C ^ 2))
    exact_mod_cast abs_acvf_le_alphaCoeff hmeas hbdd (n + 1)
  refine Summable.of_nat_of_neg hpos ?_
  simpa only [acvf_neg hws] using hpos

/-- The lag-`(s − t)` covariance of the shifted coordinates. -/
private lemma cov_shift_pair (hws : IsStationary X μ) (s t : ℕ) :
    cov[X ((s : ℤ) + 1), X ((t : ℤ) + 1); μ] = acvf X μ ((s : ℤ) - (t : ℤ)) := by
  have h := hws.cov_shift ((t : ℤ) + 1) ((s : ℤ) - (t : ℤ))
  have e : ((t : ℤ) + 1) + ((s : ℤ) - (t : ℤ)) = (s : ℤ) + 1 := by ring
  rw [e] at h
  exact h

/-- The double sum of the ACVF over an arbitrary index set is at most `Λ · |D|`: for each
fixed `s` the map `t ↦ s − t` is injective, so the inner sum is dominated by the full
`ℤ`-series `Λ = Σ_k |γ(k)|`. -/
private lemma sum_sum_acvf_le (hsum : Summable fun k : ℤ => |acvf X μ k|) (D : Finset ℕ) :
    ∑ s ∈ D, ∑ t ∈ D, acvf X μ ((s : ℤ) - (t : ℤ))
      ≤ (∑' k : ℤ, |acvf X μ k|) * (D.card : ℝ) := by
  calc ∑ s ∈ D, ∑ t ∈ D, acvf X μ ((s : ℤ) - (t : ℤ))
      ≤ ∑ s ∈ D, ∑ t ∈ D, |acvf X μ ((s : ℤ) - (t : ℤ))| := by
        gcongr with s _ t _
        exact le_abs_self _
    _ ≤ ∑ _s ∈ D, ∑' k : ℤ, |acvf X μ k| := by
        refine Finset.sum_le_sum fun s _ => ?_
        have hinj : ∀ x ∈ D, ∀ y ∈ D, (s : ℤ) - (x : ℤ) = (s : ℤ) - (y : ℤ) → x = y := by
          intro x _ y _ h; omega
        have himg : ∑ k ∈ D.image (fun t : ℕ => (s : ℤ) - (t : ℤ)), |acvf X μ k|
            = ∑ t ∈ D, |acvf X μ ((s : ℤ) - (t : ℤ))| := Finset.sum_image hinj
        rw [← himg]
        exact hsum.sum_le_tsum _ (fun i _ => abs_nonneg _)
    _ = (∑' k : ℤ, |acvf X μ k|) * (D.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The partial sum over an arbitrary index set has mean zero. -/
private lemma integral_partialSum_eq_zero [IsProbabilityMeasure μ]
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (hmean : ∫ ω, X 0 ω ∂μ = 0) (D : Finset ℕ) :
    ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ∂μ = 0 := by
  have hsplit : ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ∂μ
      = ∑ t ∈ D, ∫ ω, X ((t : ℤ) + 1) ω ∂μ :=
    integral_finset_sum (f := fun (t : ℕ) ω => X ((t : ℤ) + 1) ω) D
      (fun t _ => (memLp_of_bdd hmeas hbdd ((t : ℤ) + 1) 1).integrable le_rfl)
  rw [hsplit]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [(hstat.identDistrib hmeas ((t : ℤ) + 1) 0).integral_eq, hmean]

/-- **The `Λ·|D|` second-moment bound.** For a bounded, zero-mean, strictly stationary
process with summable ACVF, the partial sum over an arbitrary finite index set `D` has
`E S_D² ≤ Λ |D|`, `Λ = Σ_{k ∈ ℤ} |γ(k)|`. This is the workhorse of both the variance rate
and the negligibility of the Bernstein small blocks. -/
private lemma integral_sq_partialSum_le [IsProbabilityMeasure μ]
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hsum : Summable fun k : ℤ => |acvf X μ k|) (D : Finset ℕ) :
    ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ ≤ (∑' k : ℤ, |acvf X μ k|) * (D.card : ℝ) := by
  have hws : IsStationary X μ := hstat.isStationary hmeas (memLp_of_bdd hmeas hbdd 0 2)
  have hmemD : ∀ t ∈ D, MemLp (X ((t : ℤ) + 1)) 2 μ := fun t _ =>
    memLp_of_bdd hmeas hbdd _ 2
  have hfun : (fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω) = ∑ t ∈ D, X ((t : ℤ) + 1) := by
    funext ω; simp [Finset.sum_apply]
  have hmemS : MemLp (fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω) 2 μ := by
    rw [hfun]; exact memLp_finset_sum' (μ := μ) D hmemD
  have hvar : variance (fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω) μ
      = ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ := by
    rw [variance_of_integral_eq_zero hmemS.aestronglyMeasurable.aemeasurable
      (integral_partialSum_eq_zero hmeas hstat hbdd hmean D)]
  rw [← hvar, variance_fun_sum' hmemD]
  calc ∑ s ∈ D, ∑ t ∈ D, cov[X ((s : ℤ) + 1), X ((t : ℤ) + 1); μ]
      = ∑ s ∈ D, ∑ t ∈ D, acvf X μ ((s : ℤ) - (t : ℤ)) := by
        exact Finset.sum_congr rfl fun s _ =>
          Finset.sum_congr rfl fun t _ => cov_shift_pair hws s t
    _ ≤ (∑' k : ℤ, |acvf X μ k|) * (D.card : ℝ) := sum_sum_acvf_le hsum D

end Toolbox

/-! ### The triangular-weight expansion of `∑_{s,t<n} f(s−t)` -/

section Triangular

/-- `{s − n : s < n} = [−n, 0)`. -/
private lemma sum_range_sub_last (f : ℤ → ℝ) (n : ℕ) :
    ∑ s ∈ Finset.range n, f ((s : ℤ) - (n : ℤ)) = ∑ k ∈ Finset.Ico (-(n : ℤ)) 0, f k := by
  have hinj : Function.Injective fun s : ℕ => (s : ℤ) - (n : ℤ) := by
    intro a b h; dsimp only at h; omega
  have hmap : (Finset.range n).map ⟨fun s : ℕ => (s : ℤ) - (n : ℤ), hinj⟩
      = Finset.Ico (-(n : ℤ)) 0 := by
    ext k
    simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩; omega
    · intro hk; exact ⟨(k + n).toNat, by omega, by omega⟩
  rw [← hmap, Finset.sum_map]
  rfl

/-- `{n − t : t ≤ n} = [0, n]`. -/
private lemma sum_range_last_sub (f : ℤ → ℝ) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), f ((n : ℤ) - (t : ℤ)) = ∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), f k := by
  have hinj : Function.Injective fun t : ℕ => (n : ℤ) - (t : ℤ) := by
    intro a b h; dsimp only at h; omega
  have hmap : (Finset.range (n + 1)).map ⟨fun t : ℕ => (n : ℤ) - (t : ℤ), hinj⟩
      = Finset.Icc (0 : ℤ) (n : ℤ) := by
    ext k
    simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ha, rfl⟩; omega
    · intro hk; exact ⟨((n : ℤ) - k).toNat, by omega, by omega⟩
  rw [← hmap, Finset.sum_map]
  rfl

/-- **Triangular-weight identity**: `∑_{s,t<n} f(s−t) = ∑_{|k|<n} (n − |k|) f(k)`. -/
private lemma sum_sub_double_eq (f : ℤ → ℝ) : ∀ n : ℕ,
    ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, f ((s : ℤ) - (t : ℤ))
      = ∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * f k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hIoo : Finset.Ioo (-((n : ℤ) + 1)) ((n : ℤ) + 1) = Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      ext k; simp only [Finset.mem_Ioo, Finset.mem_Icc]; omega
    have hsplit : Finset.Icc (-(n : ℤ)) (n : ℤ)
        = Finset.Ico (-(n : ℤ)) 0 ∪ Finset.Icc (0 : ℤ) (n : ℤ) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.Ico (-(n : ℤ)) 0) (Finset.Icc (0 : ℤ) (n : ℤ)) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [Finset.mem_Ico] at hk
      simp only [Finset.mem_Icc] at hk'
      omega
    -- left-hand side: peel the last row and the last column
    have hL : ∑ s ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1), f ((s : ℤ) - (t : ℤ))
        = (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, f ((s : ℤ) - (t : ℤ)))
          + ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f k := by
      rw [Finset.sum_range_succ]
      have hrow : ∀ s ∈ Finset.range n, ∑ t ∈ Finset.range (n + 1), f ((s : ℤ) - (t : ℤ))
          = (∑ t ∈ Finset.range n, f ((s : ℤ) - (t : ℤ))) + f ((s : ℤ) - (n : ℤ)) := by
        intro s _
        rw [Finset.sum_range_succ]
      rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, sum_range_sub_last,
        sum_range_last_sub, hsplit, Finset.sum_union hdisj]
      ring
    -- right-hand side: the two extreme lags carry weight `1`
    have hR : ∑ k ∈ Finset.Ioo (-((n : ℤ) + 1)) ((n : ℤ) + 1), (((n : ℝ) + 1) - |(k : ℝ)|) * f k
        = (∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * f k)
          + ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f k := by
      rw [hIoo]
      have hshrink : ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * f k
          = ∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * f k := by
        refine (Finset.sum_subset ?_ ?_).symm
        · intro k hk
          simp only [Finset.mem_Ioo] at hk
          simp only [Finset.mem_Icc]
          omega
        · intro k hk hk'
          simp only [Finset.mem_Icc] at hk
          simp only [Finset.mem_Ioo, not_and_or, not_lt] at hk'
          have : |(k : ℝ)| = (n : ℝ) := by
            rcases hk' with h | h
            · have : k = -(n : ℤ) := by omega
              subst this; push_cast; simp
            · have : k = (n : ℤ) := by omega
              subst this; push_cast; simp
          rw [this]; ring
      rw [← hshrink, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hL, ih]
    push_cast
    push_cast at hR
    rw [hR]

end Triangular

/-- **FY Theorem 2.20(ii)** (in-text; erratum `4α(j)C²` applied): bounded zero-mean
strictly stationary + summable α ⇒ summable ACVF and the variance-rate identity
(2.63). -/
theorem summable_acvf_and_var_rate_of_bounded [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {C : ℝ}
    -- USER-INPUT: uniform bound; FY Thm 2.20(ii)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    -- USER-INPUT: zero mean; FY §2.6.3 setup
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    -- USER-INPUT: summable mixing coefficients; FY Thm 2.20(ii)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n) :
    (Summable fun k : ℤ => |acvf X μ k|) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
          variance (fun ω => ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ) atTop
        (𝓝 (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))) := by
  classical
  have hws : IsStationary X μ := hstat.isStationary hmeas (memLp_of_bdd hmeas hbdd 0 2)
  have hsum : Summable fun k : ℤ => |acvf X μ k| := summable_abs_acvf' hmeas hstat hbdd hα
  refine ⟨hsum, ?_⟩
  have hsumZ : Summable fun k : ℤ => acvf X μ k := hsum.of_abs
  have hsumN : Summable fun n : ℕ => acvf X μ (n : ℤ) := hsumZ.comp_injective Nat.cast_injective
  have hsumN1 : Summable fun n : ℕ => acvf X μ ((n : ℤ) + 1) := by
    have h := (summable_nat_add_iff 1).mpr hsumN
    refine h.congr fun n => ?_
    have e : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e]
  -- (a) the `ℤ`-series of the ACVF is the book's `σ² = γ(0) + 2 Σ_{j≥1} γ(j)`
  have hσeq : (∑' k : ℤ, acvf X μ k)
      = acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) := by
    have hneg : Summable fun n : ℕ => acvf X μ (-((n : ℤ) + 1)) := by
      simpa only [acvf_neg hws] using hsumN1
    have hnegeq : (∑' n : ℕ, acvf X μ (-((n : ℤ) + 1))) = ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) :=
      tsum_congr fun n => acvf_neg hws _
    have hshift : (∑' n : ℕ, acvf X μ ((n + 1 : ℕ) : ℤ))
        = ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) :=
      tsum_congr fun n => by
        rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring]
    have hpos : (∑' n : ℕ, acvf X μ (n : ℤ))
        = acvf X μ 0 + ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) := by
      rw [hsumN.tsum_eq_zero_add, hshift]
      norm_num
    rw [tsum_of_nat_of_neg_add_one hsumN hneg, hnegeq, hpos]
    ring
  -- (b) the exact triangular-weight expansion of `Var S_n`
  have hvar : ∀ n : ℕ, variance (fun ω => ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ
      = ∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * acvf X μ k := by
    intro n
    have h1 : ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n,
          cov[X ((s : ℤ) + 1), X ((t : ℤ) + 1); μ]
        = ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, acvf X μ ((s : ℤ) - (t : ℤ)) :=
      Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => cov_shift_pair hws s t
    have h0 := variance_fun_sum' (μ := μ) (X := fun t : ℕ => X ((t : ℤ) + 1))
      (s := Finset.range n) (fun t _ => memLp_of_bdd hmeas hbdd ((t : ℤ) + 1) 2)
    rw [h0, h1, sum_sub_double_eq]
  -- (c) the Fejér-weighted family, extended by zero to all of `ℤ`
  set g : ℕ → ℤ → ℝ := fun n k =>
    if k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ) then (1 - |(k : ℝ)| / (n : ℝ)) * acvf X μ k else 0
    with hgdef
  have hns : ∀ n : ℕ, (n : ℝ)⁻¹ * variance (fun ω => ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ
      = ∑' k : ℤ, g n k := by
    intro n
    have hz : ∑' k : ℤ, g n k = ∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), g n k :=
      tsum_eq_sum fun k hk => by simp only [hgdef, if_neg hk]
    rw [hvar n, hz]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [hgdef, if_pos hk]
      field_simp
  -- (d) Tannery / dominated convergence for series: the Fejér weights tend to `1`
  have hdom : Tendsto (fun n : ℕ => ∑' k : ℤ, g n k) atTop (𝓝 (∑' k : ℤ, acvf X μ k)) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun k => ?_) (Eventually.of_forall ?_)
    · have hk : ∀ᶠ n : ℕ in atTop, g n k = (1 - |(k : ℝ)| / (n : ℝ)) * acvf X μ k := by
        filter_upwards [eventually_ge_atTop (k.natAbs + 1)] with n hn
        have hmem : k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ) := by
          simp only [Finset.mem_Ioo]
          have : (k.natAbs : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
          omega
        simp only [hgdef, if_pos hmem]
      refine Tendsto.congr' (hk.mono fun n h => h.symm) ?_
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - |(k : ℝ)| / (n : ℝ)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat |(k : ℝ)|)
      simpa using h1.mul_const (acvf X μ k)
    · intro n k
      by_cases hk : k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ)
      · simp only [hgdef, if_pos hk, Real.norm_eq_abs, abs_mul]
        refine mul_le_of_le_one_left (abs_nonneg _) ?_
        simp only [Finset.mem_Ioo] at hk
        have hklt : |(k : ℝ)| < (n : ℝ) := by
          rw [abs_lt]
          exact ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩
        have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (abs_nonneg _) hklt
        have hd0 : 0 ≤ |(k : ℝ)| / (n : ℝ) := div_nonneg (abs_nonneg _) hnpos.le
        have hd1 : |(k : ℝ)| / (n : ℝ) < 1 := (div_lt_one hnpos).mpr hklt
        rw [abs_le]
        constructor <;> linarith
      · simp only [hgdef, if_neg hk, norm_zero]
        exact abs_nonneg _
  rw [← hσeq]
  exact (Tendsto.congr (fun n => (hns n).symm) hdom)

/-! ### Analytic bricks for the Bernstein-block CLT -/

section Bernstein

/-- Third-order Taylor control of `e^{ix}` in the two forms the block expansion consumes:
a **global cubic** bound (for the bulk, where the phase is small) and a **global
quadratic** bound (for the Lindeberg tail, where the phase is not small). Both follow from
`Complex.exp_bound` at `n = 3` on `|x| ≤ 1` and from the triangle inequality
(`‖e^{ix}‖ = 1`) on `|x| > 1`. -/
private lemma norm_expI_taylor (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖
        ≤ 4 * |x| ^ 3 ∧
      ‖Complex.exp ((x : ℂ) * Complex.I) - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖
        ≤ 4 * x ^ 2 := by
  have hzn : ‖(x : ℂ) * Complex.I‖ = |x| := by
    simp
  have hI2 : ((x : ℂ) * Complex.I) ^ 2 = -(x : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]; ring
  have hsum : ∑ m ∈ Finset.range 3, ((x : ℂ) * Complex.I) ^ m / (Nat.factorial m : ℂ)
      = 1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, hI2]
    push_cast
    ring
  have habs : 0 ≤ |x| := abs_nonneg x
  have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
  by_cases hx : |x| ≤ 1
  · have hb := Complex.exp_bound (x := (x : ℂ) * Complex.I) (by rw [hzn]; exact hx)
      (n := 3) (by norm_num)
    rw [hsum, hzn] at hb
    have hb' : ‖Complex.exp ((x : ℂ) * Complex.I)
        - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤ |x| ^ 3 := by
      refine hb.trans ?_
      have : ((3 : ℕ).succ : ℝ) * (((Nat.factorial 3 : ℝ)) * (3 : ℝ))⁻¹ ≤ 1 := by
        norm_num [Nat.factorial]
      nlinarith [pow_nonneg habs 3]
    refine ⟨hb'.trans (by nlinarith [pow_nonneg habs 3]), hb'.trans ?_⟩
    have : |x| ^ 3 = |x| * x ^ 2 := by rw [← hsq]; ring
    nlinarith [sq_nonneg x]
  · rw [not_le] at hx
    have hE : ‖Complex.exp ((x : ℂ) * Complex.I)
        - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤ 1 + (1 + |x| + x ^ 2 / 2) := by
      refine (norm_sub_le _ _).trans ?_
      gcongr
      · exact le_of_eq (Complex.norm_exp_ofReal_mul_I x)
      · refine (norm_sub_le _ _).trans ?_
        gcongr
        · refine (norm_add_le _ _).trans ?_
          rw [hzn, norm_one]
        · rw [norm_div, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_ofNat, abs_of_nonneg (sq_nonneg x)]
    have h1 : (1 : ℝ) ≤ x ^ 2 := by nlinarith
    have h2 : |x| ≤ x ^ 2 := by nlinarith
    have hq : ‖Complex.exp ((x : ℂ) * Complex.I)
        - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤ 4 * x ^ 2 := by
      refine hE.trans ?_; linarith
    refine ⟨hq.trans ?_, hq⟩
    have : x ^ 2 ≤ |x| ^ 3 := by
      rw [← hsq]; nlinarith [pow_nonneg habs 2]
    linarith

/-- Telescoping bound for powers of unit-modulus complex numbers. -/
private lemma norm_pow_sub_pow_le_of_norm_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ∀ k : ℕ, ‖a ^ k - b ^ k‖ ≤ (k : ℝ) * ‖a - b‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + (a - b) * b ^ k := by ring
    rw [hstep]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖a‖ * ‖a ^ k - b ^ k‖ ≤ 1 * ((k : ℝ) * ‖a - b‖) :=
      mul_le_mul ha ih (norm_nonneg _) zero_le_one
    have h2 : ‖a - b‖ * ‖b‖ ^ k ≤ ‖a - b‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _)
    push_cast
    linarith

/-- **`m · α(m) → 0`** for a monotone summable mixing sequence: the tail block
`Σ_{m/2 ≤ j < m} α(j)` dominates `(m/2)·α(m)` and vanishes by the Cauchy criterion. -/
private lemma tendsto_mul_alphaCoeff [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hα : Summable fun n : ℕ => alphaCoeff X μ n) :
    Tendsto (fun m : ℕ => (m : ℝ) * alphaCoeff X μ m) atTop (𝓝 0) := by
  have hanti : Antitone fun n : ℕ => alphaCoeff X μ n := alphaCoeff_antitone X
  have hnn : ∀ n : ℕ, 0 ≤ alphaCoeff X μ n := fun _ => alphaMixCoeff_nonneg
  have hT : Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m, alphaCoeff X μ j) atTop
      (𝓝 (∑' j : ℕ, alphaCoeff X μ j)) := hα.hasSum.tendsto_sum_nat
  have hhalf : Tendsto (fun m : ℕ => m / 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 * b + 1, fun a ha => by omega⟩
  have hdiff : Tendsto (fun m : ℕ => (∑ j ∈ Finset.range m, alphaCoeff X μ j)
      - ∑ j ∈ Finset.range (m / 2), alphaCoeff X μ j) atTop (𝓝 0) := by
    simpa using hT.sub (hT.comp hhalf)
  refine squeeze_zero (fun m => mul_nonneg (Nat.cast_nonneg _) (hnn m)) (fun m => ?_)
    (by simpa using hdiff.const_mul 2)
  have hle : m / 2 ≤ m := Nat.div_le_self _ _
  have hIco : ∑ j ∈ Finset.Ico (m / 2) m, alphaCoeff X μ j
      = (∑ j ∈ Finset.range m, alphaCoeff X μ j)
        - ∑ j ∈ Finset.range (m / 2), alphaCoeff X μ j := by
    rw [Finset.sum_Ico_eq_sub _ hle]
  have hcard : ((Finset.Ico (m / 2) m).card : ℝ) * alphaCoeff X μ m
      ≤ ∑ j ∈ Finset.Ico (m / 2) m, alphaCoeff X μ j := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun j hj => ?_
    exact hanti (le_of_lt (Finset.mem_Ico.mp hj).2)
  rw [← hIco]
  have hc : ((Finset.Ico (m / 2) m).card : ℝ) = ((m - m / 2 : ℕ) : ℝ) := by
    rw [Nat.card_Ico]
  have hge : (m : ℝ) ≤ 2 * ((m - m / 2 : ℕ) : ℝ) := by
    have : m ≤ 2 * (m - m / 2) := by omega
    exact_mod_cast this
  nlinarith [hnn m, hcard, hc ▸ hcard]

/-! #### The block scheme -/

private lemma tendsto_natSqrt : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b * b, fun a ha => by
    calc b = Nat.sqrt (b * b) := (Nat.sqrt_eq b).symm
      _ ≤ Nat.sqrt a := Nat.sqrt_le_sqrt ha⟩

private lemma tendsto_natSqrt_div : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ) / (n : ℝ))
    atTop (𝓝 0) := by
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (Nat.sqrt n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp tendsto_natSqrt
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hone
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hs : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr hn
  have hsq : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le n
  have hs0 : (0 : ℝ) < (Nat.sqrt n : ℝ) := by exact_mod_cast hs
  rw [div_le_div_iff₀ (by positivity) hs0]
  nlinarith

/-- **The Bernstein block scheme.** Small blocks `s_n ≈ n^{1/4}`, big blocks
`l_n = ⌊n/s_n⌋ + 1 ≈ n^{3/4}`, block count `k_n = ⌊n/(l_n + s_n)⌋ ≈ n^{1/4}`. The choice
`l_n s_n > n` forces `k_n ≤ s_n`, which is exactly what turns `m α(m) → 0` into the
Volkonskii–Rozanov budget `k_n α(s_n) → 0`. -/
private lemma exists_block_scheme [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hα : Summable fun n : ℕ => alphaCoeff X μ n) :
    ∃ l s k : ℕ → ℕ,
      (∀ n, 1 ≤ s n) ∧ (∀ n, 1 ≤ l n) ∧ (∀ n, k n * (l n + s n) ≤ n) ∧
      Tendsto (fun n : ℕ => (l n : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ((k n * l n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => (k n : ℝ) * alphaCoeff X μ (s n)) atTop (𝓝 0) := by
  classical
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → ℕ, ∀ n, s n = Nat.sqrt (Nat.sqrt n) + 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨l, hldef⟩ : ∃ l : ℕ → ℕ, ∀ n, l n = n / s n + 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ → ℕ, ∀ n, k n = n / (l n + s n) := ⟨_, fun _ => rfl⟩
  have hs1 : ∀ n, 1 ≤ s n := fun n => by rw [hsdef]; omega
  have hl1 : ∀ n, 1 ≤ l n := fun n => by rw [hldef]; exact Nat.le_add_left 1 _
  have hfit : ∀ n, k n * (l n + s n) ≤ n := fun n => by rw [hkdef]; exact Nat.div_mul_le_self _ _
  -- `s_n l_n > n`: the big blocks overshoot, which is what caps the block count
  have hsl : ∀ n, n < s n * l n := by
    intro n
    have h1 := Nat.div_add_mod n (s n)
    have h2 : n % s n < s n := Nat.mod_lt _ (hs1 n)
    have h3 : s n * l n = s n * (n / s n) + s n := by rw [hldef]; ring
    omega
  have hks : ∀ n, k n ≤ s n := by
    intro n
    by_contra hcon
    rw [not_le] at hcon
    have h1 : k n * l n ≤ n :=
      le_trans (Nat.mul_le_mul_left (k n) (Nat.le_add_right (l n) (s n))) (hfit n)
    have h2 : (s n + 1) * l n ≤ k n * l n := Nat.mul_le_mul_right _ hcon
    have h3 : (s n + 1) * l n = s n * l n + l n := by ring
    have h4 := hsl n
    have h5 := hl1 n
    omega
  -- the small blocks grow
  have hstopN : Tendsto s atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [Function.comp_apply, hsdef]; omega)
      (tendsto_natSqrt.comp tendsto_natSqrt)
  have hinvs : Tendsto (fun n : ℕ => (1 : ℝ) / (s n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hstopN
  have hinvn : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  -- `s_n² / n → 0`
  have hs2 : ∀ n, s n ^ 2 ≤ 3 * Nat.sqrt n + 1 := by
    intro n
    have hq : Nat.sqrt (Nat.sqrt n) * Nat.sqrt (Nat.sqrt n) ≤ Nat.sqrt n :=
      Nat.sqrt_le (Nat.sqrt n)
    have hq' : Nat.sqrt (Nat.sqrt n) ≤ Nat.sqrt n := Nat.sqrt_le_self _
    have : s n ^ 2 = Nat.sqrt (Nat.sqrt n) * Nat.sqrt (Nat.sqrt n)
        + 2 * Nat.sqrt (Nat.sqrt n) + 1 := by rw [hsdef]; ring
    omega
  have hsqn : Tendsto (fun n : ℕ => (s n : ℝ) ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 3 * ((Nat.sqrt n : ℝ) / (n : ℝ)) + 1 / (n : ℝ))
        atTop (𝓝 0) := by
      simpa using (tendsto_natSqrt_div.const_mul 3).add hinvn
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hb : (s n : ℝ) ^ 2 ≤ 3 * (Nat.sqrt n : ℝ) + 1 := by exact_mod_cast hs2 n
    have hrw : 3 * ((Nat.sqrt n : ℝ) / (n : ℝ)) + 1 / (n : ℝ)
        = (3 * (Nat.sqrt n : ℝ) + 1) / (n : ℝ) := by ring
    rw [hrw, div_le_div_iff_of_pos_right hn0]
    exact hb
  -- `l_n / n → 0`
  have hln0 : Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
      (by simpa only [add_zero] using hinvs.add hinvn)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hs0 : (0 : ℝ) < (s n : ℝ) := by exact_mod_cast hs1 n
    have hdiv : ((n / s n : ℕ) : ℝ) ≤ (n : ℝ) / (s n : ℝ) := Nat.cast_div_le
    have hlc : (l n : ℝ) ≤ (n : ℝ) / (s n : ℝ) + 1 := by
      rw [hldef]; push_cast; linarith
    calc (l n : ℝ) / (n : ℝ) ≤ ((n : ℝ) / (s n : ℝ) + 1) / (n : ℝ) := by gcongr
      _ = 1 / (s n : ℝ) + 1 / (n : ℝ) := by field_simp
  -- `l_n → ∞`
  have hltop : Tendsto (fun n : ℕ => (l n : ℝ)) atTop atTop := by
    have hhalf : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ) / 2) atTop atTop :=
      Tendsto.atTop_div_const (by norm_num)
        (tendsto_natCast_atTop_atTop.comp tendsto_natSqrt)
    refine tendsto_atTop_mono' _ ?_ hhalf
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hr1 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr hn
    have hsr : s n ≤ 2 * Nat.sqrt n := by
      have := Nat.sqrt_le_self (Nat.sqrt n)
      rw [hsdef]; omega
    have hrr : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le n
    have hs0 : (0 : ℝ) < (s n : ℝ) := by exact_mod_cast hs1 n
    have hnl : (n : ℝ) < (s n : ℝ) * (l n : ℝ) := by exact_mod_cast hsl n
    have hsr' : (s n : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) := by exact_mod_cast hsr
    have hr0 : (0 : ℝ) < (Nat.sqrt n : ℝ) := by exact_mod_cast hr1
    nlinarith [hnl, hrr, hsr', hr0]
  -- `k_n l_n / n → 1`
  have hkl : Tendsto (fun n : ℕ => ((k n * l n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    have hsn0 : Tendsto (fun n : ℕ => (s n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hsqn
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hs1' : (1 : ℝ) ≤ (s n : ℝ) := by exact_mod_cast hs1 n
      gcongr
      nlinarith
    have hlow : Tendsto (fun n : ℕ => 1 - (s n : ℝ) ^ 2 / (n : ℝ) - (l n : ℝ) / (n : ℝ)
        - (s n : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds.sub hsqn).sub hln0).sub hsn0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hkq : (l n + s n) * k n + n % (l n + s n) = n := by
        rw [hkdef]; exact Nat.div_add_mod n (l n + s n)
      have hmlt : n % (l n + s n) < l n + s n := Nat.mod_lt _ (by have := hl1 n; omega)
      have hexp : (l n + s n) * k n = k n * l n + k n * s n := by ring
      have hks' : k n * s n ≤ s n * s n := Nat.mul_le_mul_right _ (hks n)
      have hnat : n ≤ k n * l n + s n * s n + l n + s n := by omega
      have hcast : (n : ℝ) ≤ ((k n * l n : ℕ) : ℝ) + (s n : ℝ) ^ 2 + (l n : ℝ) + (s n : ℝ) := by
        have h2 : ((n : ℕ) : ℝ) ≤ ((k n * l n + s n * s n + l n + s n : ℕ) : ℝ) := by
          exact_mod_cast hnat
        push_cast at h2 ⊢
        nlinarith [h2]
      have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
      calc 1 - (s n : ℝ) ^ 2 / (n : ℝ) - (l n : ℝ) / (n : ℝ) - (s n : ℝ) / (n : ℝ)
          = ((n : ℝ) - (s n : ℝ) ^ 2 - (l n : ℝ) - (s n : ℝ)) / (n : ℝ) := by field_simp
        _ ≤ ((k n * l n : ℕ) : ℝ) / (n : ℝ) := by gcongr; linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h1 : k n * l n ≤ n :=
        le_trans (Nat.mul_le_mul_left (k n) (Nat.le_add_right (l n) (s n))) (hfit n)
      rw [div_le_one hn0]
      exact_mod_cast h1
  -- `k_n α(s_n) → 0`
  have hkα : Tendsto (fun n : ℕ => (k n : ℝ) * alphaCoeff X μ (s n)) atTop (𝓝 0) := by
    have hnn : ∀ m : ℕ, 0 ≤ alphaCoeff X μ m := fun _ => alphaMixCoeff_nonneg
    refine squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg _) (hnn _)) (fun n => ?_)
      ((tendsto_mul_alphaCoeff hα).comp hstopN)
    have : (k n : ℝ) ≤ (s n : ℝ) := by exact_mod_cast hks n
    exact mul_le_mul_of_nonneg_right this (hnn _)
  exact ⟨l, s, k, hs1, hl1, hfit, hltop, hln0, hkl, hkα⟩

/-! #### Window laws, phase increments, and the Lindeberg input -/

/-- `‖e^{ix} − 1‖ ≤ |x| + 5x²` — the crude phase-increment bound, read off the
third-order Taylor brick (no trigonometric identities needed). -/
private lemma norm_expI_sub_one_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x| + 5 * x ^ 2 := by
  have hT := (norm_expI_taylor x).2
  have hx : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
  have hx2 : ‖(x : ℂ) ^ 2 / 2‖ = x ^ 2 / 2 := by
    rw [norm_div, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat, abs_of_nonneg (sq_nonneg x)]
  have hsplit : Complex.exp ((x : ℂ) * Complex.I) - 1
      = (Complex.exp ((x : ℂ) * Complex.I) - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2))
        + ((x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h2 : ‖(x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2‖ ≤ |x| + x ^ 2 / 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [hx, hx2]
  nlinarith [hT, h2, sq_nonneg x]

/-- **Product-to-exponential comparison.** If `a_n = 1 + z_n` has modulus at most one,
`Re z_n ≤ 0`, `z_n → 0`, `k_n z_n → w` and `k_n ‖z_n‖² → 0`, then `a_n^{k_n} → e^w`. This
is the scalar limit that replaces the independent-copy array in the Bernstein scheme:
stationarity makes all big blocks identically distributed, so the factorized
characteristic function is a single power. -/
private lemma tendsto_pow_of_tendsto_mul {k : ℕ → ℕ} {z : ℕ → ℂ} {w : ℂ}
    (hz1 : ∀ n, ‖1 + z n‖ ≤ 1) (hzre : ∀ n, (z n).re ≤ 0)
    (hz0 : Tendsto z atTop (𝓝 0))
    (hkz : Tendsto (fun n => (k n : ℂ) * z n) atTop (𝓝 w))
    (hkb : Tendsto (fun n => (k n : ℝ) * ‖z n‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => (1 + z n) ^ k n) atTop (𝓝 (Complex.exp w)) := by
  have hexpre : ∀ n, ‖Complex.exp (z n)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr (hzre n)
  have hgap : Tendsto (fun n => (1 + z n) ^ k n - Complex.exp ((k n : ℂ) * z n))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hkb
    have hz0' : ∀ᶠ n in atTop, ‖z n‖ ≤ 1 := by
      have := hz0.norm
      simp only [norm_zero] at this
      filter_upwards [this.eventually_le_const (by norm_num : (0:ℝ) < 1)] with n hn using hn
    filter_upwards [hz0'] with n hn
    have hpow : Complex.exp ((k n : ℂ) * z n) = Complex.exp (z n) ^ k n := by
      rw [Complex.exp_nat_mul]
    rw [hpow]
    refine (norm_pow_sub_pow_le_of_norm_le_one (hz1 n) (hexpre n) (k n)).trans ?_
    have hstep : ‖(1 + z n) - Complex.exp (z n)‖ ≤ ‖z n‖ ^ 2 := by
      have h := Complex.norm_exp_sub_one_sub_id_le (x := z n) hn
      rw [← norm_neg]
      have he : -((1 + z n) - Complex.exp (z n)) = Complex.exp (z n) - 1 - z n := by ring
      rw [he]
      exact h
    exact mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
  have hexp : Tendsto (fun n => Complex.exp ((k n : ℂ) * z n)) atTop (𝓝 (Complex.exp w)) :=
    (Complex.continuous_exp.tendsto w).comp hkz
  have := hgap.add hexp
  simpa using this

/-- Strict stationarity transports the law of a length-`m` window: any measurable
functional of a shifted block sum has the anchored expectation. -/
private lemma integral_comp_window_eq [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    {F : ℝ → ℂ} (hF : Measurable F) (m : ℕ) (c : ℤ) :
    ∫ ω, F (∑ t ∈ Finset.range m, X ((t : ℤ) + 1 + c) ω) ∂μ
      = ∫ ω, F (∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω) ∂μ := by
  have hG : Measurable fun q : Fin m → ℝ => F (∑ i, q i) :=
    hF.comp (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  have hm1 : Measurable fun ω (i : Fin m) => X (((i : ℕ) : ℤ) + 1 + c) ω :=
    measurable_pi_lambda _ fun _ => hmeas _
  have hm2 : Measurable fun ω (i : Fin m) => X (((i : ℕ) : ℤ) + 1) ω :=
    measurable_pi_lambda _ fun _ => hmeas _
  have key := hstat m (fun i : Fin m => ((i : ℕ) : ℤ) + 1) c
  have e1 := integral_map (μ := μ) (φ := fun ω (i : Fin m) => X (((i : ℕ) : ℤ) + 1 + c) ω)
    (f := fun q : Fin m → ℝ => F (∑ i, q i)) hm1.aemeasurable hG.aestronglyMeasurable
  have e2 := integral_map (μ := μ) (φ := fun ω (i : Fin m) => X (((i : ℕ) : ℤ) + 1) ω)
    (f := fun q : Fin m → ℝ => F (∑ i, q i)) hm2.aemeasurable hG.aestronglyMeasurable
  rw [key] at e1
  have h := e1.symm.trans e2
  have conv1 : ∀ ω : Ω, ∑ t ∈ Finset.range m, X ((t : ℤ) + 1 + c) ω
      = ∑ i : Fin m, X (((i : ℕ) : ℤ) + 1 + c) ω :=
    fun ω => (Fin.sum_univ_eq_sum_range (fun j : ℕ => X ((j : ℤ) + 1 + c) ω) m).symm
  have conv2 : ∀ ω : Ω, ∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω
      = ∑ i : Fin m, X (((i : ℕ) : ℤ) + 1) ω :=
    fun ω => (Fin.sum_univ_eq_sum_range (fun j : ℕ => X ((j : ℤ) + 1) ω) m).symm
  simp only [conv1, conv2]
  exact h

/-- Cauchy–Schwarz on a probability space in the only form used: `(E|f|)² ≤ E f²`
(the variance of `|f|` is nonnegative). -/
private lemma sq_integral_abs_le [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, |f ω| ∂μ) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂μ := by
  have habs : MemLp (fun ω => |f ω|) 2 μ := by
    simpa [Real.norm_eq_abs] using hf.norm
  have h := variance_nonneg (fun ω => |f ω|) μ
  rw [variance_eq_sub habs] at h
  simp only [Pi.pow_apply, sq_abs] at h
  linarith

omit [MeasurableSpace Ω] in
private lemma sigmaLE_mono (X : ℤ → Ω → ℝ) {a b : ℤ} (h : a ≤ b) :
    sigmaLE X a ≤ sigmaLE X b :=
  iSup₂_le fun _ hs => comap_le_sigmaLE X (le_trans hs h)

omit [MeasurableSpace Ω] in
private lemma sigmaGE_mono (X : ℤ → Ω → ℝ) {a b : ℤ} (h : a ≤ b) :
    sigmaGE X b ≤ sigmaGE X a :=
  iSup₂_le fun _ hs => comap_le_sigmaGE X (le_trans h hs)

/-- **Volkonskii–Rozanov for the Bernstein big blocks.** The `j`-th big block occupies
the time window `[j(l+s)+1, j(l+s)+l]`, so its σ-algebra sits inside
`σ{X_t : t ≤ j(l+s)+l} ⊓ σ{X_t : t ≥ j(l+s)+1}`; consecutive cumulative pasts and blocks
are separated by the small block of length `s`, and the shift lemma identifies the gap
coefficient as `α(s+1) ≤ α(s)`. -/
private lemma norm_integral_prod_blocks_sub_prod_le [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    (l s k : ℕ) (v : ℝ) :
    ‖(∫ ω, ∏ j : Fin k, Complex.exp (((v * ∑ i ∈ Finset.range l,
            X ((i : ℤ) + 1 + ((j : ℕ) * (l + s) : ℕ)) ω : ℝ) : ℂ) * Complex.I) ∂μ)
        - ∏ j : Fin k, ∫ ω, Complex.exp (((v * ∑ i ∈ Finset.range l,
            X ((i : ℤ) + 1 + ((j : ℕ) * (l + s) : ℕ)) ω : ℝ) : ℂ) * Complex.I) ∂μ‖
      ≤ 16 * ((k : ℝ) - 1) * alphaCoeff X μ s := by
  classical
  set m : Fin k → MeasurableSpace Ω := fun j =>
    sigmaLE X (((j : ℕ) * (l + s) : ℕ) + l) ⊓ sigmaGE X (((j : ℕ) * (l + s) : ℕ) + 1) with hm
  have hle : ∀ j, m j ≤ (inferInstance : MeasurableSpace Ω) := fun j =>
    le_trans inf_le_left (sigmaLE_le hmeas _)
  -- each block variable is measurable for the block σ-algebra
  have hcomap : ∀ (j : Fin k) (i : ℕ), i < l →
      MeasurableSpace.comap (X ((i : ℤ) + 1 + (((j : ℕ) * (l + s) : ℕ) : ℤ))) inferInstance
        ≤ m j := by
    intro j i hi
    refine le_inf (comap_le_sigmaLE X ?_) (comap_le_sigmaGE X ?_)
    · have : (i : ℤ) + 1 ≤ (l : ℤ) := by exact_mod_cast hi
      push_cast
      omega
    · push_cast
      omega
  have hmeasξ : ∀ j : Fin k, Measurable[m j] fun ω =>
      Complex.exp (((v * ∑ i ∈ Finset.range l,
        X ((i : ℤ) + 1 + ((j : ℕ) * (l + s) : ℕ)) ω : ℝ) : ℂ) * Complex.I) := by
    intro j
    have hsum : Measurable[m j] fun ω => ∑ i ∈ Finset.range l,
        X ((i : ℤ) + 1 + (((j : ℕ) * (l + s) : ℕ) : ℤ)) ω :=
      Finset.measurable_sum _ fun i hi =>
        (measurable_comap_self X _).mono (hcomap j i (Finset.mem_range.mp hi)) le_rfl
    exact (Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp (measurable_const.mul hsum))).mul measurable_const))
  have hbddξ : ∀ j : Fin k, ∀ᵐ ω ∂μ, ‖Complex.exp (((v * ∑ i ∈ Finset.range l,
      X ((i : ℤ) + 1 + ((j : ℕ) * (l + s) : ℕ)) ω : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
    intro j
    filter_upwards with ω
    rw [Complex.norm_exp_ofReal_mul_I]
  refine norm_integral_prod_sub_prod_integral_le hle _ hmeasξ hbddξ ?_
  intro j hj
  -- cumulative past ≤ `σ{X_t : t ≤ j(l+s)+l}`, next block ≤ `σ{X_t : t ≥ j(l+s)+l+s+1}`
  have hpast : (⨆ j' : Fin k, ⨆ _ : (j' : ℕ) ≤ (j : ℕ), m j')
      ≤ sigmaLE X (((j : ℕ) * (l + s) : ℕ) + l) := by
    refine iSup₂_le fun j' hj' => le_trans inf_le_left (sigmaLE_mono X ?_)
    have : ((j' : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hj'
    have hmul : ((j' : ℕ) * (l + s) : ℕ) ≤ ((j : ℕ) * (l + s) : ℕ) :=
      Nat.mul_le_mul_right _ hj'
    have : (((j' : ℕ) * (l + s) : ℕ) : ℤ) ≤ (((j : ℕ) * (l + s) : ℕ) : ℤ) := by
      exact_mod_cast hmul
    omega
  have hfut : m ⟨(j : ℕ) + 1, hj⟩
      ≤ sigmaGE X ((((j : ℕ) * (l + s) : ℕ) + l : ℤ) + ((s : ℤ) + 1)) := by
    refine le_trans inf_le_right (sigmaGE_mono X ?_)
    have hmul : (((j : ℕ) + 1) * (l + s) : ℕ) = ((j : ℕ) * (l + s) : ℕ) + (l + s) := by ring
    push_cast [hmul]
    omega
  calc alphaMixCoeff μ (⨆ j' : Fin k, ⨆ _ : (j' : ℕ) ≤ (j : ℕ), m j') (m ⟨(j : ℕ) + 1, hj⟩)
      ≤ alphaMixCoeff μ (sigmaLE X (((j : ℕ) * (l + s) : ℕ) + l))
          (sigmaGE X ((((j : ℕ) * (l + s) : ℕ) + l : ℤ) + ((s : ℤ) + 1))) :=
        alphaMixCoeff_mono hpast hfut
    _ = alphaCoeff X μ (s + 1) := by
        have := hstat.alphaMixCoeff_shift hmeas ((((j : ℕ) * (l + s) : ℕ) + l : ℤ)) (s + 1)
        simpa using this
    _ ≤ alphaCoeff X μ s := alphaCoeff_antitone X (Nat.le_succ s)

/-- **NAMED PRIVATE DEBT** (Ibragimov–Linnik, *Independent and Stationary Sequences of
Random Variables*, 1971, Theorem 18.5.3; the technical lemma behind FY Theorem 2.21(ii)).

Under `|X| ≤ C`, strict stationarity, zero mean and `Σ α(j) < ∞`, the normalised block
sums `S_l²/l` are **uniformly integrable**, so the Lindeberg mass at a level `ε√n` with
`l_n/n → 0` vanishes.

**This is the single unproved brick of `clt_of_bounded_alphaMixing`.** It is *not*
derivable from the ambient hypotheses by the fourth-moment route: Yokoyama's bound
`E S_l⁴ = O(l²)` needs `Σ_j (j+1) α(j) < ∞`, strictly stronger than `Σ_j α(j) < ∞`, so
`Mixing/Inequalities.moment4_partial_sum_le` (which assumes `α(n) ≤ K n⁻²`) does not
apply. The statement below is the weakest true form that closes the Bernstein scheme. -/
private theorem lindeberg_blocks_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ) {C : ℝ}
    -- USER-INPUT: uniform bound; FY Thm 2.21(ii)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    -- USER-INPUT: zero mean; FY §2.6.3 setup
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    -- USER-INPUT: summable mixing coefficients; FY Thm 2.21(ii)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n)
    (l : ℕ → ℕ) (hl1 : ∀ n, 1 ≤ l n)
    (hln : Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ((l n : ℝ))⁻¹ *
        ∫ ω in {ω | ε * Real.sqrt n ≤ |∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω|},
          (∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  sorry

end Bernstein

/-- **FY Theorem 2.21(ii)** (full in-text proof, Bernstein blocks): bounded zero-mean
strictly stationary, summable α, positive long-run variance ⇒ `S_n/√n →d N(0, σ²)`
(charFun form). -/
theorem clt_of_bounded_alphaMixing [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {C : ℝ}
    -- USER-INPUT: uniform bound; FY Thm 2.21(ii)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    -- USER-INPUT: zero mean; FY §2.6.3 setup
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    -- USER-INPUT: summable mixing coefficients; FY Thm 2.21(ii)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n)
    -- USER-INPUT: positive long-run variance; FY Thm 2.21
    (hσ : 0 < acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))
    (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) u) atTop
      (𝓝 (charFun (gaussianReal 0
        (Real.toNNReal (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1)))) u)) := by
  classical
  set σ2 : ℝ := acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) with hσ2def
  have hSmeas : ∀ D : Finset ℕ, Measurable fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω :=
    fun D => Finset.measurable_sum _ fun t _ => hmeas _
  -- ### 0. Both sides as explicit integrals
  have hRHS : charFun (gaussianReal 0 (Real.toNNReal σ2)) u
      = Complex.exp (-((σ2 : ℂ) * (u : ℂ) ^ 2 / 2)) := by
    rw [charFun_gaussianReal, Real.coe_toNNReal _ hσ.le]
    congr 1
    push_cast
    ring
  have hcf : ∀ n : ℕ, charFun (μ.map fun ω =>
      (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) u
      = ∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ := by
    intro n
    have hae : AEMeasurable (fun ω => (Real.sqrt n)⁻¹ *
        ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ :=
      (measurable_const.mul (hSmeas _)).aemeasurable
    have hsm : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I))
        (μ.map fun ω => (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) :=
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    rw [charFun_apply_real, integral_map hae hsm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    congr 1
    push_cast
    ring
  rw [hRHS]
  simp only [hcf]
  -- ### 1. Block scheme and moment bookkeeping
  obtain ⟨hsumacvf, hrate⟩ := summable_acvf_and_var_rate_of_bounded hmeas hstat hbdd hmean hα
  obtain ⟨l, s, k, hs1, hl1, hfit, hltop, hln0, hkl, hkα⟩ := exists_block_scheme (X := X) hα
  set Λ : ℝ := ∑' j : ℤ, |acvf X μ j| with hΛdef
  have hΛ0 : 0 ≤ Λ := tsum_nonneg fun _ => abs_nonneg _
  have hSmem : ∀ (D : Finset ℕ) (q : ℝ≥0∞),
      MemLp (fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω) q μ := by
    intro D q
    have hfun : (fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω) = ∑ t ∈ D, X ((t : ℤ) + 1) := by
      funext ω; simp [Finset.sum_apply]
    rw [hfun]
    exact memLp_finset_sum' (μ := μ) D fun t _ => memLp_of_bdd hmeas hbdd _ q
  have hSint : ∀ D : Finset ℕ, Integrable (fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω) μ :=
    fun D => (hSmem D 1).integrable le_rfl
  have hSsq : ∀ D : Finset ℕ, Integrable (fun ω => (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2) μ :=
    fun D => (hSmem D 2).integrable_sq
  have hS1 : ∀ D : Finset ℕ, ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ∂μ = 0 :=
    integral_partialSum_eq_zero hmeas hstat hbdd hmean
  have hS2 : ∀ D : Finset ℕ, ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ ≤ Λ * (D.card : ℝ) :=
    integral_sq_partialSum_le hmeas hstat hbdd hmean hsumacvf
  have hS2nn : ∀ D : Finset ℕ, 0 ≤ ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ :=
    fun _ => integral_nonneg fun _ => sq_nonneg _
  -- the big-block variance rate
  have hltopN : Tendsto l atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hltop.eventually_ge_atTop (b : ℝ))
    exact ⟨N, fun a ha => by exact_mod_cast hN a ha⟩
  have hblock : Tendsto (fun n : ℕ => ((l n : ℝ))⁻¹ *
      ∫ ω, (∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω) ^ 2 ∂μ) atTop (𝓝 σ2) := by
    have hv : ∀ m : ℕ, variance (fun ω => ∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω) μ
        = ∫ ω, (∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω) ^ 2 ∂μ := fun m =>
      variance_of_integral_eq_zero (hSmem _ 2).aestronglyMeasurable.aemeasurable (hS1 _)
    have h := hrate.comp hltopN
    simpa only [Function.comp_def, hv] using h
  -- ### 2. Geometry of the block partition
  have hd : ∀ (n j j' : ℕ), j < j' →
      Disjoint (Finset.Ico (j * (l n + s n)) (j * (l n + s n) + l n))
        (Finset.Ico (j' * (l n + s n)) (j' * (l n + s n) + l n)) := by
    intro n j j' h
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_Ico] at ha ha'
    have h1 : (j + 1) * (l n + s n) ≤ j' * (l n + s n) := Nat.mul_le_mul_right _ h
    have h2 : (j + 1) * (l n + s n) = j * (l n + s n) + (l n + s n) := by ring
    omega
  have hdisj : ∀ (n : ℕ), ∀ j ∈ Finset.range (k n), ∀ j' ∈ Finset.range (k n), j ≠ j' →
      Disjoint (Finset.Ico (j * (l n + s n)) (j * (l n + s n) + l n))
        (Finset.Ico (j' * (l n + s n)) (j' * (l n + s n) + l n)) := by
    intro n j _ j' _ hne
    rcases Nat.lt_or_ge j j' with h | h
    · exact hd n j j' h
    · exact (hd n j' j (by omega)).symm
  set G : ℕ → Finset ℕ := fun n =>
    (Finset.range (k n)).biUnion fun j =>
      Finset.Ico (j * (l n + s n)) (j * (l n + s n) + l n) with hGdef
  have hGsub : ∀ n, G n ⊆ Finset.range n := by
    intro n a ha
    simp only [hGdef, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ico] at ha
    obtain ⟨j, hj, haj⟩ := ha
    have h1 : (j + 1) * (l n + s n) ≤ k n * (l n + s n) := Nat.mul_le_mul_right _ hj
    have h2 : (j + 1) * (l n + s n) = j * (l n + s n) + (l n + s n) := by ring
    have h4 := hfit n
    simp only [Finset.mem_range]
    omega
  have hGcard : ∀ n, (G n).card = k n * l n := by
    intro n
    simp only [hGdef]
    rw [Finset.card_biUnion (hdisj n)]
    simp [Nat.card_Ico, mul_comm]
  have hDcard : ∀ n, ((Finset.range n \ G n).card : ℝ) = (n : ℝ) - ((k n * l n : ℕ) : ℝ) := by
    intro n
    have hc : (Finset.range n \ G n).card + k n * l n = n := by
      have h := Finset.card_sdiff_add_card_eq_card (hGsub n)
      rwa [hGcard, Finset.card_range] at h
    have hcast : ((Finset.range n \ G n).card : ℝ) + ((k n * l n : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hc
    linarith
  have hsplit : ∀ (n : ℕ) (ω : Ω), ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω
      = (∑ t ∈ G n, X ((t : ℤ) + 1) ω) + ∑ t ∈ Finset.range n \ G n, X ((t : ℤ) + 1) ω := by
    intro n ω
    rw [add_comm]
    exact (Finset.sum_sdiff (hGsub n)).symm
  have hblocksum : ∀ (n : ℕ) (ω : Ω), ∑ t ∈ G n, X ((t : ℤ) + 1) ω
      = ∑ j ∈ Finset.range (k n), ∑ i ∈ Finset.range (l n),
          X ((i : ℤ) + 1 + ((j * (l n + s n) : ℕ) : ℤ)) ω := by
    intro n ω
    simp only [hGdef]
    rw [Finset.sum_biUnion (fun j hj j' hj' hne => hdisj n j hj j' hj' hne)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    push_cast
    ring
  -- ### 3. The three characteristic functions
  set Φ : ℕ → ℂ := fun n => ∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
      ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ with hΦdef
  set Φ' : ℕ → ℂ := fun n => ∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
      ∑ t ∈ G n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ with hΦ'def
  set φ : ℕ → ℂ := fun n => ∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
      ∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ with hφdef
  have hexpint : ∀ (D : Finset ℕ) (v : ℝ), Integrable (fun ω =>
      Complex.exp (((v * ∑ t ∈ D, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)) μ := by
    intro D v
    have hmf : Measurable fun ω =>
        Complex.exp (((v * ∑ t ∈ D, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) :=
      Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (measurable_const.mul (hSmeas D))).mul measurable_const)
    refine MemLp.integrable (q := ⊤) le_top (memLp_top_of_bound hmf.aestronglyMeasurable 1 ?_)
    filter_upwards with ω
    rw [Complex.norm_exp_ofReal_mul_I]
  -- ### 4. Gap A: small blocks + remainder are `L²`-negligible
  have hW : Tendsto (fun n : ℕ =>
      (∫ ω, (∑ t ∈ Finset.range n \ G n, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) / (n : ℝ))
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => Λ * (1 - ((k n * l n : ℕ) : ℝ) / (n : ℝ)))
        atTop (𝓝 0) := by
      have h := (hkl.const_sub 1).const_mul Λ
      simpa using h
    refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg (hS2nn _) (Nat.cast_nonneg _))
      ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 := hS2 (Finset.range n \ G n)
    rw [hDcard n] at h1
    rw [div_le_iff₀ hn0]
    have he : Λ * (1 - ((k n * l n : ℕ) : ℝ) / (n : ℝ)) * (n : ℝ)
        = Λ * ((n : ℝ) - ((k n * l n : ℕ) : ℝ)) := by field_simp
    rw [he]
    exact h1
  have hA : Tendsto (fun n : ℕ => Φ n - Φ' n) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => |u| * Real.sqrt
        ((∫ ω, (∑ t ∈ Finset.range n \ G n, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) / (n : ℝ))
        + 5 * u ^ 2 * ((∫ ω, (∑ t ∈ Finset.range n \ G n, X ((t : ℤ) + 1) ω) ^ 2 ∂μ)
          / (n : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Real.sqrt
          ((∫ ω, (∑ t ∈ Finset.range n \ G n, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) / (n : ℝ)))
          atTop (𝓝 0) := by
        have h := (Real.continuous_sqrt.tendsto 0).comp hW
        simpa [Function.comp_def] using h
      have := (h1.const_mul |u|).add (hW.const_mul (5 * u ^ 2))
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsq : Real.sqrt (n : ℝ) > 0 := Real.sqrt_pos.mpr hn0
    set D : Finset ℕ := Finset.range n \ G n with hDdef
    set w : ℝ := u * (Real.sqrt n)⁻¹ with hwdef
    -- pointwise phase-increment bound
    have hpt : ∀ ω : Ω, ‖Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ G n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)‖
        ≤ |w * ∑ t ∈ D, X ((t : ℤ) + 1) ω| + 5 * (w * ∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 := by
      intro ω
      have hreal : u * (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω
          = (u * (Real.sqrt n)⁻¹ * ∑ t ∈ G n, X ((t : ℤ) + 1) ω)
            + w * ∑ t ∈ D, X ((t : ℤ) + 1) ω := by
        rw [hsplit n ω, hwdef]; ring
      have hfac : Complex.exp (((u * (Real.sqrt n)⁻¹ *
            ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((u * (Real.sqrt n)⁻¹ *
            ∑ t ∈ G n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
          = Complex.exp (((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ G n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
            * (Complex.exp (((w * ∑ t ∈ D, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) - 1) := by
        rw [hreal, Complex.ofReal_add, add_mul, Complex.exp_add]
        ring
      rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact norm_expI_sub_one_le _
    have hint : Integrable (fun ω => |w * ∑ t ∈ D, X ((t : ℤ) + 1) ω|
        + 5 * (w * ∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2) μ := by
      refine Integrable.add ((hSint D).const_mul w).abs ?_
      have : Integrable (fun ω => (5 * w ^ 2) * (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2) μ :=
        (hSsq D).const_mul _
      refine this.congr (Eventually.of_forall fun ω => ?_)
      ring
    calc ‖Φ n - Φ' n‖
        = ‖∫ ω, (Complex.exp (((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ G n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)) ∂μ‖ := by
          rw [integral_sub (hexpint _ _) (hexpint _ _)]
      _ ≤ ∫ ω, ‖Complex.exp (((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ G n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (|w * ∑ t ∈ D, X ((t : ℤ) + 1) ω|
            + 5 * (w * ∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2) ∂μ :=
          integral_mono (((hexpint (Finset.range n) _).sub (hexpint (G n) _)).norm) hint hpt
      _ ≤ |u| * Real.sqrt ((∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) / (n : ℝ))
            + 5 * u ^ 2 * ((∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) / (n : ℝ)) := by
          have hE2 : 0 ≤ ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ := hS2nn D
          have hA1 : ∫ ω, |w * ∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ
              = |w| * ∫ ω, |∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ := by
            simp_rw [abs_mul]
            rw [integral_const_mul]
          have hA2 : ∫ ω, 5 * (w * ∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ
              = 5 * w ^ 2 * ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ := by
            have hpw : ∀ ω : Ω, 5 * (w * ∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2
                = (5 * w ^ 2) * (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 := fun ω => by ring
            simp_rw [hpw]
            rw [integral_const_mul]
          rw [integral_add ((hSint D).const_mul w).abs
            (((hSsq D).const_mul (5 * w ^ 2)).congr (Eventually.of_forall fun ω => by ring)),
            hA1, hA2]
          have hcs : (∫ ω, |∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ)
              ≤ Real.sqrt (∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) := by
            have h := sq_integral_abs_le (hSmem D 2)
            have hnn : 0 ≤ ∫ ω, |∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ :=
              integral_nonneg fun _ => abs_nonneg _
            calc (∫ ω, |∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ)
                = Real.sqrt ((∫ ω, |∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ) ^ 2) :=
                  (Real.sqrt_sq hnn).symm
              _ ≤ Real.sqrt (∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) := Real.sqrt_le_sqrt h
          have hw1 : |w| = |u| / Real.sqrt (n : ℝ) := by
            rw [hwdef, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
            ring
          have hw2 : w ^ 2 = u ^ 2 / (n : ℝ) := by
            rw [hwdef, mul_pow, inv_pow, Real.sq_sqrt hn0.le]
            ring
          rw [hw1, hw2, Real.sqrt_div hE2]
          have h1 : |u| / Real.sqrt (n : ℝ) * (∫ ω, |∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ)
              ≤ |u| / Real.sqrt (n : ℝ)
                * Real.sqrt (∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) :=
            mul_le_mul_of_nonneg_left hcs (by positivity)
          have heq1 : |u| / Real.sqrt (n : ℝ)
              * Real.sqrt (∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ)
              = |u| * (Real.sqrt (∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ)
                / Real.sqrt (n : ℝ)) := by ring
          have heq2 : 5 * (u ^ 2 / (n : ℝ)) * (∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ)
              = 5 * u ^ 2 * ((∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) / (n : ℝ)) := by ring
          linarith
  -- ### 5. Gap B: Volkonskii–Rozanov factorization; identical block laws give a power
  have hB : Tendsto (fun n : ℕ => Φ' n - (φ n) ^ (k n)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 16 * (k n : ℝ) * alphaCoeff X μ (s n)) atTop (𝓝 0) := by
      have h := hkα.const_mul (16 : ℝ)
      simpa [mul_assoc] using h
    refine squeeze_zero_norm' (Eventually.of_forall fun n => ?_) hlim
    have hprod : Φ' n = ∫ ω, ∏ j : Fin (k n), Complex.exp (((u * (Real.sqrt n)⁻¹ *
        ∑ i ∈ Finset.range (l n),
          X ((i : ℤ) + 1 + (((j : ℕ) * (l n + s n) : ℕ) : ℤ)) ω : ℝ) : ℂ) * Complex.I) ∂μ := by
      simp only [hΦ'def]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      dsimp only
      rw [hblocksum n ω]
      have hexpo : (((u * (Real.sqrt n)⁻¹ * ∑ j ∈ Finset.range (k n), ∑ i ∈ Finset.range (l n),
            X ((i : ℤ) + 1 + ((j * (l n + s n) : ℕ) : ℤ)) ω : ℝ)) : ℂ) * Complex.I
          = ∑ j : Fin (k n), ((((u * (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range (l n),
            X ((i : ℤ) + 1 + (((j : ℕ) * (l n + s n) : ℕ) : ℤ)) ω : ℝ)) : ℂ) * Complex.I) := by
        rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((((u * (Real.sqrt n)⁻¹ *
          ∑ i ∈ Finset.range (l n),
            X ((i : ℤ) + 1 + ((j * (l n + s n) : ℕ) : ℤ)) ω : ℝ)) : ℂ) * Complex.I))]
        push_cast
        rw [Finset.mul_sum, Finset.sum_mul]
      rw [hexpo, Complex.exp_sum]
    have hFmeas : Measurable fun x : ℝ =>
        Complex.exp (((u * (Real.sqrt n)⁻¹ * x : ℝ) : ℂ) * Complex.I) :=
      Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (measurable_const.mul measurable_id)).mul measurable_const)
    have hone : ∀ j : Fin (k n), (∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
        ∑ i ∈ Finset.range (l n),
          X ((i : ℤ) + 1 + (((j : ℕ) * (l n + s n) : ℕ) : ℤ)) ω : ℝ) : ℂ) * Complex.I) ∂μ)
        = φ n := fun j =>
      integral_comp_window_eq hmeas hstat hFmeas (l n) (((j : ℕ) * (l n + s n) : ℕ) : ℤ)
    have hfac : ∏ j : Fin (k n), (∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
        ∑ i ∈ Finset.range (l n),
          X ((i : ℤ) + 1 + (((j : ℕ) * (l n + s n) : ℕ) : ℤ)) ω : ℝ) : ℂ) * Complex.I) ∂μ)
        = (φ n) ^ (k n) := by
      rw [Finset.prod_congr rfl (fun j _ => hone j), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [hprod, ← hfac]
    refine le_trans (norm_integral_prod_blocks_sub_prod_le hmeas hstat (l n) (s n) (k n)
      (u * (Real.sqrt n)⁻¹)) ?_
    have hnn : 0 ≤ alphaCoeff X μ (s n) := alphaMixCoeff_nonneg
    nlinarith [hnn]
  sorry

/-- **DEBT (Bosq 1998 §1.5; FY Theorem 2.20(i))**: the `δ`-moment version of the
variance rate: `E|X|^δ < ∞` (δ > 2) and `Σ_j α(j)^{1−2/δ} < ∞` suffice. -/
theorem summable_acvf_and_var_rate_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {δ : ℝ}
    -- USER-INPUT: δ-moment; FY Thm 2.20(i)
    (hδ : 2 < δ) (hLδ : MemLp (X 0) (ENNReal.ofReal δ) μ)
    -- USER-INPUT: zero mean; FY §2.6.3 setup
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    -- USER-INPUT: Σ α^{1−2/δ} < ∞; FY Thm 2.20(i)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n ^ (1 - 2 / δ)) :
    (Summable fun k : ℤ => |acvf X μ k|) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
          variance (fun ω => ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ) atTop
        (𝓝 (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))) := by
  sorry

/-- **DEBT (Peligrad; FY Theorem 2.21(i))**: the `δ`-moment CLT under the Thm 2.20(i)
hypotheses and positive long-run variance. -/
theorem clt_of_alphaMixing_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {δ : ℝ} (hδ : 2 < δ) (hLδ : MemLp (X 0) (ENNReal.ofReal δ) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n ^ (1 - 2 / δ))
    (hσ : 0 < acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))
    (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) u) atTop
      (𝓝 (charFun (gaussianReal 0
        (Real.toNNReal (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1)))) u)) := by
  sorry

/-- **DEBT (Doob 1953 / Ibragimov–Linnik 1971; FY Proposition 2.8)**: the strong law
for α-mixing strictly stationary sequences with a first moment. The cited route is
"α-mixing ⇒ ergodicity" + the Birkhoff pointwise ergodic theorem, which the Mathlib
pin does not provide. -/
theorem slln_of_alphaMixing_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    (hL1 : Integrable (X 0) μ)
    -- USER-INPUT: α-mixing; FY Prop 2.8
    (hmix : IsAlphaMixing X μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
        (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) atTop
      (𝓝 (∫ ω', X 0 ω' ∂μ)) := by
  sorry

end StatLean.TimeSeries
