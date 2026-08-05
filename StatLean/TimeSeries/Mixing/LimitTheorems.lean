import StatLean.TimeSeries.Mixing.Inequalities
import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT

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
      push_cast
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
  sorry

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
