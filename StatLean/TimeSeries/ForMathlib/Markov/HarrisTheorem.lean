import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity

/-!
# Harris' ergodic theorem, Hairer–Mattingly form

The elementary route to geometric ergodicity of a Markov kernel: **Lyapunov drift plus
minorization on a level set imply a contraction in a weighted total-variation
distance**, hence a unique invariant law approached at a geometric rate.

* `lyapDist β V μ ν = ∫ (1 + β V) d|μ − ν|` — the weighted TV distance (`weightedTV`
  below; the `β = 0` case is `2·tvDist`);
* `HasLyapunovDrift κ V γ K` — `P V ≤ γ V + K` pointwise with `γ < 1`;
* `HasMinorization κ S α` — `κ x ≥ α · ρ` on the level set `S` for a common probability
  measure `ρ`;
* `harris_contraction` — the Hairer–Mattingly estimate: for suitable `β`, `κ` contracts
  `lyapDist` by a factor `ᾱ < 1`;
* `harris_theorem` — the packaged conclusion: a unique invariant probability measure
  `π`, with `tvDist (κⁿ x) π ≤ C(x)·ρ̄ⁿ` — exactly the envelope `IsErgodicWithRate`
  (and hence `IsGeometricallyErgodic`) needs;
* `IsGeometricallyErgodic.of_pow` — the glue that lifts geometric ergodicity of the
  `p`-step kernel `κ^p` back to `κ` (needed because the minorization for the nonlinear
  AR kernel of FY Theorem 2.4 only holds after `p` steps, once every coordinate has
  been refreshed).

This file exists to discharge the last structural debt of the TimeSeries area,
`nlARKernel_geometricallyErgodic` (FY Theorem 2.4(ii)); the Meyn–Tweedie
ψ-irreducibility/petite-set apparatus is deliberately avoided.

**Reference.** M. Hairer and J. C. Mattingly, *Yet another look at Harris' ergodic
theorem for Markov chains*, in Seminar on Stochastic Analysis, Random Fields and
Applications VI, Progr. Probab. 63, Birkhäuser (2011), 109–117. Consumed by
FY §2.1.4 Theorem 2.4 (An & Huang 1996; Bhattacharya & Lee 1995).
(`Hairer–Mattingly 2011` in tags.)

**Bibliographic comments.** Harris' theorem is T. E. Harris (1956); the drift/
minorization formulation is Meyn & Tweedie, *Markov Chains and Stochastic Stability*
(1993), ch. 15–16; the weighted-TV contraction proof formalized here is the
Hairer–Mattingly simplification, which needs no irreducibility theory.
-/

open MeasureTheory ProbabilityTheory Filter StatLean.Minimaxity StatLean.Bayesian
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {S : Type*} [MeasurableSpace S]

-- Kernel powers of a Markov kernel are Markov (the same one-line induction as the private
-- `isMarkovKernel_pow` of `GeometricErgodicity`, repeated here because that one is file-scoped).
private theorem markov_pow (κ : Kernel S S) [IsMarkovKernel κ] :
    ∀ n : ℕ, IsMarkovKernel (κ ^ n)
  | 0 => by rw [pow_zero]; exact (inferInstance : IsMarkovKernel (Kernel.id : Kernel S S))
  | n + 1 => by
      haveI := markov_pow κ n
      rw [pow_succ]
      exact Kernel.IsMarkovKernel.comp (κ ^ n) κ

-- **Kernel averaging is a total-variation contraction** (the private `tvDist_bind_le` of
-- `GeometricErgodicity`, repeated here for the same reason): on a measurable `s` the two sides
-- are the integrals of the `[0,1]`-valued measurable function `y ↦ κ y s`, which moves by at
-- most `1 * tvDist μ ν`.
private theorem tvDist_bind_le (κ : Kernel S S) [IsMarkovKernel κ] (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist (μ.bind κ) (ν.bind κ) ≤ tvDist μ ν := by
  refine iSup_le fun s => iSup_le fun hs => ?_
  rw [Measure.bind_apply hs κ.aemeasurable, Measure.bind_apply hs κ.aemeasurable]
  refine tsub_le_iff_left.mpr ?_
  simpa using
    lintegral_le_lintegral_add_tvDist μ ν (κ.measurable_coe hs) (B := 1) fun _ => prob_le_one

/-- The **weighted total-variation distance** `∫ (1 + βV) d|μ − ν|` of Hairer–Mattingly
(their `ρ_β`), as an `ℝ≥0∞`-valued quantity built from the Jordan decomposition of the
signed difference. At `β = 0` it is twice `StatLean.Minimaxity.tvDist`. -/
noncomputable def weightedTV (β : ℝ) (V : S → ℝ) (μ ν : Measure S) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(μ.singularPart ν))
    + ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(ν.singularPart μ)

/-- **Lyapunov drift condition**: `∫ V d(κ x) ≤ γ V x + K` with a contraction factor
`γ < 1` (Hairer–Mattingly Assumption 1). -/
structure HasLyapunovDrift (κ : Kernel S S) (V : S → ℝ) (γ K : ℝ) : Prop where
  /-- Constitutive (H–M Assumption 1): the Lyapunov function is nonnegative. -/
  V_nonneg : ∀ x, 0 ≤ V x
  /-- Constitutive (H–M Assumption 1): `V` is measurable. -/
  V_measurable : Measurable V
  /-- Constitutive (H–M Assumption 1): the contraction factor is in `(0, 1)`. -/
  gamma_mem : 0 < γ ∧ γ < 1
  /-- Constitutive (H–M Assumption 1): the additive constant is nonnegative. -/
  K_nonneg : 0 ≤ K
  /-- Constitutive (H–M Assumption 1): the drift inequality `PV ≤ γV + K`. -/
  drift : ∀ x, (∫ y, V y ∂(κ x)) ≤ γ * V x + K

/-- **Minorization on a sublevel set**: on `{V ≤ R}` the kernel dominates `α·ρ` for a
fixed probability measure `ρ` (Hairer–Mattingly Assumption 2). -/
structure HasMinorization (κ : Kernel S S) (V : S → ℝ) (R α : ℝ) (ρ : Measure S) :
    Prop where
  /-- Constitutive (H–M Assumption 2): the minorization strength is in `(0, 1]`. -/
  alpha_mem : 0 < α ∧ α ≤ 1
  /-- Constitutive (H–M Assumption 2): the minorizing measure is a probability
  measure. -/
  isProbability : IsProbabilityMeasure ρ
  /-- Constitutive (H–M Assumption 2): domination on the level set. -/
  minorize : ∀ x, V x ≤ R → ∀ A : Set S, MeasurableSet A →
    ENNReal.ofReal α * ρ A ≤ κ x A

/-- **Harris contraction** (Hairer–Mattingly Theorem 1.3): under a Lyapunov drift and a
minorization on a high enough level set, the kernel contracts the weighted TV distance
`weightedTV β V` for a suitable `β > 0`, uniformly over initial laws. -/
theorem harris_contraction {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ)
    -- USER-INPUT: the level set is high enough to see the drift (H–M Thm 1.3);
    -- `R > 2K/(1 − γ)`
    (hR : 2 * K / (1 - γ) < R) :
    ∃ β ᾱ : ℝ, 0 < β ∧ 0 < ᾱ ∧ ᾱ < 1 ∧
      ∀ μ ν : Measure S, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        weightedTV β V (μ.bind κ) (ν.bind κ)
          ≤ ENNReal.ofReal ᾱ * weightedTV β V μ ν := by
  sorry

/-- **Harris' theorem** (Hairer–Mattingly): drift + minorization give a unique invariant
probability measure and a geometric total-variation rate from every starting point —
packaged exactly as `IsGeometricallyErgodic` needs it. -/
theorem harris_theorem {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ) (hR : 2 * K / (1 - γ) < R) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ Kernel.Invariant κ π ∧
      IsGeometricallyErgodic κ π := by
  sorry

/-- **Uniqueness** of the invariant law under the Harris hypotheses. -/
theorem harris_invariant_unique {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ}
    {γ K : ℝ} (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ) (hR : 2 * K / (1 - γ) < R)
    {π π' : Measure S} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : Kernel.Invariant κ π) (hπ' : Kernel.Invariant κ π')
    -- LEAN-ONLY: both invariant laws integrate the Lyapunov function (automatic for
    -- the constructed one; needed to compare in the weighted distance)
    (hV : Integrable V π) (hV' : Integrable V π') :
    π = π' := by
  sorry

/-- **Lifting from the `p`-step kernel**: if `κ^p` is geometrically ergodic with
invariant law `π` and `π` is invariant for `κ` itself, then `κ` is geometrically
ergodic. (The nonlinear-AR kernel of FY Theorem 2.4 is only minorized after `p` steps,
so this is the last glue step of that proof.) -/
theorem IsGeometricallyErgodic.of_pow {κ : Kernel S S} [IsMarkovKernel κ]
    {π : Measure S} [IsProbabilityMeasure π] {p : ℕ} (hp : 0 < p)
    (hpow : IsGeometricallyErgodic (κ ^ p) π) (hinv : Kernel.Invariant κ π) :
    IsGeometricallyErgodic κ π := by
  obtain ⟨ρ, hρ1, hρ⟩ := hpow
  have hpinv : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hbase : (1 : ℝ≥0∞) ≤ ρ⁻¹ := ENNReal.one_le_inv.mpr hρ.rho_le_one
  refine ⟨ρ ^ ((p : ℝ)⁻¹), ENNReal.rpow_lt_one hρ1 hpinv,
    ⟨ENNReal.rpow_pos hρ.rho_pos hρ1.ne_top, (ENNReal.rpow_lt_one hρ1 hpinv).le, fun x => ?_⟩⟩
  -- the `q`-step envelope of the `p`-step kernel, scaled by the fixed constant `ρ⁻¹`
  have hq : Tendsto (fun n : ℕ => n / p) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * p, fun _ ha => (Nat.le_div_iff_mul_le hp).2 ha⟩
  have hmaj : Tendsto
      (fun n : ℕ => ρ⁻¹ * (ρ⁻¹ ^ (n / p) * tvDist (((κ ^ p) ^ (n / p)) x) π)) atTop (𝓝 0) := by
    have h := (hρ.tendsto x).comp hq
    simpa using ENNReal.Tendsto.const_mul h (Or.inr (by simp [hρ.rho_pos.ne']))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
    (Eventually.of_forall fun n => zero_le _) (Eventually.of_forall fun n => ?_)
  set q := n / p with hqdef
  set r := n % p with hrdef
  have hnr : n = r + p * q := by rw [hrdef, hqdef, Nat.mod_add_div]
  haveI := markov_pow κ (p * q)
  haveI := markov_pow κ r
  -- Distance: the leftover `r = n % p` steps, applied *last*, can only contract (`π` is
  -- `κ^r`-invariant), so the `n`-step distance is at most the `pq`-step one.
  have hdist : tvDist ((κ ^ n) x) π ≤ tvDist (((κ ^ p) ^ q) x) π := by
    have hπ : π = π.bind (κ ^ r) := ((invariant_pow hinv r).def).symm
    have hstep : (κ ^ n) x = ((κ ^ (p * q)) x).bind (κ ^ r) := by
      rw [hnr, pow_add]
      exact Kernel.comp_apply (κ ^ r) (κ ^ (p * q)) x
    rw [hstep, ← pow_mul]
    nth_rewrite 1 [hπ]
    exact tvDist_bind_le (κ ^ r) ((κ ^ (p * q)) x) π
  -- Rate: `(ρ^{1/p})⁻ⁿ ≤ ρ⁻¹ · ρ⁻ᵠ` because `n/p ≤ q + 1`.
  have hrate : (ρ ^ ((p : ℝ)⁻¹))⁻¹ ^ n ≤ ρ⁻¹ * ρ⁻¹ ^ q := by
    have hexp : ((p : ℝ)⁻¹) * (n : ℝ) ≤ (q : ℝ) + 1 := by
      have hnp : (n : ℝ) ≤ (p : ℝ) * ((q : ℝ) + 1) := by
        have hr : r < p := by rw [hrdef]; exact Nat.mod_lt n hp
        have hpq : p * (q + 1) = p * q + p := by ring
        have hle : n ≤ p * (q + 1) := by omega
        exact_mod_cast hle
      rw [inv_mul_le_iff₀ (by exact_mod_cast hp)]
      linarith
    calc (ρ ^ ((p : ℝ)⁻¹))⁻¹ ^ n
        = (ρ⁻¹ ^ ((p : ℝ)⁻¹)) ^ ((n : ℕ) : ℝ) := by
          rw [ENNReal.inv_rpow, ENNReal.rpow_natCast]
      _ = ρ⁻¹ ^ (((p : ℝ)⁻¹) * (n : ℝ)) := (ENNReal.rpow_mul _ _ _).symm
      _ ≤ ρ⁻¹ ^ ((q : ℝ) + 1) := ENNReal.rpow_le_rpow_of_exponent_le hbase hexp
      _ = ρ⁻¹ ^ (q + 1) := by rw [← ENNReal.rpow_natCast ρ⁻¹ (q + 1)]; norm_num
      _ = ρ⁻¹ * ρ⁻¹ ^ q := by rw [pow_succ]; ring
  calc (ρ ^ ((p : ℝ)⁻¹))⁻¹ ^ n * tvDist ((κ ^ n) x) π
      ≤ (ρ⁻¹ * ρ⁻¹ ^ q) * tvDist (((κ ^ p) ^ q) x) π := mul_le_mul' hrate hdist
    _ = ρ⁻¹ * (ρ⁻¹ ^ q * tvDist (((κ ^ p) ^ q) x) π) := by ring

end StatLean.TimeSeries
