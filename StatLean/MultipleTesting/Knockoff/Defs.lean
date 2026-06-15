import Mathlib.Probability.Independence.Basic

/-!
# Knock-off score — definition

Concept-layer data model for the knock-off filter (Lu, *Big Data Analysis* §19, Def. `kos`).

A **knock-off score** is a statistic `W : Fin d → Ω → ℝ` whose defining property (Def. `kos`,
condition 3) is that the signs of the *null* coordinates are i.i.d. fair coins given the
magnitudes `|W₁|, …, |W_d|`. We formalize exactly that property — the only thing the FDR-control
proof consumes — as three fields on `KnockoffScore`:

* `signs_iIndep`     — the null signs `{sign Wⱼ : j ∈ H₀}` are jointly independent;
* `signs_fair`       — each null sign is fair, `P(Wⱼ ≥ 0) = ½`;
* `signs_indep_outer` — the null sign vector is independent of the *outer data* (the magnitudes
  `|W₁|,…,|W_d|` together with the non-null signs), the data the count filtration conditions on.

Together these say: *conditional on the magnitudes, the null signs are i.i.d. `Ber(½)`* — Def.
`kos` condition 3. The book's antisymmetry (condition 1) is an upstream property of the
*construction* of `W` that guarantees condition 3; condition 2 (`Wⱼ =ᵈ −Wⱼ` for nulls) is a
consequence of the three fields. The procedure (`S±`, `FDPhat`, `t*`, the rejection set) lives in
the assembly file `Knockoff.lean`.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

/-- Real-valued sign of `Wⱼ`: `+1` if `Wⱼ ≥ 0`, else `−1` (Lu-BDA §19). Under the no-ties
assumption `Wⱼ ≠ 0` a.s. (supplied as a theorem hypothesis) this is the genuine sign. -/
noncomputable def sgnReal (W : Fin d → Ω → ℝ) (j : Fin d) (ω : Ω) : ℝ :=
  if 0 ≤ W j ω then 1 else -1

/-- `KnockoffScore W H₀ μ`: the statistic `W : Fin d → Ω → ℝ` is a knock-off score for the true
null set `H₀` under `μ` (Lu-BDA §19, Def. `kos` condition 3) — the null signs are i.i.d. fair
coins given the magnitudes. -/
structure KnockoffScore (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (μ : Measure Ω) : Prop where
  /-- Constitutive (Lu-BDA §19, Def. `kos` cond. 3): the null signs `{sign Wⱼ : j ∈ H₀}` are
  jointly independent. -/
  signs_iIndep : iIndepFun (fun (j : H₀) (ω : Ω) => sgnReal W (j : Fin d) ω) μ
  /-- Constitutive (Lu-BDA §19, Def. `kos` cond. 3): each null sign is a fair coin,
  `P(Wⱼ ≥ 0) = ½` (with a probability measure). -/
  signs_fair : ∀ j ∈ H₀, μ {ω | 0 ≤ W j ω} = 1 / 2
  /-- Constitutive (Lu-BDA §19, Def. `kos` cond. 3): the null sign vector is independent of the
  *outer data* — the magnitude vector `(|Wⱼ|)ⱼ` **together with the non-null signs** (encoded, as in
  `cproc`, by the padded vector `fun j => if j ∈ H₀ then 0 else sgn Wⱼ`). This is the data the count
  filtration `𝒢rev` conditions on; with `signs_iIndep`/`signs_fair` it gives: conditional on the
  magnitudes and non-null signs, the null signs are i.i.d. `Ber(½)` — exactly what the exchangeable
  supermartingale step (`count_condExp`) consumes. Strengthens the former `signs_indep_mag` (⊥
  magnitudes only); ⊥ (magnitudes ⊕ non-null signs) is the genuine model-X knock-off property (null
  signs are fresh fair coins independent of all observed data). -/
  signs_indep_outer :
    IndepFun (fun ω (j : H₀) => sgnReal W (j : Fin d) ω)
      (fun ω => ((fun j => |W j ω|), (fun j => if j ∈ H₀ then (0 : ℝ) else sgnReal W j ω)))
      μ
  /-- Constitutive (Lu-BDA §19, Def. `kos`): a knock-off *score* is a statistic, so each `Wⱼ` is
  measurable. Needed for the martingale construction (natural filtration, adaptedness,
  integrability, conditional expectation) in `Knockoff/Supermartingale.lean`. -/
  meas : ∀ j, Measurable (W j)

end StatLean.MultipleTesting
