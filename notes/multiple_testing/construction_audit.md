# Knockoff martingale construction — audit (Phase 2, 2026-06-14)

Gates Phases 3–4 (the 3 remaining `Supermartingale.lean` sorries: `step_condExp_le`,
`FDPhat_atTheta_adapted`, `ratio_eq_Yproc_hittingIdx`). Conclusion first, then the reasoning.

## TL;DR

The current scaffold reduces the master inequality to a **one-step** supermartingale inequality
`step_condExp_le : μ[Yproc (n+1) | 𝒢rev n] ≤ᵐ Yproc n` with `𝒢rev = Filtration.natural Yproc`.
Auditing against Lu §19 (and the underlying Barber–Candès 2015 argument) surfaces a **structural
tension that cannot be resolved by filling the three sorries against the current scaffold**:

* the **supermartingale step** is sound only under a *coarse* conditioning (the textbook `F_t`
  knows the **total** null count above `t`, not the sign split — so `V₊ | V₊+V₋` is hypergeometric);
* but **`FDPhat_atTheta_adapted`** (needed for `tauStar` to be a stopping time) requires `FDPhat(θ_n)`
  — the all-coordinate observable estimator `(#S⁻+1)/(#S⁺∨1)` — to be `𝒢rev n`-measurable, which
  needs *finer* information than `σ(Yproc 0..n)` (the null ratios) exposes.

Coarse ⇒ supermartingale holds but `FDPhat` is not adapted. Fine (reveal signs) ⇒ `FDPhat` adapted
but the one-step inequality is **false** (see algebra below). A single `Filtration.natural`-based
`𝒢rev` in the `Yproc`-over-rising-threshold indexing cannot satisfy both.

## The textbook filtration (Lu §19, chapter19.tex line 236, verbatim)

> `E( V₊(s)/(1+V₋(s)) | 𝓕_t ) ≤ V₊(t)/(1+V₋(t))` for `s ≥ t`, where `𝓕_t` contains information
> "if `j ∈ H₀` for `|W_j| > t` and `V₋(t)+V₊(t)`."

So `𝓕_t = σ(` magnitudes `|W|`, null-membership of coords with `|W_j|>t`, and the **total**
`V₊(t)+V₋(t)` `)`. It **does not** contain the individual null signs above `t` — that is the whole
point ("`V₊(t) | V₊(t)+V₋(t)` is hypergeometric, as the signs are i.i.d. `Ber(½)`"). Note that under
this `𝓕_t`, `V₊(t)/(1+V₋(t))` is itself **not** `𝓕_t`-measurable (the split is unknown); the textbook
uses "supermartingale" heuristically.

## Why the naive one-step inequality is false (fine conditioning)

`Yproc n = M(θ_n) = V₊(θ_n)/(1+V₋(θ_n))`, `θ_n` = n-th smallest null magnitude; as `n` increases the
threshold rises and the n-th null `j*` leaves the above-threshold set. If `𝒢rev n` reveals `j*`'s
sign, the update is deterministic:

* `j*` positive: `Yproc(n+1) = (V₊−1)/(1+V₋)`  (≤ `Yproc n` ✓);
* `j*` negative: `Yproc(n+1) = V₊/V₋`           (≥ `Yproc n` ✗, smaller denominator).

Averaging with a fresh `½` coin: `½(V₊−1)/(1+V₋) + ½ V₊/V₋ ≤ V₊/(1+V₋) ⟺ V₊ ≤ V₋`, **false in
general**. So `Yproc` is **not** a one-step supermartingale w.r.t. any filtration that reveals the
boundary sign. The genuine result needs the *coarse* conditional law (hypergeometric given the total),
i.e. an **exchangeability / sampling-without-replacement** argument, not a one-coin computation.

## The adaptedness obstruction (coarse conditioning)

`FDPhat(θ_n) = (#S⁻(θ_n)+1)/(#S⁺(θ_n)∨1)` counts over **all `d` coordinates** (Procedure.lean:
`S± = univ.filter …`). It is a function of the magnitudes **and the individual signs above `θ_n`**.
`σ(Yproc 0..n)` only determines the null **ratios** `V₊/(1+V₋)` at the thresholds — not `#S±`, not
even the null split `V₊,V₋` separately. Hence `FDPhat(θ_n)` is **not** `𝒢rev n = Filtration.natural
Yproc`-measurable, and `FDPhat_atTheta_adapted` is **not provable as stated**. Enriching `𝒢rev` to
reveal the signs (to make `FDPhat` adapted) re-introduces the boundary sign and breaks the
supermartingale step (previous section).

## Recommendation

`step_condExp_le` (one-step supermartingale via `supermartingale_nat`) is **not the right
reduction** for the knockoff master inequality. Two viable paths to a sound completion:

1. **Faithful Barber–Candès reconstruction (correct, heavier).** Replace the `supermartingale_nat`
   route with the exchangeability/optional-stopping argument: condition on the magnitudes and the
   **multiset** of null signs (equivalently `V₊(0)+V₋(0)`); the sign assignment to the ordered
   magnitudes is a uniform arrangement; `V₊(t)/(1+V₋(t))` run as `t` increases is a
   sampling-without-replacement supermartingale, and `tauStar` is a stopping time of the
   **observable** filtration. This needs a new `ForMathlib` brick (an exchangeable / hypergeometric
   supermartingale, absent from Mathlib) and a re-statement of `𝒢rev`, `knockoff_supermartingale`,
   `tauStar_isStoppingTime`. Substantial; the genuine research core.

2. **Isolate the gap honestly (lighter, what the approved plan calls for).** Keep the three sorries
   but **retag** them: `step_condExp_le`'s docstring must record that it is the
   exchangeable-supermartingale core (NOT a fresh-coin/`nlinarith` finish) and that its validity is
   contingent on the coarse-conditioning reading; `FDPhat_atTheta_adapted` must record that it is
   **only provable after `𝒢rev`/`tauStar` are re-based on the observable-sign filtration** (path 1),
   i.e. it is blocked on the reconstruction, not mere bookkeeping. Do **not** fill these against the
   current scaffold — a "proof" of `FDPhat_atTheta_adapted` w.r.t. `Filtration.natural Yproc` would be
   either false or hypothesis-laundering.

**Decision needed from the user** (the difficulty is materially higher than the plan's "intricate
bookkeeping" estimate for residuals 2–3): pursue path 1 (reconstruct, multi-session research) or
path 2 (retag + document, leaving the 3 as honest research debts). Phase 1 (the binomial reduction,
`knockoff_initial_integral_le_binom_sum`) is **closed** regardless — it never depended on the
filtration.

## State

`mt/area`: green, **3 sorries**, all `Supermartingale.lean` (`step_condExp_le:261`,
`FDPhat_atTheta_adapted:293`, `ratio_eq_Yproc_hittingIdx:325`). BH, Holm, `knockoff_fdp_le`,
`knockoff_initial_le` (+ its binomial reduction), `knockoff_fdr_le`, and the master-inequality
*assembly* are proven; only the supermartingale **core + its adapted stopping time** remain, and the
audit shows they are entangled as above.
