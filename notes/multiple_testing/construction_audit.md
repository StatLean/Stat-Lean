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

## RESOLUTION (the correct construction — 2026-06-14)

The tension dissolves with the **count filtration** (not `Filtration.natural Yproc`, not the
sign-revealing fine filtration):

`𝒢rev n := σ( |W| (all magnitudes), the non-null signs, and the null split-counts
(V₊(θ_k), V₋(θ_k)) for k ≤ n )`.

Under `𝒢rev n`:
* `Yproc n = V₊(θ_n)/(1+V₋(θ_n))` is adapted (the split-counts are exposed). ✓
* `FDPhat(θ_n) = (#S⁻(θ_n)+1)/(#S⁺(θ_n)∨1)` is adapted: `#S±(θ_n) = (non-null ± above θ_n,
  known from magnitudes + non-null signs) + V±(θ_n)` (known). ⇒ **`FDPhat_atTheta_adapted` is
  PROVABLE** w.r.t. `𝒢rev`. ✓
* `Yproc` is a **supermartingale** — the genuine, correct statement.

**Why it is a supermartingale (the exact computation).** Going `n → n+1` raises the threshold past
the `(n+1)`-th smallest null; by **exchangeability** of the i.i.d. `Ber(½)` null signs, conditional
on `𝒢rev n` (which fixes only the *counts* `A := V₊(θ_n)`, `B := V₋(θ_n)`, `k := A+B` among the
`N₀−n` remaining), the removed null's sign is **uniform among the remaining**:
`E[𝟙(removed = +) | 𝒢rev n] = A/k`, `E[𝟙(removed = −) | 𝒢rev n] = B/k`. The removal is then
deterministic given which sign: `+ ⇒ (A−1)/(1+B)`, `− ⇒ A/B`. Hence
```
E[Yproc(n+1) | 𝒢rev n] = (A/k)·(A−1)/(1+B) + (B/k)·(A/B)
                       = (A/k)·[ (A−1)/(1+B) + 1 ] = (A/k)·(A+B)/(1+B) = A/(1+B) = Yproc n
```
(a martingale equality when `B ≥ 1`; at `B = 0` the `−` branch has probability 0 and the value is
`A−1 ≤ A`, a strict supermartingale). So `E[Yproc(n+1)|𝒢rev n] ≤ Yproc n` — `step_condExp_le` is
**TRUE** w.r.t. the count filtration (it was the *one-step/fresh-coin* reading, and the
`Filtration.natural Yproc` reading, that were wrong).

**This re-bases the scaffold and pins the lone research brick.** `supermartingale_nat` is still
usable (the one-step inequality now holds), but `step_condExp_le` decomposes as:
1. `count_condExp` *(the research brick — no Mathlib support)*:
   `E[𝟙(sign of the (n+1)-th smallest null = +) | 𝒢rev n] =ᵐ V₊(θ_n)/(V₊(θ_n)+V₋(θ_n))`
   — the conditional expectation of an exchangeable indicator given the count filtration =
   empirical fraction (sampling-without-replacement / Pólya). This is the genuine nugget.
2. `step_removal_eq` *(deterministic counting)*: `Yproc(n+1) = 𝟙(+)·(V₊−1)/(1+V₋) + 𝟙(−)·V₊/V₋`.
3. `step_ratio_le` *(finite inequality, `nlinarith`)*:
   `(A/k)·(A−1)/(1+B) + (B/k)·(A/B) ≤ A/(1+B)` (`/0 = 0` conventions; `B=0` edge gives `A−1 ≤ A`).

**Reconstruction work-list (Phases 3–4, revised):**
- ✅ **DONE (Step A, builds green).** `𝒢rev` re-based as the count filtration `Filtration.natural
  cproc` (`cproc` = magnitudes ⊕ non-null signs ⊕ `(V₊(θ_n),V₋(θ_n))`); `measurable_cproc`,
  `measurable_Vplus_theta`/`measurable_Vminus_theta`, and `Yproc_adapted` (via `g ∘ cproc`) proven;
  all downstream (`knockoff_supermartingale`, `tauStar_isStoppingTime`, `knockoff_ratio_stopped_le_one`)
  recompiled unchanged against the new `𝒢rev`.
- ✅ `step_ratio_le` proven (`ForMathlib/BinomialRatio`).
- ✅ **DONE (builds green).** `FDPhat_atTheta_adapted` — `FDPhat(θ_n) = G(cproc n)` via the
  `#S±(θ_n) = V±(θ_n) + (non-null count)` decomposition (`Splus_card_decomp`/`Sminus_card_decomp`),
  the rank condition for the threshold, and the sign equivalences `0<W_j ↔ sgnReal=1∧|W_j|≠0`,
  `W_j<0 ↔ sgnReal=-1` on non-nulls; `G` Borel-measurable on the product. (Note: `Adapted` is
  `Measurable`-based here.)
- ⬜ `ratio_eq_Yproc_hittingIdx`: deterministic order-stat ↔ hitting (~80 lines).
- ⬜ `step_condExp_le`: assemble from `count_condExp` (brick, sorry) + `step_removal_eq` (counting:
  removing the boundary null shifts `V₊` or `V₋` by 1) + `step_ratio_le` (✅), via `condExp_add`
  + `condExp_mul_of_stronglyMeasurable_*` to pull the count factors out and `count_condExp` for the
  indicator. `count_condExp` (`E[𝟙(removed=+)|𝒢rev n] = V₊/(V₊+V₋)`) is the single documented
  research brick (no Mathlib sampling-without-replacement conditional-expectation support).

## State

`mt/area`: green, **3 sorries**, all `Supermartingale.lean` (`step_condExp_le:261`,
`FDPhat_atTheta_adapted:293`, `ratio_eq_Yproc_hittingIdx:325`). BH, Holm, `knockoff_fdp_le`,
`knockoff_initial_le` (+ its binomial reduction), `knockoff_fdr_le`, and the master-inequality
*assembly* are proven; only the supermartingale **core + its adapted stopping time** remain, and the
audit shows they are entangled as above.
