import StatLean.NonparametricStatistics.RKHS.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The representer theorem

Regularized empirical risk minimization over an RKHS:
`J(f) = W(‖f‖²) + L(f(x₁), …, f(xₙ))`, with `W` increasing and `L` depending only on
the values at the data points.

* **Representer theorem**: if `W` is *strictly* increasing, every minimizer of `J` lies
  in `span {k_{x₁}, …, k_{xₙ}}` — the problem is intrinsically finite-dimensional.
  (For merely monotone `W`, the orthogonal projection of a minimizer onto the span is
  again a minimizer with the same data values.)
* **Existence and uniqueness** for the ridge form `J(f) = ‖f‖² + L(...)` with `L`
  convex and continuous: the parallelogram law gives uniqueness, and coercivity via an
  affine minorant of `L` gives existence.

**Bibliographic comments.** G. Kimeldorf and G. Wahba, *Some results on Tchebycheffian
spline functions*, J. Math. Anal. Appl. **33** (1971), 82–95; the general form with an
arbitrary increasing regularizer is due to B. Schölkopf, R. Herbrich and A. J. Smola,
*A generalized representer theorem*, COLT (2001).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]
variable {n : ℕ}

/-- The span of the kernel functions at the data points — the finite-dimensional
subspace in which representer solutions live. -/
def dataSpan (x : Fin n → X) : Submodule 𝕜 H :=
  Submodule.span 𝕜 (Set.range fun i => kernelFun H (x i))

instance (x : Fin n → X) : FiniteDimensional 𝕜 (dataSpan (H := H) x) := by
  unfold dataSpan
  exact FiniteDimensional.span_of_finite 𝕜 (Set.finite_range fun i => kernelFun H (x i))

instance (x : Fin n → X) : IsClosed ((dataSpan (H := H) x : Submodule 𝕜 H) : Set H) :=
  Submodule.closed_of_finiteDimensional _

/-- Functions orthogonal to the data span vanish at the data points. -/
theorem apply_eq_zero_of_mem_dataSpan_orthogonal {x : Fin n → X} {h : H}
    (hh : h ∈ (dataSpan x)ᗮ) (i : Fin n) : h (x i) = 0 := by
  have hmem : kernelFun H (x i) ∈ dataSpan (H := H) x := Submodule.subset_span ⟨i, rfl⟩
  have := (Submodule.mem_orthogonal _ _).mp hh _ hmem
  rwa [inner_kernelFun] at this

/-- Projecting onto the data span preserves the data values. -/
theorem starProjection_dataSpan_apply {x : Fin n → X} (f : H) (i : Fin n) :
    ((dataSpan x).starProjection f) (x i) = f (x i) := by
  have h := apply_eq_zero_of_mem_dataSpan_orthogonal
    (Submodule.sub_starProjection_mem_orthogonal (K := dataSpan (H := H) x) f) i
  simp only [RKHS.coe_sub, Pi.sub_apply, sub_eq_zero] at h
  exact h.symm

/-- **The representer theorem**: for `W` strictly increasing and any data-dependent loss
`L`, every minimizer of `f ↦ W(‖f‖²) + L(f ∘ x)` lies in the span of the kernel
functions of the data points. -/
theorem representer_mem_dataSpan (x : Fin n → X) (W : ℝ → ℝ)
    -- USER-INPUT: strictly increasing regularizer
    (hW : StrictMono W)
    (L : (Fin n → 𝕜) → ℝ) (f₀ : H)
    -- USER-INPUT: `f₀` minimizes the regularized empirical risk
    (hmin : ∀ f : H, W (‖f₀‖ ^ 2) + L (fun i => f₀ (x i))
      ≤ W (‖f‖ ^ 2) + L (fun i => f (x i))) :
    f₀ ∈ dataSpan x := by
  set g : H := (dataSpan x).starProjection f₀ with hg
  have hval : ∀ i, g (x i) = f₀ (x i) := fun i => starProjection_dataSpan_apply f₀ i
  have hle : W (‖f₀‖ ^ 2) ≤ W (‖g‖ ^ 2) := by
    have := hmin g
    simp only [hval] at this
    linarith
  have hnorm : ‖f₀‖ ^ 2 ≤ ‖g‖ ^ 2 := (hW.le_iff_le).mp hle
  have hle' : ‖g‖ ≤ ‖f₀‖ := Submodule.norm_starProjection_apply_le _ f₀
  have : ‖g‖ = ‖f₀‖ := by nlinarith [norm_nonneg f₀, norm_nonneg g]
  exact ((dataSpan x).mem_iff_norm_starProjection f₀).mpr this

/-- Representer theorem, weak (monotone) form: the projection of a minimizer onto the
data span is again a minimizer. -/
theorem representer_starProjection_isMin (x : Fin n → X) (W : ℝ → ℝ)
    -- USER-INPUT: monotone regularizer
    (hW : Monotone W)
    (L : (Fin n → 𝕜) → ℝ) (f₀ : H)
    -- USER-INPUT: `f₀` minimizes the regularized empirical risk
    (hmin : ∀ f : H, W (‖f₀‖ ^ 2) + L (fun i => f₀ (x i))
      ≤ W (‖f‖ ^ 2) + L (fun i => f (x i))) :
    ∀ f : H, W (‖(dataSpan x).starProjection f₀‖ ^ 2)
        + L (fun i => ((dataSpan x).starProjection f₀) (x i))
      ≤ W (‖f‖ ^ 2) + L (fun i => f (x i)) := by
  intro f
  have hval : ∀ i, ((dataSpan x).starProjection f₀) (x i) = f₀ (x i) :=
    fun i => starProjection_dataSpan_apply f₀ i
  have hle' : ‖(dataSpan x).starProjection f₀‖ ≤ ‖f₀‖ :=
    Submodule.norm_starProjection_apply_le _ f₀
  have hW' : W (‖(dataSpan x).starProjection f₀‖ ^ 2) ≤ W (‖f₀‖ ^ 2) :=
    hW (by nlinarith [norm_nonneg f₀, norm_nonneg ((dataSpan x).starProjection f₀)])
  simp only [hval]
  have := hmin f
  linarith

/-- **Existence and uniqueness for convex ridge losses**: with the regularizer `‖f‖²`
and `L` convex, the regularized empirical risk has a unique minimizer.  (Continuity of
`L` on the finite-dimensional value space is automatic from convexity.) -/
theorem representer_existsUnique_of_convex (x : Fin n → X) (L : (Fin n → 𝕜) → ℝ)
    -- USER-INPUT: convex loss (in the data values, over the real structure)
    (hL : ConvexOn ℝ Set.univ L) :
    ∃! f₀ : H, ∀ f : H, ‖f₀‖ ^ 2 + L (fun i => f₀ (x i))
      ≤ ‖f‖ ^ 2 + L (fun i => f (x i)) := by
  sorry

/-- The hinge loss `v ↦ ∑ᵢ max(0, 1 − λᵢ·vᵢ)` of the soft-margin classifier is convex,
so the soft-margin problem has a unique solution in the data span. -/
theorem convexOn_hinge (lab : Fin n → ℝ) :
    ConvexOn ℝ Set.univ fun v : Fin n → ℝ => ∑ i, max 0 (1 - lab i * v i) := by
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hai : (1 : ℝ) - lab i * ((s • a + t • b) i)
      = s * (1 - lab i * a i) + t * (1 - lab i * b i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hst]
  refine max_le ?_ ?_
  · have h1 : 0 ≤ s * max 0 (1 - lab i * a i) := mul_nonneg hs (le_max_left _ _)
    have h2 : 0 ≤ t * max 0 (1 - lab i * b i) := mul_nonneg ht (le_max_left _ _)
    linarith
  · rw [hai]
    exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) hs)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) ht)

end StatLean.NonparametricStatistics
