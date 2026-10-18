import Foundation.SignedSchwartzClosedDerivative

/-! A genuine complete Hilbert majorant and its signed fundamental symmetry. -/
noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap ENNReal
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzFundamentalSymmetry
open SignedSchwartzL2Rigging SignedSchwartzClosedDerivative

def sign (K : 𝓢(ℝ, ℝ)) (x : ℝ) : ℝ := if 0 ≤ K x then 1 else -1

theorem sign_measurable (K : 𝓢(ℝ, ℝ)) : Measurable (sign K) :=
  Measurable.ite (measurableSet_le measurable_const K.continuous.measurable)
    measurable_const measurable_const

theorem sign_square (K : 𝓢(ℝ, ℝ)) (x : ℝ) : sign K x * sign K x = 1 := by
  by_cases h : 0 ≤ K x <;> simp [sign, h]

theorem sign_density (K : 𝓢(ℝ, ℝ)) (x : ℝ) : |K x| * sign K x = K x := by
  by_cases h : 0 ≤ K x
  · simp [sign, h, abs_of_nonneg h]
  · simp [sign, h, abs_of_neg (lt_of_not_ge h)]

theorem sign_memLp (K : 𝓢(ℝ, ℝ)) : MemLp (sign K) ∞ (measure K) := by
  apply memLp_top_of_bound (sign_measurable K).aestronglyMeasurable 1
  exact Eventually.of_forall (fun x => by
    by_cases h : 0 ≤ K x <;> simp [sign, h])

def symmetry (K : 𝓢(ℝ, ℝ)) : H K →L[ℝ] H K :=
  boundedMultiplier (H := ℂ) (sign K) (sign_memLp K)

theorem symmetry_ae (K : 𝓢(ℝ, ℝ)) (u : H K) :
    symmetry K u =ᵐ[measure K] (fun x => sign K x • u x) :=
  boundedMultiplier_coeFn _ _ u

theorem symmetry_twice (K : 𝓢(ℝ, ℝ)) (u : H K) : symmetry K (symmetry K u) = u := by
  apply Lp.ext
  filter_upwards [symmetry_ae K (symmetry K u), symmetry_ae K u] with x hx hu
  rw [hx, hu, smul_smul, sign_square, one_smul]

theorem symmetry_selfadjoint (K : 𝓢(ℝ, ℝ)) (u v : H K) :
    inner ℝ (symmetry K u) v = inner ℝ u (symmetry K v) :=
  boundedMultiplier_symmetric _ _ u v

theorem symmetry_norm (K : 𝓢(ℝ, ℝ)) (u : H K) : ‖symmetry K u‖ = ‖u‖ := by
  have he := symmetry_selfadjoint K u (symmetry K u)
  rw [symmetry_twice, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

theorem symmetry_injective (K : 𝓢(ℝ, ℝ)) : Function.Injective (symmetry K) := by
  intro u v h
  have he := congrArg (symmetry K) h
  simpa only [symmetry_twice] using he

def form (K : 𝓢(ℝ, ℝ)) : H K →L[ℝ] H K →L[ℝ] ℝ :=
  (innerSL ℝ).comp (symmetry K)

theorem form_apply (K : 𝓢(ℝ, ℝ)) (u v : H K) :
    form K u v = inner ℝ (symmetry K u) v := rfl

theorem form_symmetric (K : 𝓢(ℝ, ℝ)) (u v : H K) : form K u v = form K v u := by
  rw [form_apply, form_apply, symmetry_selfadjoint, real_inner_comm]

theorem form_detects_norm (K : 𝓢(ℝ, ℝ)) (u : H K) :
    form K u (symmetry K u) = ‖u‖^2 := by
  rw [form_apply, real_inner_self_eq_norm_sq, symmetry_norm]

theorem form_nondegenerate (K : 𝓢(ℝ, ℝ)) (u : H K)
    (h : ∀ v : H K, form K u v = 0) : u=0 := by
  have he := h (symmetry K u)
  rw [form_detects_norm] at he
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])

theorem form_core (K : 𝓢(ℝ, ℝ)) (f g : 𝓢(ℝ, ℂ)) :
    form K (coreInput K f) (coreInput K g) =
      ∫ x, sign K x * inner ℝ (f x) (g x) ∂measure K := by
  rw [form_apply, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [symmetry_ae K (coreInput K f), f.coeFn_toLp 2 (measure K),
    g.coeFn_toLp 2 (measure K)] with x hx hf hg
  change inner ℝ ((symmetry K (coreInput K f)) x) ((g.toLp 2 (measure K)) x) = _
  rw [hx]
  change inner ℝ (sign K x • (f.toLp 2 (measure K)) x) ((g.toLp 2 (measure K)) x) = _
  rw [hf, hg, real_inner_smul_left]

theorem form_core_density (K : 𝓢(ℝ, ℝ)) (f g : 𝓢(ℝ, ℂ)) :
    form K (coreInput K f) (coreInput K g) = ∫ x : ℝ, K x * inner ℝ (f x) (g x) := by
  have hm : Measurable (fun x : ℝ => |K x|) := by
    simpa only [Real.norm_eq_abs] using K.continuous.measurable.norm
  rw [form_core, SignedSchwartzL2Rigging.measure, SignedAbsoluteIntegration.absoluteDensity,
    integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top (r := |K x|)))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change (ENNReal.ofReal |K x|).toReal * (sign K x * inner ℝ (f x) (g x)) =
      K x * inner ℝ (f x) (g x)
    rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    change |K x| * (sign K x * inner ℝ (f x) (g x)) = _
    rw [← mul_assoc, sign_density])

end OperatorDerivativeRewrite.Foundation.SignedSchwartzFundamentalSymmetry
