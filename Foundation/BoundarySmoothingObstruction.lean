import Foundation.DictionaryConditionalContraction

/-! A normalized interior kernel fixes boundary-only tests. Such a fixed test
places a quantitative lower bound on proximity to a strict smoother. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.BoundarySmoothingObstruction
set_option backward.isDefEq.respectTransparency false

def retainedKernel {X Y : Type*} [MeasurableSpace Y]
    (ν : X → Measure Y) (f : X → ℝ) (x : X) : ℝ := ∫ _y, f x ∂ν x

theorem retainedKernel_eq {X Y : Type*} [MeasurableSpace Y]
    (ν : X → Measure Y) (hν : ∀ x, IsProbabilityMeasure (ν x)) (f : X → ℝ) :
    retainedKernel ν f=f := by
  funext x
  letI := hν x
  simp [retainedKernel]

section Normed
variable {F G : Type*} [AddCommGroup F] [Module ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The standard reference-plus-error estimate is valid in a fixed linear seminorm. -/
theorem transfer_budget (D : F →ₗ[ℝ] G) (T R : F → F) (f : F) (q ε : ℝ)
    (hR : ‖D (R f)‖ ≤ q*‖D f‖) (herror : ‖D (T f-R f)‖ ≤ ε*‖D f‖) :
    ‖D (T f)‖ ≤ (q+ε)*‖D f‖ := by
  have he : D (T f)=D (R f)+D (T f-R f) := by rw [map_sub]; abel
  rw [he]
  calc
    _ ≤ ‖D (R f)‖+‖D (T f-R f)‖ := norm_add_le _ _
    _ ≤ q*‖D f‖+ε*‖D f‖ := add_le_add hR herror
    _ = _ := by ring

theorem fixed_error_lower (D : F →ₗ[ℝ] G) (T R : F → F) (f : F) (q : ℝ)
    (hfix : T f=f) (hR : ‖D (R f)‖ ≤ q*‖D f‖) :
    (1-q)*‖D f‖ ≤ ‖D (T f-R f)‖ := by
  have he : D f=D (R f)+D (T f-R f) := by rw [hfix,map_sub]; abel
  have hn := norm_add_le (D (R f)) (D (T f-R f))
  rw [← he] at hn
  nlinarith

theorem fixed_error_floor (D : F →ₗ[ℝ] G) (T R : F → F) (f : F) (q ε : ℝ)
    (hf : D f ≠ 0) (hfix : T f=f) (hR : ‖D (R f)‖ ≤ q*‖D f‖)
    (herror : ‖D (T f-R f)‖ ≤ ε*‖D f‖) : 1-q ≤ ε := by
  have hn : 0 < ‖D f‖ := norm_pos_iff.mpr hf
  have hl := fixed_error_lower D T R f q hfix hR
  nlinarith

theorem no_strict_error_budget (D : F →ₗ[ℝ] G) (T R : F → F) (f : F) (q ε η : ℝ)
    (hf : D f ≠ 0) (hfix : T f=f) (hR : ‖D (R f)‖ ≤ q*‖D f‖)
    (hη : 0 ≤ η) (hbudget : q+ε+η < 1) :
    ¬ ‖D (T f-R f)‖ ≤ ε*‖D f‖ := by
  intro he
  have hl := fixed_error_floor D T R f q ε hf hfix hR he
  linarith

/-- Even an approximately fixed test forces the total error to cover its defect. -/
theorem approximate_fixed_budget (D : F →ₗ[ℝ] G) (T R : F → F) (f : F) (q ε δ : ℝ)
    (hf : D f ≠ 0) (hR : ‖D (R f)‖ ≤ q*‖D f‖)
    (herror : ‖D (T f-R f)‖ ≤ ε*‖D f‖)
    (hfix : ‖D (f-T f)‖ ≤ δ*‖D f‖) : 1 ≤ q+ε+δ := by
  have hb := transfer_budget D T R f q ε hR herror
  have he : D f=D (T f)+D (f-T f) := by rw [map_sub]; abel
  have hn := norm_add_le (D (T f)) (D (f-T f))
  rw [← he] at hn
  have hp : 0 < ‖D f‖ := norm_pos_iff.mpr hf
  nlinarith
end Normed

def mehlerDifference (t : ℝ) (x : ℝ) : ℝ := x-GaussianMehler.mehler t id x

theorem mehlerDifference_formula (t : ℝ) :
    mehlerDifference t=fun x : ℝ => (1-Real.exp (-t))*x := by
  funext x
  unfold mehlerDifference
  rw [DictionaryConditionalContraction.mehler_coordinate]
  simp only [id_eq]
  ring

theorem mehlerDifference_gradient (t : ℝ) (ht : 0 ≤ t) :
    DictionaryConditionalContraction.lowGradientNorm (mehlerDifference t)=1-Real.exp (-t) := by
  have hp : 0 ≤ 1-Real.exp (-t) := by
    have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  rw [mehlerDifference_formula]
  simp [DictionaryConditionalContraction.lowGradientNorm,Real.sqrt_sq_eq_abs,abs_of_nonneg hp]

/-- Actual Mehler smoothing attains the fixed-test error floor on the Gaussian coordinate. -/
theorem mehler_gradient_budget_exact (t : ℝ) (ht : 0 ≤ t) :
    DictionaryConditionalContraction.lowGradientNorm (GaussianMehler.mehler t id)+
      DictionaryConditionalContraction.lowGradientNorm (mehlerDifference t)=1 := by
  rw [DictionaryConditionalContraction.mehler_coordinate_gradient,mehlerDifference_gradient t ht]
  ring

theorem mehler_difference_positive (t : ℝ) (ht : 0 < t) :
    0 < DictionaryConditionalContraction.lowGradientNorm (mehlerDifference t) := by
  rw [mehlerDifference_gradient t ht.le]
  have he : Real.exp (-t)<1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

end OperatorDerivativeRewrite.Foundation.BoundarySmoothingObstruction
