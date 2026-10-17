import Foundation.StickyVanishingBoundaryTest

/-! Both members of a nontrivial actual sticky martingale test pair belong to
C0(R). No closed-generator domain, density, or uniqueness theorem is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology ZeroAtInfty
namespace OperatorDerivativeRewrite.Foundation.StickyVanishingGeneratorPair
open InfiniteGaussian BrownianMassRandomTimeChange SmoothAbsoluteApproximation
open StickyC2MartingaleProblem StickyBoundaryGeneratorCore StickyVanishingBoundaryTest
set_option backward.isDefEq.respectTransparency false

theorem radius_tendsto (e : ℝ) (he : 0 < e) :
    Tendsto (radius e) (cocompact ℝ) atTop := by
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually (eventually_ge_atTop R)] with x hx
  have hx' : R ≤ |x| := by simpa only [Real.norm_eq_abs] using hx
  exact hx'.trans (abs_le_radius he x)

theorem curvature_tendsto (e : ℝ) (he : 0 < e) :
    Tendsto (curvature e) (cocompact ℝ) (𝓝 0) := by
  have h := ((radius_tendsto e he).inv_tendsto_atTop.pow 3).const_mul (e^2)
  have heq : curvature e = fun x => e^2*((radius e x)⁻¹)^3 := by
    funext x
    simp [curvature, div_eq_mul_inv, inv_pow]
  rw [heq]
  simpa only [zero_pow (by decide : 3 ≠ 0), mul_zero, Pi.inv_apply] using h

theorem generator_tendsto (κ : ℝ≥0) :
    Tendsto (candidateGenerator (base κ)) (cocompact ℝ) (𝓝 0) := by
  have h := (((curvature_tendsto 1 (by norm_num)).const_mul (a κ : ℝ)).sub
    ((curvature_tendsto 2 (by norm_num)).const_mul (b κ : ℝ))).const_mul (1/2 : ℝ)
  have he : candidateGenerator (base κ) =
      fun x => (1/2 : ℝ)*((a κ : ℝ)*curvature 1 x-(b κ : ℝ)*curvature 2 x) := by
    funext x
    rw [candidateGenerator, base_second_deriv]
  rw [he]
  simpa only [mul_zero, sub_zero] using h

def generatorC0 (κ : ℝ≥0) : C₀(ℝ, ℝ) where
  toFun := candidateGenerator (base κ)
  continuous_toFun := generator_continuous (base κ) (base_smooth κ)
  zero_at_infty' := generator_tendsto κ

theorem generator_zero (κ : ℝ≥0) : generatorC0 κ 0 = 1/4 := by
  change (1/2 : ℝ)*deriv (deriv (base κ)) 0 = 1/4
  rw [base_second_zero]
  norm_num

theorem right_derivative (κ : ℝ≥0) :
    HasDerivWithinAt (testC0 κ) ((κ : ℝ)/4) (Ici 0) 0 := by
  have he : (testC0 κ : ℝ → ℝ) = boundaryTest (base κ) κ := by funext x; rfl
  rw [he]
  have h := StickyC2MartingaleProblem.right_derivative (base κ) (base_smooth κ) κ
  simpa [base_deriv, SmoothAbsoluteApproximation.slope, coefficient_eq] using h

theorem left_derivative (κ : ℝ≥0) :
    HasDerivWithinAt (testC0 κ) (-(κ : ℝ)/4) (Iic 0) 0 := by
  have he : (testC0 κ : ℝ → ℝ) = boundaryTest (base κ) κ := by funext x; rfl
  rw [he]
  have h := StickyC2MartingaleProblem.left_derivative (base κ) (base_smooth κ) κ
  simpa [base_deriv, SmoothAbsoluteApproximation.slope, coefficient_eq, neg_div] using h

theorem boundary_condition (κ : ℝ≥0) :
    (κ : ℝ)/4-(-(κ : ℝ)/4) = 2*(κ : ℝ)*generatorC0 κ 0 := by
  rw [generator_zero]
  ring

theorem concrete_martingale (κ : ℝ≥0) :
    Martingale (fun t ω => testC0 κ (changedPath κ ω t)-testC0 κ 0-
      ∫ s in 0..(t : ℝ), generatorC0 κ (changedPath κ ω s.toNNReal))
      (augmentedPhysicalPast κ) gaussianProduct := StickyVanishingBoundaryTest.concrete_martingale κ

end OperatorDerivativeRewrite.Foundation.StickyVanishingGeneratorPair
