import Foundation.ComplexRootPoissonTransform
import Foundation.ComplexDensityUnbounded

/-! Actual complex-weighted four-point transition operators and their compensated generators. -/
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootTiltedStep
open ComplexFourthRootNoise ComplexRootTransitionOperator

def weight (a ξ : ℝ) (k : Fin 4) : ℂ := Complex.exp (Complex.I*(ξ : ℂ)*noise a k)

def weightedStep (a ξ : ℝ) : Test →L[ℂ] Test :=
  (1/4 : ℂ) • ∑ k : Fin 4, weight a ξ k • shift (noise a k)

theorem weightedStep_apply (a ξ : ℝ) (f : Test) (z : ℂ) :
    weightedStep a ξ f z = (1/4 : ℂ) * ∑ k : Fin 4,
      weight a ξ k * f (z+noise a k) := by
  simp [weightedStep, shift, smul_eq_mul]

theorem weightedStep_integral (a ξ : ℝ) (f : Test) (z : ℂ) :
    weightedStep a ξ f z = ∫ k, weight a ξ k * f (z+noise a k)
      ∂ComplexFourthRootNoise.probability := by
  rw [weightedStep_apply, integral_formula]
  norm_num [Fin.sum_univ_succ]
  ring

theorem weightedStep_bound (a ξ : ℝ) (f : Test) :
    ‖weightedStep a ξ f‖ ≤ Real.exp (2 * |a| * |ξ|) * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro z
  rw [weightedStep_integral]
  calc
    _ ≤ ∫ k, ‖weight a ξ k * f (z+noise a k)‖
        ∂ComplexFourthRootNoise.probability := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : Fin 4, Real.exp (2 * |a| * |ξ|) * ‖f‖
        ∂ComplexFourthRootNoise.probability :=
      integral_mono_ae Integrable.of_finite (integrable_const _) (Eventually.of_forall fun k => by
        change ‖weight a ξ k * f (z+noise a k)‖ ≤ Real.exp (2 * |a| * |ξ|) * ‖f‖
        rw [norm_mul]
        exact mul_le_mul (ComplexRootPoissonTransform.exponential_noise_bound a ξ k)
          (f.norm_coe_le_norm _) (norm_nonneg _) (le_of_lt (Real.exp_pos _)))
    _ = _ := by simp

theorem weightedStep_norm (a ξ : ℝ) :
    ‖weightedStep a ξ‖ ≤ Real.exp (2 * |a| * |ξ|) := by
  exact (weightedStep a ξ).opNorm_le_bound (le_of_lt (Real.exp_pos _))
    (weightedStep_bound a ξ)

theorem weightedStep_constant (a ξ : ℝ) (c : ℂ) :
    weightedStep a ξ (BoundedContinuousFunction.const ℂ c) =
      BoundedContinuousFunction.const ℂ (ComplexFourthRootWalk.stepTransform a ξ*c) := by
  ext z
  rw [weightedStep_integral]
  change (∫ k, weight a ξ k * c ∂ComplexFourthRootNoise.probability) =
    (∫ k, weight a ξ k ∂ComplexFourthRootNoise.probability) * c
  exact integral_mul_const c _

def generator (a ξ : ℝ) : Test →L[ℂ] Test :=
  weightedStep a ξ - ComplexFourthRootWalk.stepTransform a ξ • ContinuousLinearMap.id ℂ Test

theorem generator_apply (a ξ : ℝ) (f : Test) (z : ℂ) :
    generator a ξ f z = (∫ k, weight a ξ k * (f (z+noise a k)-f z)
      ∂ComplexFourthRootNoise.probability) := by
  change weightedStep a ξ f z - ComplexFourthRootWalk.stepTransform a ξ * f z = _
  rw [weightedStep_integral]
  change _ - (∫ k, weight a ξ k ∂ComplexFourthRootNoise.probability) * f z = _
  rw [← integral_mul_const]
  change _ - (∫ k, weight a ξ k * f z ∂ComplexFourthRootNoise.probability) = _
  rw [← integral_sub Integrable.of_finite Integrable.of_finite]
  apply integral_congr_ae
  exact Eventually.of_forall fun k => (mul_sub _ _ _).symm

theorem generator_constant (a ξ : ℝ) (c : ℂ) :
    generator a ξ (BoundedContinuousFunction.const ℂ c) = 0 := by
  ext z
  rw [generator_apply]
  simp

end OperatorDerivativeRewrite.Foundation.ComplexRootTiltedStep
