import Foundation.IBMInitialCusp

/-! A concrete obstruction to convolution-semigroup composition of actual IBM laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology Convolution
namespace OperatorDerivativeRewrite.Foundation.IBMConvolutionObstruction
open IBMOneTimeFourier IBMGaussianLaplaceBoundary IBMClockTransformDerivative
open IBMClockTimeEvolution IBMFourierTimeEquation IBMInitialCusp IBMOneTimeMixture

theorem transform_one_pos (a : ℝ) (ha : 0 ≤ a) : 0 < timeTransform a 1 := by
  change 0 < ∫ r : ℝ, Real.exp (-a*|r|) ∂gaussianReal 0 (1 : ℝ).toNNReal
  norm_num
  simpa only [neg_mul] using (integral_exp_pos (transform_integrable a ha))

theorem no_unit_shift_multiplication (a : ℝ) (ha : 0 < a) :
    ¬ ∀ s : ℝ, 0 ≤ s →
      timeTransform a (s+1)=timeTransform a s*timeTransform a 1 := by
  intro h
  have hp := transform_one_pos a ha.le
  have hd := (time_derivative a 1 ha (by norm_num)).comp_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).add_const 1) (by simp)
  have hq := hd.div_const (timeTransform a 1)
  have he : timeTransform a =ᶠ[𝓝[Ici 0] 0]
      fun s : ℝ => timeTransform a (s+1)/timeTransform a 1 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [h s hs,mul_div_cancel_right₀ _ hp.ne']
  have he0 : timeTransform a 0 = timeTransform a (0+1)/timeTransform a 1 := by
    rw [h 0 (by norm_num),mul_div_cancel_right₀ _ hp.ne']
  have hw := hq.hasDerivWithinAt (s := Ici 0)
  have hc := hw.congr_of_eventuallyEq he he0
  exact no_initial_right_derivative a _ ha.ne' hc

theorem not_convolution_semigroup :
    ¬ ∀ s t : ℝ≥0, mixture (s+t)=mixture s ∗ mixture t := by
  intro h
  apply no_unit_shift_multiplication (1/2) (by norm_num)
  intro s hs
  have hc := congrArg (fun μ : Measure ℝ => charFun μ (1 : ℝ)) (h s.toNNReal 1)
  rw [charFun_conv,mixture_characteristic,mixture_characteristic,mixture_characteristic] at hc
  have hr := congrArg Complex.re hc
  norm_num at hr
  change clockTransform (s+1).toNNReal (1/2) =
    clockTransform s.toNNReal (1/2)*clockTransform (1 : ℝ).toNNReal (1/2)
  rw [Real.toNNReal_add hs (by norm_num)]
  simpa using hr

end OperatorDerivativeRewrite.Foundation.IBMConvolutionObstruction
