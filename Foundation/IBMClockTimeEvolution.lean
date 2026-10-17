import Foundation.IBMClockTransformDerivative
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Time evolution of the Laplace transform of an actual Gaussian Brownian clock. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockTimeEvolution
open IBMOneTimeFourier IBMGaussianLaplaceBoundary IBMClockTransformDerivative

theorem gaussian_scaling (t : ℝ≥0) :
    (gaussianReal 0 1).map (fun r : ℝ => Real.sqrt t*r) = gaussianReal 0 t := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · apply NNReal.eq
    simp only [NNReal.coe_mul,NNReal.coe_mk,NNReal.coe_one,mul_one]
    exact Real.sq_sqrt t.coe_nonneg

theorem transform_scaling (t : ℝ≥0) (a : ℝ) :
    clockTransform t a = clockTransform 1 (a*Real.sqrt t) := by
  unfold clockTransform
  rw [← gaussian_scaling t,integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with r
  rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  congr 1
  ring

def timeTransform (a t : ℝ) : ℝ := clockTransform t.toNNReal a

theorem timeTransform_eq (a t : ℝ) (ht : 0 ≤ t) :
    timeTransform a t = clockTransform 1 (a*Real.sqrt t) := by
  rw [timeTransform,transform_scaling,Real.coe_toNNReal _ ht]

theorem time_derivative (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (timeTransform a)
      (a^2/2*timeTransform a t-a*gaussianConstant/Real.sqrt t) t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hd := (parameter_derivative (a*Real.sqrt t) (mul_pos ha hs)).comp t
    ((Real.hasDerivAt_sqrt ht.ne').const_mul a)
  have he : timeTransform a =ᶠ[𝓝 t] fun s => clockTransform 1 (a*Real.sqrt s) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact timeTransform_eq a s hs.le
  have hh := hd.congr_of_eventuallyEq he
  convert hh using 1
  rw [timeTransform_eq a t ht.le]
  field_simp

end OperatorDerivativeRewrite.Foundation.IBMClockTimeEvolution
