import Foundation.IBMClockTimeEvolution
import Mathlib.Analysis.Complex.RealDeriv

/-! The time equation of actual IBM characteristic functions, with its boundary source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFourierTimeEquation
open IBMOneTimeFourier IBMGaussianLaplaceBoundary IBMClockTimeEvolution

theorem transform_zero_parameter (t : ℝ≥0) : clockTransform t 0=1 := by
  simp [clockTransform]

theorem time_derivative_nonneg (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) :
    HasDerivAt (timeTransform a)
      (a^2/2*timeTransform a t-a*gaussianConstant/Real.sqrt t) t := by
  rcases ha.eq_or_lt with h | h
  · subst a
    have hz : timeTransform 0 = fun _ => (1 : ℝ) := by
      funext s
      exact transform_zero_parameter s.toNNReal
    rw [hz]
    simpa using hasDerivAt_const t (1 : ℝ)
  · exact time_derivative a t h ht

def fourierLaw (u t : ℝ) : ℂ := charFun (IBMOneTimeMixture.mixture t.toNNReal) u

theorem fourierLaw_eq (u t : ℝ) :
    fourierLaw u t=(timeTransform (u^2/2) t : ℂ) := by
  exact mixture_characteristic t.toNNReal u

theorem fourier_derivative (u t : ℝ) (ht : 0 < t) :
    HasDerivAt (fourierLaw u)
      (((u^4/8 : ℝ) : ℂ)*fourierLaw u t-
        ((u^2/2*gaussianConstant/Real.sqrt t : ℝ) : ℂ)) t := by
  have hd := (time_derivative_nonneg (u^2/2) t (by positivity) ht).ofReal_comp
  have he : fourierLaw u = fun s => (timeTransform (u^2/2) s : ℂ) := by
    funext s
    exact fourierLaw_eq u s
  rw [he]
  convert hd using 1 <;> push_cast <;> ring

theorem signed_characteristic_derivative (u t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ =>
      ∫ ω, observable u (SignedIBMRealization.value s.toNNReal ω) ∂IBMSourceLaws.jointMeasure)
      (((u^4/8 : ℝ) : ℂ)*fourierLaw u t-
        ((u^2/2*gaussianConstant/Real.sqrt t : ℝ) : ℂ)) t := by
  have he : (fun s : ℝ =>
      ∫ ω, observable u (SignedIBMRealization.value s.toNNReal ω) ∂IBMSourceLaws.jointMeasure) =
      fourierLaw u := by
    funext s
    unfold fourierLaw
    rw [charFun_eq_observable]
    exact (IBMOneTimeMixture.signed_value_law s.toNNReal).integral_comp
      (observable_continuous u).aestronglyMeasurable
  rw [he]
  exact fourier_derivative u t ht

end OperatorDerivativeRewrite.Foundation.IBMFourierTimeEquation
