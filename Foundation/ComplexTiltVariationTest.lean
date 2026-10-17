import Foundation.ComplexRootNormTransform

/-! A fixed bounded continuous observable reads off the total variation
of the actual tilted laws. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexTiltVariationTest

def cancelPhase (ξ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-Complex.I*(ξ : ℂ)*(z.re : ℂ))

theorem cancelPhase_continuous (ξ : ℝ) : Continuous (cancelPhase ξ) := by
  unfold cancelPhase
  fun_prop

theorem cancelPhase_norm (ξ : ℝ) (z : ℂ) : ‖cancelPhase ξ z‖ = 1 := by
  simp [cancelPhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

def test (ξ : ℝ) : ℂ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (cancelPhase ξ) (cancelPhase_continuous ξ) 1
    (fun z => (cancelPhase_norm ξ z).le)

theorem cancelPhase_phase (ξ : ℝ) (z : ℂ) :
    cancelPhase ξ z * Complex.exp (Complex.I*(ξ : ℂ)*z) =
      (‖Complex.exp (Complex.I*(ξ : ℂ)*z)‖ : ℂ) := by
  rw [cancelPhase, ← Complex.exp_add, Complex.norm_exp, Complex.ofReal_exp]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem cancelPhase_density (a ξ : ℝ) (r : ℝ≥0) (z : ℂ) :
    cancelPhase ξ z * ComplexRootTiltedLaw.density a ξ r z =
      (‖ComplexRootTiltedLaw.density a ξ r z‖ : ℂ) := by
  have hr : Complex.exp (-(r : ℂ)*MarkedHolomorphicExponential.symbol a ξ) =
      (Real.exp (-(r : ℝ)*(Real.cos (a*ξ)*Real.cosh (a*ξ)-1)) : ℂ) := by
    rw [ComplexRootNormTransform.symbol_real, Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  calc
    _ = Complex.exp (-(r : ℂ)*MarkedHolomorphicExponential.symbol a ξ) *
        (cancelPhase ξ z * Complex.exp (Complex.I*(ξ : ℂ)*z)) := by
      unfold ComplexRootTiltedLaw.density
      ring
    _ = _ := by
      rw [cancelPhase_phase]
      simp only [ComplexRootTiltedLaw.density, norm_mul, Complex.ofReal_mul, hr,
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]

theorem test_integral (a ξ : ℝ) (r : ℝ≥0) :
    (∫ᵛ z, test ξ z ∂[ContinuousLinearMap.mul ℝ ℂ; ComplexRootTiltedLaw.law a ξ r]) =
      (Real.exp ((r : ℝ)*Real.cosh (a*ξ)*(1-Real.cos (a*ξ))) : ℂ) := by
  rw [ComplexRootTiltedLaw.law, ComplexDensityIntegral.integral_density _ _
    (ComplexRootTiltedLaw.density_integrable a ξ r) (fun z => test ξ z)
    (test ξ).continuous.measurable 1 zero_le_one (fun z => (cancelPhase_norm ξ z).le)]
  have he : (fun z => test ξ z * ComplexRootTiltedLaw.density a ξ r z) =
      (fun z => (‖ComplexRootTiltedLaw.density a ξ r z‖ : ℂ)) :=
    funext (cancelPhase_density a ξ r)
  rw [he, integral_complex_ofReal, ComplexRootNormTransform.tilted_density_norm_mean]

end OperatorDerivativeRewrite.Foundation.ComplexTiltVariationTest
