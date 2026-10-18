import Foundation.MarkedRenewalExponentialTransform
import Foundation.HigherEvenRenewalProcess
import Foundation.CyclicPolynomialKernel

/-! Actual all-even-order process transforms and their normalized heat exponents. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherEvenRenewalTransform

def markTransform (m : ℕ) [NeZero m] (a : ℝ) (w : ℂ) : ℂ :=
  MarkedRenewalExponentialTransform.oneStep (CyclicRootProbabilityNoise.probability (2*m))
    (HigherEvenRootInnovation.innovation m a) w

def symbol (m : ℕ) [NeZero m] (a : ℝ) (w : ℂ) : ℂ := markTransform m a w-1

def normalizedSymbol (m : ℕ) [NeZero m] (a : ℝ) (w : ℂ) : ℂ :=
  (CyclicPolynomialKernel.rate m a : ℂ)*symbol m a w

theorem exponential_integrable (m : ℕ) [NeZero m] (a : ℝ) (t : ℝ≥0) (w : ℂ) :
    Integrable (fun ω => Complex.exp (w*HigherEvenRenewalProcess.process m a t ω))
      (HigherEvenRenewalProcess.probability m) :=
  MarkedRenewalExponentialTransform.exponential_integrable _ _ (measurable_of_countable _) |a|
    (fun k => (HigherEvenRenewalProcess.innovation_norm m a k).le) t w

theorem process_transform (m : ℕ) [NeZero m] (a : ℝ) (t : ℝ≥0) (w : ℂ) :
    (∫ ω, Complex.exp (w*HigherEvenRenewalProcess.process m a t ω)
      ∂HigherEvenRenewalProcess.probability m) = Complex.exp ((t : ℂ)*symbol m a w) := by
  simpa only [HigherEvenRenewalProcess.process,HigherEvenRenewalProcess.probability,symbol,markTransform] using
    MarkedRenewalExponentialTransform.process_transform (CyclicRootProbabilityNoise.probability (2*m))
      (HigherEvenRootInnovation.innovation m a) (measurable_of_countable _) |a|
      (fun k => (HigherEvenRenewalProcess.innovation_norm m a k).le) t w

theorem normalized_transform (m : ℕ) [NeZero m] (a : ℝ) (ha : a ≠ 0) (t : ℝ≥0) (w : ℂ) :
    (∫ ω, Complex.exp (w*HigherEvenRenewalProcess.process m a
        (Real.toNNReal (CyclicPolynomialKernel.rate m a)*t : ℝ≥0) ω)
      ∂HigherEvenRenewalProcess.probability m) = Complex.exp ((t : ℂ)*normalizedSymbol m a w) := by
  rw [process_transform m a (Real.toNNReal (CyclicPolynomialKernel.rate m a)*t) w]
  have hr := (CyclicPolynomialKernel.rate_pos m a ha).le
  have hc : ((Real.toNNReal (CyclicPolynomialKernel.rate m a)*t : ℝ≥0) : ℂ) =
      (CyclicPolynomialKernel.rate m a : ℂ)*(t : ℂ) := by
    have he : ((Real.toNNReal (CyclicPolynomialKernel.rate m a)*t : ℝ≥0) : ℝ) =
        CyclicPolynomialKernel.rate m a*(t : ℝ) := by rw [NNReal.coe_mul,Real.coe_toNNReal _ hr]
    simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal he
  rw [hc]
  congr 1
  unfold normalizedSymbol
  ring

end OperatorDerivativeRewrite.Foundation.HigherEvenRenewalTransform
