import Foundation.MarkedRealizationExponentialMartingale
import Foundation.HigherEvenRenewalMartingale
import Foundation.HigherEvenRenewalTransform

/-! Actual exponential martingales carry the full cyclic symbol at every even heat order. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherEvenExponentialMartingale

def normalized (m : ℕ) [NeZero m] (a : ℝ) (w : ℂ) :=
  MarkedRealizationExponentialMartingale.normalized (CyclicRootProbabilityNoise.probability (2*m))
    (HigherEvenRootInnovation.innovation m a) w

theorem normalized_martingale (m : ℕ) [NeZero m] (a : ℝ) (w : ℂ) :
    Martingale (normalized m a w) (HigherEvenRenewalMartingale.history m a)
      (HigherEvenRenewalProcess.probability m) :=
  MarkedRealizationExponentialMartingale.normalized_martingale
    (CyclicRootProbabilityNoise.probability (2*m)) (HigherEvenRootInnovation.innovation m a)
    (measurable_of_countable _) |a| (fun k => (HigherEvenRenewalProcess.innovation_norm m a k).le) w

theorem normalized_formula (m : ℕ) [NeZero m] (a : ℝ) (w : ℂ) (t : ℝ≥0)
    (ω : HigherEvenRenewalProcess.Sample m) :
    normalized m a w t ω = Complex.exp (w*HigherEvenRenewalProcess.process m a t ω-
      (t : ℂ)*HigherEvenRenewalTransform.symbol m a w) := by
  change Complex.exp (-(t : ℂ)*HigherEvenRenewalTransform.symbol m a w)*
    Complex.exp (w*HigherEvenRenewalProcess.process m a t ω) = _
  rw [← Complex.exp_add]
  congr 1
  ring

end OperatorDerivativeRewrite.Foundation.HigherEvenExponentialMartingale
