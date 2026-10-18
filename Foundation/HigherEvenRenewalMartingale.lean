import Foundation.MarkedRealizationMartingale
import Foundation.HigherEvenRenewalProcess

/-! Genuine native natural-filtration martingales at every positive even heat order. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherEvenRenewalMartingale

def history (m : ℕ) [NeZero m] (a : ℝ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (HigherEvenRenewalProcess.Sample m)) :=
  MarkedRealizationMartingale.history (HigherEvenRootInnovation.innovation m a)
    (measurable_of_countable _)

theorem process_martingale (m : ℕ) [NeZero m] (a : ℝ) :
    Martingale (fun t : ℝ≥0 => HigherEvenRenewalProcess.process m a t)
      (history m a) (HigherEvenRenewalProcess.probability m) := by
  apply MarkedRealizationMartingale.value_martingale
    (CyclicRootProbabilityNoise.probability (2*m)) (HigherEvenRootInnovation.innovation m a)
    (measurable_of_countable _) |a|
    (fun k => (HigherEvenRenewalProcess.innovation_norm m a k).le)
  simpa only [pow_one] using HigherEvenRootInnovation.lower_moment m a 1
    (by decide) (by have hm := NeZero.pos m; omega)

end OperatorDerivativeRewrite.Foundation.HigherEvenRenewalMartingale
