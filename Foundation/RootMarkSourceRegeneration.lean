import Foundation.RootRenewalWalkMarginal
import Foundation.MarkedSourceRegeneration

/-! Genuine finite-past/infinite-future splitting of the actual root-mark source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RootMarkSourceRegeneration
open MarkedRootRenewalProcess

def tail (n : ℕ) (η : MarkSample) : MarkSample := fun j => η (n+j)

theorem tail_measurable (n : ℕ) : Measurable (tail n) :=
  MarkedSourceRegeneration.tail_measurable n

theorem tail_preserving (n : ℕ) : MeasurePreserving (tail n) marks marks :=
  MarkedSourceRegeneration.tail_preserving ComplexFourthRootNoise.probability n

theorem past_tail_independent (n : ℕ) :
    IndepFun (RootRenewalWalkMarginal.initialSegment n) (tail n) marks :=
  MarkedSourceRegeneration.past_tail_independent ComplexFourthRootNoise.probability n

theorem split_preserving (n : ℕ) :
    MeasurePreserving (fun η => (RootRenewalWalkMarginal.initialSegment n η,tail n η)) marks
      ((ComplexFourthRootWalk.probability n).prod marks) :=
  MarkedSourceRegeneration.split_preserving ComplexFourthRootNoise.probability n

theorem position_add (a : ℝ) (n k : ℕ) (η : MarkSample) :
    position a (n+k) η = position a n η + position a k (tail n η) :=
  MarkedSourceRegeneration.position_add (ComplexFourthRootNoise.noise a) n k η

theorem position_increment (a : ℝ) (n k : ℕ) (η : MarkSample) :
    position a (n+k) η-position a n η = position a k (tail n η) :=
  MarkedSourceRegeneration.position_increment (ComplexFourthRootNoise.noise a) n k η

end OperatorDerivativeRewrite.Foundation.RootMarkSourceRegeneration
