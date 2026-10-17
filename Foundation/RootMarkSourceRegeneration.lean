import Foundation.RootRenewalWalkMarginal
import Foundation.IndependentCoordinateBlocks

/-! Genuine finite-past/infinite-future splitting of the actual root-mark source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RootMarkSourceRegeneration
open MarkedRootRenewalProcess

def tail (n : ℕ) (η : MarkSample) : MarkSample := fun j => η (n+j)

theorem tail_measurable (n : ℕ) : Measurable (tail n) :=
  measurable_pi_iff.mpr (fun j => measurable_pi_apply (n+j))

theorem tail_preserving (n : ℕ) : MeasurePreserving (tail n) marks marks := by
  refine ⟨tail_measurable n, ?_⟩
  unfold marks tail
  exact Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Nat.add_left_cancel h)

theorem past_tail_independent (n : ℕ) :
    IndepFun (RootRenewalWalkMarginal.initialSegment n) (tail n) marks :=
  IndependentCoordinateBlocks.disjoint_families (fun j => measurable_pi_apply j) marks_independent
    (fun i : Fin n => i.val) (fun j : ℕ => n+j) (fun i j h => by omega)

theorem split_preserving (n : ℕ) :
    MeasurePreserving (fun η => (RootRenewalWalkMarginal.initialSegment n η,tail n η)) marks
      ((ComplexFourthRootWalk.probability n).prod marks) := by
  refine ⟨(RootRenewalWalkMarginal.prefix_measurable n).prodMk (tail_measurable n), ?_⟩
  rw [(past_tail_independent n).map_prod_eq_prod_map_map
    (RootRenewalWalkMarginal.prefix_measurable n).aemeasurable (tail_measurable n).aemeasurable,
    (RootRenewalWalkMarginal.prefix_preserving n).map_eq, (tail_preserving n).map_eq]

theorem position_add (a : ℝ) (n k : ℕ) (η : MarkSample) :
    position a (n+k) η = position a n η + position a k (tail n η) := by
  simp only [position, Finset.sum_range_add, tail]

theorem position_increment (a : ℝ) (n k : ℕ) (η : MarkSample) :
    position a (n+k) η-position a n η = position a k (tail n η) := by
  rw [position_add]
  abel

end OperatorDerivativeRewrite.Foundation.RootMarkSourceRegeneration
