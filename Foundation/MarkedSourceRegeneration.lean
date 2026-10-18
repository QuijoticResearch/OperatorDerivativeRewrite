import Foundation.FiniteMarkedRenewalMarginals
import Foundation.IndependentCoordinateBlocks

/-! General independent finite-past / infinite-tail splitting for actual mark sources. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.MarkedSourceRegeneration
open MarkedRenewalRealization FiniteMarkedRenewalMarginals
variable {A : Type*} [MeasurableSpace A]

def tail (n : ℕ) (η : MarkSample A) : MarkSample A := fun j => η (n+j)

theorem tail_measurable (n : ℕ) : Measurable (tail (A := A) n) :=
  measurable_pi_iff.mpr (fun j => measurable_pi_apply (n+j))

theorem tail_preserving (μ : Measure A) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (tail n) (marks μ) (marks μ) := by
  refine ⟨tail_measurable n,?_⟩
  unfold marks tail
  exact Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Nat.add_left_cancel h)

theorem past_tail_independent (μ : Measure A) [IsProbabilityMeasure μ] (n : ℕ) :
    IndepFun (initialSegment n) (tail n) (marks μ) :=
  IndependentCoordinateBlocks.disjoint_families (fun j => measurable_pi_apply j) (marks_independent μ)
    (fun i : Fin n => i.val) (fun j : ℕ => n+j) (fun i j h => by omega)

theorem split_preserving (μ : Measure A) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (fun η => (initialSegment n η,tail n η)) (marks μ)
      ((finiteProbability μ n).prod (marks μ)) := by
  refine ⟨(prefix_measurable n).prodMk (tail_measurable n),?_⟩
  rw [(past_tail_independent μ n).map_prod_eq_prod_map_map
    (prefix_measurable n).aemeasurable (tail_measurable n).aemeasurable,
    (prefix_preserving μ n).map_eq,(tail_preserving μ n).map_eq]

theorem position_add (z : A → ℂ) (n k : ℕ) (η : MarkSample A) :
    position z (n+k) η = position z n η+position z k (tail n η) := by
  simp only [position,Finset.sum_range_add,tail]

theorem position_increment (z : A → ℂ) (n k : ℕ) (η : MarkSample A) :
    position z (n+k) η-position z n η = position z k (tail n η) := by
  rw [position_add]
  abel

end OperatorDerivativeRewrite.Foundation.MarkedSourceRegeneration
