import Foundation.IBMConditionalObservable

/-! Orthogonal geometry of the conditional IBM observable L² space. -/
noncomputable section
open MeasureTheory
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.IBMConditionalProjectionGeometry
open IBMConditionalObservable IBMSourceLaws InfiniteGaussian

variable (X : SampleSpace → C(ℝ, ℝ)) (Y : SampleSpace → C(ℝ≥0, ℝ))
variable (hX : Measurable X) (hY : Measurable Y)

/-- Observable L² functions are fixed by conditional expectation. -/
theorem observableProjection_fixed (f : observableSpace X Y) :
    observableProjection X Y hX hY (f : Lp ℝ 2 jointMeasure) = f := by
  haveI : Fact (observableSigma X Y ≤ (inferInstance : MeasurableSpace JointSample)) :=
    ⟨observableSigma_le X Y hX hY⟩
  letI : CompleteSpace (observableSpace X Y) := by
    change CompleteSpace (lpMeas ℝ ℝ (observableSigma X Y) 2 jointMeasure)
    infer_instance
  change (observableSpace X Y).orthogonalProjectionOnto (f : Lp ℝ 2 jointMeasure) = f
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self f

/-- Conditional projection preserves the inner product against every
observable test function. -/
theorem observableProjection_pairing
    (f : Lp ℝ 2 jointMeasure) (g : observableSpace X Y) :
    inner ℝ ((observableProjection X Y hX hY f : observableSpace X Y) : Lp ℝ 2 jointMeasure)
      (g : Lp ℝ 2 jointMeasure) = inner ℝ f (g : Lp ℝ 2 jointMeasure) := by
  haveI : Fact (observableSigma X Y ≤ (inferInstance : MeasurableSpace JointSample)) :=
    ⟨observableSigma_le X Y hX hY⟩
  letI : CompleteSpace (observableSpace X Y) := by
    change CompleteSpace (lpMeas ℝ ℝ (observableSigma X Y) 2 jointMeasure)
    infer_instance
  change inner ℝ (((observableSpace X Y).orthogonalProjectionOnto f : observableSpace X Y) :
    Lp ℝ 2 jointMeasure) (g : Lp ℝ 2 jointMeasure) = inner ℝ f (g : Lp ℝ 2 jointMeasure)
  exact (observableSpace X Y).inner_orthogonalProjectionOnto_eq_of_mem_right g f

end OperatorDerivativeRewrite.Foundation.IBMConditionalProjectionGeometry
