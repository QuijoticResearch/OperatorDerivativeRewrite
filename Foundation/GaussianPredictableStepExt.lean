import Foundation.GaussianConditionalIto

/-! Determination on the ENTIRE independently defined predictable L2 space
from actual past L2 step pairings, by the already verified polynomial-step density. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianPredictableStepExt
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianConditionalIto
open GaussianPredictableFull GaussianPredictableL2Completion GaussianTimePolynomialPairing

theorem ext (U V : fullPredictable)
    (h : ∀ (s t : ℝ≥0), s ≤ t → ∀ A : GaussianL2, A ∈ pastL2 s →
      inner ℝ (U : TimeProbabilityL2) (productTensor (intervalVector s t) A) =
        inner ℝ (V : TimeProbabilityL2) (productTensor (intervalVector s t) A)) : U = V := by
  let Z : TimeProbabilityL2 := (U : TimeProbabilityL2)-(V : TimeProbabilityL2)
  let B : TimeProbabilityL2 →L[ℝ] ℝ := innerSL ℝ Z
  have hc : closedProductSteps ≤ B.ker := by
    apply Submodule.topologicalClosure_minimal
    · change transportRelation.map (LinearMap.fst ℝ TimeProbabilityL2 GaussianVectorL2) ≤ B.ker
      rw [Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro z ⟨n,r,p,s,t,hrs,hst,rfl⟩
      change inner ℝ Z (productTensor (intervalVector s t)
        (GaussianTimeDivergence.pastCoefficient r p)) = 0
      rw [show Z = (U : TimeProbabilityL2)-(V : TimeProbabilityL2) from rfl, inner_sub_left]
      exact sub_eq_zero.mpr (h s t hst _
        (GaussianPastStepCompletion.past_polynomial_measurable s r hrs p))
    · exact B.isClosed_ker
  have hz : Z ∈ closedProductSteps := by
    rw [closedProductSteps_eq_fullPredictable]
    exact fullPredictable.sub_mem U.property V.property
  have he := hc hz
  change inner ℝ Z Z = 0 at he
  have hzero := inner_self_eq_zero.mp he
  exact Subtype.ext (sub_eq_zero.mp hzero)

end OperatorDerivativeRewrite.Foundation.GaussianPredictableStepExt
