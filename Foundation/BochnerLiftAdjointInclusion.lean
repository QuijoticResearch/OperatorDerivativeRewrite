import Foundation.BochnerClosedOperator
import Foundation.OperatorDomains

/-! Actual fiberwise integration by parts implies a native Hilbert-adjoint
inclusion. No equality of the two full adjoint domains is presumed. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.BochnerLiftAdjointInclusion
variable {X E F : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem lift_formal (T : E →ₗ.[ℝ] F) (S : F →ₗ.[ℝ] E)
    (h : T.IsFormalAdjoint S) :
    (BochnerClosedOperator.lift μ T).IsFormalAdjoint (BochnerClosedOperator.lift μ S) := by
  intro u v
  rw [L2_inner_eq_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [BochnerClosedOperator.lift_value_ae μ T u,
    BochnerClosedOperator.lift_value_ae μ S v] with x hu hv
  have htu := LinearPMap.mem_domain_of_mem_graph hu
  have hsv := LinearPMap.mem_domain_of_mem_graph hv
  rw [(T.image_iff htu).mpr hu, (S.image_iff hsv).mpr hv]
  exact h ⟨_, htu⟩ ⟨_, hsv⟩

omit [CompleteSpace F] in
theorem lift_adjoint_le (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E)) :
    BochnerClosedOperator.lift μ T.adjoint ≤ (BochnerClosedOperator.lift μ T).adjoint :=
  (lift_formal μ T T.adjoint (T.adjoint_isFormalAdjoint hd).symm).le_adjoint
    (BochnerClosedOperator.lift_dense_domain μ T hd)

end OperatorDerivativeRewrite.Foundation.BochnerLiftAdjointInclusion
