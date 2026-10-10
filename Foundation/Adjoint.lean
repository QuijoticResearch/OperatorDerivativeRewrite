import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # Operator-adjoint foundation

Extracted from the `UnboundedFoundation` section of `OperatorDerivative.lean`.
The operator derivative is the Hilbert-space adjoint on its natural domain.
Dense domain is required for the adjoint identity and closedness; no stochastic
process, multiplication, chain rule, or closability assumption is used here.
-/

noncomputable section

namespace OperatorDerivativeRewrite.Foundation

variable {L2Ω : Type*} {L2ΩH : Type*}
  [NormedAddCommGroup L2Ω] [InnerProductSpace ℝ L2Ω] [CompleteSpace L2Ω]
  [NormedAddCommGroup L2ΩH] [InnerProductSpace ℝ L2ΩH] [CompleteSpace L2ΩH]

/-- The operator derivative as a partially defined Hilbert-space adjoint. -/
def operatorDerivative (δ_unbdd : L2ΩH →ₗ.[ℝ] L2Ω) : L2Ω →ₗ.[ℝ] L2ΩH :=
  δ_unbdd.adjoint

/-- The adjoint of a densely defined operator is closed. -/
theorem operatorDerivative_isClosed (δ_unbdd : L2ΩH →ₗ.[ℝ] L2Ω)
    (hDense : Dense (δ_unbdd.domain : Set L2ΩH)) :
    (operatorDerivative δ_unbdd).IsClosed :=
  δ_unbdd.adjoint_isClosed hDense

/-- Adjointness, with both arguments explicitly restricted to their domains. -/
theorem operatorDerivative_adjoint_identity (δ_unbdd : L2ΩH →ₗ.[ℝ] L2Ω)
    (hDense : Dense (δ_unbdd.domain : Set L2ΩH))
    (F : δ_unbdd.adjoint.domain) (u : δ_unbdd.domain) :
    @inner ℝ L2ΩH _ (δ_unbdd.adjoint F) u = @inner ℝ L2Ω _ F (δ_unbdd u) :=
  δ_unbdd.adjoint_isFormalAdjoint hDense F u

end OperatorDerivativeRewrite.Foundation
