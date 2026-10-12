import Foundation.WeightedL2Transport
import Foundation.AdjointUnitaryTransport

/-!
# Exact adjoints under a concrete squared-density change of integrand space

Multiplication by the measurable, almost-everywhere nonzero weight is the
constructed unitary. The partial operator is transported with its full domain,
and its adjoint value is actual division by the weight in weighted L².
This module does not assert a stochastic-integral realization of the input operator.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace OperatorDerivativeRewrite.Foundation.WeightedAdjointTransport

variable {Ω X : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  (μ : Measure Ω) (σ : Ω → ℝ) (hσ : Measurable σ)
  (hne : ∀ᵐ ω ∂μ, σ ω ≠ 0)

/-- Pull back an actual partial operator along multiplication by the weight. -/
def weightedOperator (T : Lp ℝ 2 μ →ₗ.[ℝ] X) :
    Lp ℝ 2 (WeightedL2Transport.weightedMeasure μ σ) →ₗ.[ℝ] X :=
  AdjointUnitaryTransport.pullback (WeightedL2Transport.unitary μ σ hσ hne) T

theorem weightedOperator_domain (T : Lp ℝ 2 μ →ₗ.[ℝ] X)
    (u : Lp ℝ 2 (WeightedL2Transport.weightedMeasure μ σ)) :
    u ∈ (weightedOperator μ σ hσ hne T).domain ↔
      WeightedL2Transport.unitary μ σ hσ hne u ∈ T.domain := Iff.rfl

theorem weightedOperator_dense_domain_iff (T : Lp ℝ 2 μ →ₗ.[ℝ] X) :
    Dense ((weightedOperator μ σ hσ hne T).domain :
      Set (Lp ℝ 2 (WeightedL2Transport.weightedMeasure μ σ))) ↔
      Dense (T.domain : Set (Lp ℝ 2 μ)) :=
  AdjointUnitaryTransport.pullback_dense_domain_iff _ T

theorem weightedOperator_isClosed_iff (T : Lp ℝ 2 μ →ₗ.[ℝ] X) :
    (weightedOperator μ σ hσ hne T).IsClosed ↔ T.IsClosed :=
  AdjointUnitaryTransport.pullback_isClosed_iff _ T

/-- Full domain equality, not merely an inclusion on test functions. -/
theorem weightedOperator_adjoint_domain (T : Lp ℝ 2 μ →ₗ.[ℝ] X)
    (hT : Dense (T.domain : Set (Lp ℝ 2 μ))) :
    (weightedOperator μ σ hσ hne T).adjoint.domain = T.adjoint.domain :=
  AdjointUnitaryTransport.pullback_adjoint_domain _ T hT

/-- Equality of actual partial adjoints, with no reciprocal-moment assumption. -/
theorem weightedOperator_adjoint_eq (T : Lp ℝ 2 μ →ₗ.[ℝ] X)
    (hT : Dense (T.domain : Set (Lp ℝ 2 μ))) :
    (weightedOperator μ σ hσ hne T).adjoint =
      (WeightedL2Transport.unitary μ σ hσ hne).symm.toLinearEquiv.toLinearMap.compPMap
        T.adjoint :=
  AdjointUnitaryTransport.pullback_adjoint_eq _ T hT

/-- The inverse-unitary value is the genuine weighted-L² class of `(T*F)/σ`. -/
theorem weightedOperator_adjoint_coeFn (T : Lp ℝ 2 μ →ₗ.[ℝ] X)
    (hT : Dense (T.domain : Set (Lp ℝ 2 μ))) (F : T.adjoint.domain) :
    (weightedOperator μ σ hσ hne T).adjoint ⟨(F : X), by
      rw [weightedOperator_adjoint_domain μ σ hσ hne T hT]
      exact F.property⟩
      =ᵐ[WeightedL2Transport.weightedMeasure μ σ]
        fun ω => T.adjoint F ω / σ ω := by
  change (AdjointUnitaryTransport.pullback
    (WeightedL2Transport.unitary μ σ hσ hne) T).adjoint ⟨(F : X), _⟩ =ᵐ[_] _
  erw [AdjointUnitaryTransport.pullback_adjoint_apply _ T hT (F : X) _ F.property]
  exact WeightedL2Transport.unitary_symm_coeFn μ σ hσ hne _

end OperatorDerivativeRewrite.Foundation.WeightedAdjointTransport
