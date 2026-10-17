import Foundation.SU2BoundaryJointLaw
import Foundation.ConditionalResamplingKernel

/-! A concrete invariant and idempotent heat-bath update for the finite-word SU(2) interaction. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.SU2ConditionalHeatBath
open QuaternionSU2Representation SU2BoundaryJointLaw
variable {ι κ : Type*}
variable (ν : Measure SU2) [IsProbabilityMeasure ν]

def update (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    Kernel ((ι → SU2) × SU2) ((ι → SU2) × SU2) := by
  let _ := SU2BoundaryWordKernel.kernel_markov ν s w β
  exact ConditionalResamplingKernel.update (SU2BoundaryWordKernel.kernel ν s w β)

theorem update_markov (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    IsMarkovKernel (update ν s w β) := by
  let _ := SU2BoundaryWordKernel.kernel_markov ν s w β
  exact ConditionalResamplingKernel.update_markov _

theorem update_idempotent (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    update ν s w β ∘ₖ update ν s w β = update ν s w β := by
  let _ := SU2BoundaryWordKernel.kernel_markov ν s w β
  exact ConditionalResamplingKernel.update_idempotent _

theorem boundary_preserved (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ)
    (J : Measure ((ι → SU2) × SU2)) [SFinite J] :
    (update ν s w β ∘ₘ J).fst = J.fst := by
  let _ := SU2BoundaryWordKernel.kernel_markov ν s w β
  exact ConditionalResamplingKernel.boundary_preserved _ J

variable (ρ : Measure (ι → SU2)) [IsProbabilityMeasure ρ]

theorem joint_invariant (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ) :
    update ν s w β ∘ₘ joint ρ ν s w β = joint ρ ν s w β := by
  let _ := SU2BoundaryWordKernel.kernel_markov ν s w β
  let _ := joint_probability ρ ν s w β
  let _ := conditional_kernel ρ ν s w β
  exact ConditionalResamplingKernel.invariant _ _

theorem concrete_invariant [Fintype ι] (s : Finset κ)
    (w : κ → List (ι × Bool)) (β : ℝ) :
    update law s w β ∘ₘ joint finiteBoundaryHaar law s w β =
      joint finiteBoundaryHaar law s w β :=
  joint_invariant law finiteBoundaryHaar s w β

end OperatorDerivativeRewrite.Foundation.SU2ConditionalHeatBath
