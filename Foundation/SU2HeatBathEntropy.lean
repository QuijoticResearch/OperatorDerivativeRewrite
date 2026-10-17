import Foundation.SU2ConditionalHeatBath
import Foundation.ConditionalResamplingEntropy

/-! Entropy accounting for the actual finite-word SU(2) heat bath.
The reference in `actual_joint_entropy_after_update` is the globally normalized
interaction law. The binary-reference counterexample uses the same genuine
conditional kernel, but a separately specified boundary probability law. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
namespace OperatorDerivativeRewrite.Foundation.SU2HeatBathEntropy
open QuaternionSU2Representation SU2BoundaryJointLaw
open ConditionalResamplingEntropy
variable {ι κ : Type*}
variable (ν : Measure SU2) [IsProbabilityMeasure ν]
variable (ρ : Measure (ι → SU2)) [IsProbabilityMeasure ρ]

theorem actual_joint_entropy_after_update (s : Finset κ) (w : κ → List (ι × Bool))
    (β : ℝ) (J : Measure ((ι → SU2) × SU2)) [IsFiniteMeasure J] :
    klDiv (SU2ConditionalHeatBath.update ν s w β ∘ₘ J) (joint ρ ν s w β) =
      klDiv J.fst (boundary ρ ν s w β) := by
  let _ := SU2BoundaryWordKernel.kernel_markov ν s w β
  let _ := boundary_probability ρ ν s w β
  rw [factorization]
  exact entropy_after_update (SU2BoundaryWordKernel.kernel ν s w β) J _

theorem actual_joint_entropy_decomposition (s : Finset κ) (w : κ → List (ι × Bool))
    (β : ℝ) (π : Measure (ι → SU2)) [IsFiniteMeasure π]
    (L : Kernel (ι → SU2) SU2) [IsMarkovKernel L] :
    klDiv (π ⊗ₘ L) (joint ρ ν s w β) =
      klDiv (SU2ConditionalHeatBath.update ν s w β ∘ₘ (π ⊗ₘ L)) (joint ρ ν s w β) +
      klDiv (π ⊗ₘ L) (π ⊗ₘ SU2BoundaryWordKernel.kernel ν s w β) := by
  let _ := SU2BoundaryWordKernel.kernel_markov ν s w β
  let _ := boundary_probability ρ ν s w β
  rw [factorization]
  exact entropy_decomposition (SU2BoundaryWordKernel.kernel ν s w β) π _ L

theorem binary_boundary_obstruction [Finite ι]
    (s : Finset κ) (w : κ → List (ι × Bool)) (β : ℝ)
    (a b : ι → SU2) (hab : a ≠ b) (q : ℝ) (hq : q < 1) :
    ¬ (klDiv (SU2ConditionalHeatBath.update ν s w β ∘ₘ
      (Measure.dirac a ⊗ₘ SU2BoundaryWordKernel.kernel ν s w β))
      (binaryReference a b ⊗ₘ SU2BoundaryWordKernel.kernel ν s w β)).toReal ≤
      q * (klDiv (Measure.dirac a ⊗ₘ SU2BoundaryWordKernel.kernel ν s w β)
        (binaryReference a b ⊗ₘ SU2BoundaryWordKernel.kernel ν s w β)).toReal := by
  let _ := SU2BoundaryWordKernel.kernel_markov ν s w β
  exact binary_no_strict_contraction (SU2BoundaryWordKernel.kernel ν s w β) a b hab q hq

def opposite : SU2 :=
  ⟨SU2TraceHessianModel.rotation Real.pi, SU2ExponentialMembership.rotation_mem _⟩

theorem one_ne_opposite : (1 : SU2) ≠ opposite := by
  intro h
  have hh := congrArg (fun A : SU2 => ((A : SU2TraceHessianModel.M2) 0 0).re) h
  norm_num [opposite, SU2TraceHessianModel.rotation, Matrix.one_apply] at hh

/-- The actual Haar-based heat bath, with two explicit distinct boundary configurations.
The reference law is the binary boundary law composed with that heat bath. -/
theorem concrete_haar_obstruction (s : Finset κ) (w : κ → List (Unit × Bool))
    (β q : ℝ) (hq : q < 1) :
    ¬ (klDiv (SU2ConditionalHeatBath.update law s w β ∘ₘ
      (Measure.dirac (fun _ : Unit => (1 : SU2)) ⊗ₘ SU2BoundaryWordKernel.kernel law s w β))
      (binaryReference (fun _ : Unit => (1 : SU2)) (fun _ : Unit => opposite) ⊗ₘ
        SU2BoundaryWordKernel.kernel law s w β)).toReal ≤
      q * (klDiv
        (Measure.dirac (fun _ : Unit => (1 : SU2)) ⊗ₘ SU2BoundaryWordKernel.kernel law s w β)
        (binaryReference (fun _ : Unit => (1 : SU2)) (fun _ : Unit => opposite) ⊗ₘ
          SU2BoundaryWordKernel.kernel law s w β)).toReal := by
  apply binary_boundary_obstruction law s w β _ _ _ q hq
  intro h
  exact one_ne_opposite (congrFun h ())

end OperatorDerivativeRewrite.Foundation.SU2HeatBathEntropy
