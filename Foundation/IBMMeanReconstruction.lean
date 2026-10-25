import Foundation.IBMInitialGermTriviality
import Foundation.IBMCompletedNativeCalculus
import Foundation.IBMCompletedCoordinates

/-! Mean-centered reconstruction by the existing fixed completed stochastic family.
This is a Hilbert-space signed-covariance completion of actual predictable integrals.
It does not identify that family with a physical source or clock driver. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.IBMMeanReconstruction
open MeasureTheory
open IBMTimeAveragedObservable IBMMultichannelCompletion IBMFixedStochasticFamily
attribute [local instance] componentAdd componentGroup componentModule componentZeroDec
local instance : DecidableEq basisSet := Classical.decEq _
attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative

theorem completed_mean_reconstruction (f : IntrinsicSpace) :
    completedIntegral fixedFamily
      ((completedIntegral fixedFamily).toContinuousLinearMap.adjoint (f : JointL2)) =
        (f : JointL2) - (∫ ω, (f : JointL2) ω ∂IBMSourceLaws.jointMeasure) • IBMGlobalVacuum.one := by
  rw [IBMCompletedNativeCalculus.fixed_weak_reconstruction,
    IBMObservedTerminalMartingale.channelClass,
    IBMInitialGermTriviality.initial_projection_expectation]

theorem completed_native_mean_reconstruction
    (f : IBMJointIntrinsicDerivative.jointDerivative.domain) :
    completedIntegral fixedFamily
      ((IBMCompletedNativeCalculus.transfer fixedFamily).adjoint
        (IBMJointIntrinsicDerivative.jointDerivative f)) = ((f : IntrinsicSpace) : JointL2) -
          (∫ ω, ((f : IntrinsicSpace) : JointL2) ω ∂IBMSourceLaws.jointMeasure) •
            IBMGlobalVacuum.one := by
  rw [IBMCompletedNativeCalculus.fixed_native_reconstruction,
    IBMObservedTerminalMartingale.channelClass,
    IBMInitialGermTriviality.initial_projection_expectation]

theorem completed_actual_series (f : IntrinsicSpace) :
    let z := (completedIntegral fixedFamily).toContinuousLinearMap.adjoint (f : JointL2)
    HasSum (fun i : basisSet => IBMFullPredictableIntegral.integral (fixedFamily i)
      (IBMCompletedCoordinates.coordinates z i))
      ((f : JointL2) -
        (∫ ω, (f : JointL2) ω ∂IBMSourceLaws.jointMeasure) • IBMGlobalVacuum.one) := by
  dsimp only
  have h := IBMCompletedCoordinates.coordinates_actual_sum
    ((completedIntegral fixedFamily).toContinuousLinearMap.adjoint (f : JointL2))
  rw [completed_mean_reconstruction] at h
  exact h

end OperatorDerivativeRewrite.Foundation.IBMMeanReconstruction
