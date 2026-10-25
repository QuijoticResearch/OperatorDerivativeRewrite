import Foundation.IBMFourierClockClarkOcone
import Foundation.IBMCenteredSourceRepresentation
import Foundation.IBMNativeClockDirection

/-! Actual multitime IBM observables: original source-adjoint recovery plus
the genuine predictable Brownian-clock integral of the source mean. This is a
hybrid representation, not an observed-IBM-filtration Clark--Ocone theorem. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFourierHybridReconstruction
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMFiniteAverageCore
open IBMNativeSourceRecovery IBMGlobalVacuum IBMJointIntrinsicDerivative
open IBMClockConditionalCorrection IBMNativeClockDirection IBMFourierClockClarkOcone
open GaussianPredictableFull GaussianPredictableAdjoint
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

variable {ι : Type*} [Fintype ι] (a : ℕ → ι → ℝ) (β w : ℕ → ℝ)

theorem source_vacuum (r : ι → ℝ≥0) :
    sourceVacuum (IBMFourierCylinderSeries.observation a r β w : JointL2) =
      clockLift (IBMFourierSourceMeanCalculus.clockMean a β w r) := by
  let f : JointL2 := IBMFourierCylinderSeries.observation a r β w
  have hc : clockUnitary (sourceVacuum f) =
      BochnerClosedOperator.tensor gaussianProduct gaussianOne
        (IBMFourierSourceMeanCalculus.clockMean a β w r) := by
    rw [clock_source_flip]
    change ProductL2Curry.flip gaussianProduct gaussianProduct
      (sourceUnitary (sourceUnitary.symm _)) = _
    rw [sourceUnitary.apply_symm_apply, factor_vacuum_tensor, ProductL2Curry.flip_tensor]
    rfl
  exact (clockUnitary.symm_apply_apply (sourceVacuum f)).symm.trans
    ((congrArg clockUnitary.symm hc).trans (inverse_clock_tensor _))

theorem clockMean_expectation (r : ι → ℝ≥0) :
    (∫ Y, IBMFourierSourceMeanCalculus.clockMean a β w r Y ∂gaussianProduct) =
      ∫ ω, (IBMFourierCylinderSeries.observation a r β w : JointL2) ω
        ∂IBMSourceLaws.jointMeasure := by
  have h := sourceUnitary.inner_map_map one
    (IBMFourierCylinderSeries.observation a r β w : JointL2)
  rw [source_one, tensor_pairing] at h
  change inner ℝ gaussianOne (IBMFourierSourceMeanCalculus.clockMean a β w r) =
    inner ℝ one (IBMFourierCylinderSeries.observation a r β w : JointL2) at h
  rwa [gaussianOne_inner_eq_integral, one_inner_mean] at h

def clockField (r : ι → ℝ≥0) : FieldSpace :=
  BochnerClosedOperator.tensor gaussianProduct gaussianOne
    (predictableField (coefficient a β w r))

theorem partial_graph (r : ι → ℝ≥0) :
    (clockField a β w r, BochnerClosedOperator.tensor gaussianProduct gaussianOne
      (itoIntegral (coefficient a β w r))) ∈ partialDerivative.adjoint.graph :=
  LinearPMap.le_graph_of_le
    (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct closedCylindricalDerivative
      closedCylindricalDerivative_dense_domain)
    (BochnerClosedOperator.tensor_graph gaussianProduct hilbertDivergence gaussianOne _ _
      (predictableField_divergence_graph (coefficient a β w r)))

theorem clock_mem (r : ι → ℝ≥0) : clockField a β w r ∈ clockDerivative.adjoint.domain := by
  rw [clock_adjoint_domain]
  exact LinearPMap.mem_domain_of_mem_graph (partial_graph a β w r)

theorem clock_value (r : ι → ℝ≥0) (hv : Summable (fun k => |w k|)) :
    clockDerivative.adjoint ⟨clockField a β w r, clock_mem a β w r⟩ =
      clockLift (IBMFourierSourceMeanCalculus.clockMean a β w r -
        (∫ Y, IBMFourierSourceMeanCalculus.clockMean a β w r Y ∂gaussianProduct) •
          gaussianOne) := by
  have hp := LinearPMap.mem_domain_of_mem_graph (partial_graph a β w r)
  rw [clock_adjoint_apply _ (clock_mem a β w r) hp,
    ((partialDerivative.adjoint.image_iff hp).mpr (partial_graph a β w r)).symm,
    inverse_clock_tensor, stochastic_reconstruction a β w r hv]

def integrand (r : ι → ℝ≥0) : JointFieldSpace :=
  pairField (sourceRecovery (IBMFourierCylinderSeries.observation a r β w : JointL2))
    (clockField a β w r)

theorem reconstruction (r : ι → ℝ≥0) (hv : Summable (fun k => |w k|)) :
    ∃ hi : integrand a β w r ∈ jointDivergence.domain,
      jointDivergence ⟨integrand a β w r, hi⟩ =
        IBMFourierCylinderSeries.observation a r β w -
          (∫ ω, (IBMFourierCylinderSeries.observation a r β w : JointL2) ω
            ∂IBMSourceLaws.jointMeasure) • IBMCenteredSourceRepresentation.intrinsicOne := by
  let f : JointL2 := IBMFourierCylinderSeries.observation a r β w
  let s : sourceDerivative.adjoint.domain :=
    ⟨sourceRecovery f, LinearPMap.mem_domain_of_mem_graph (source_recovery_graph f)⟩
  let c : clockDerivative.adjoint.domain := ⟨clockField a β w r, clock_mem a β w r⟩
  obtain ⟨hi, hvv⟩ := ambient_pair_divergence s c
  have hs : sourceDerivative.adjoint s = sourceCenter f :=
    ((sourceDerivative.adjoint.image_iff s.property).mpr (source_recovery_graph f)).symm
  have hc : clockDerivative.adjoint c = clockLift
      (IBMFourierSourceMeanCalculus.clockMean a β w r -
        (∫ Y, IBMFourierSourceMeanCalculus.clockMean a β w r Y ∂gaussianProduct) •
          gaussianOne) := clock_value a β w r hv
  have h1 : clockLift gaussianOne = one := by
    rw [← inverse_clock_tensor, ← clock_one, clockUnitary.symm_apply_apply]
  have hsum : sourceDerivative.adjoint s + clockDerivative.adjoint c =
      f - (∫ ω, f ω ∂IBMSourceLaws.jointMeasure) • one := by
    rw [hs, hc, source_center_split, source_vacuum a β w r, map_sub, map_smul, h1,
      clockMean_expectation a β w r]
    abel
  refine ⟨hi, hvv.trans ?_⟩
  rw [hsum, map_sub, map_smul]
  have hf := IntrinsicSpace.orthogonalProjectionOnto_mem_subspace_eq_self
    (IBMFourierCylinderSeries.observation a r β w)
  have ho := IntrinsicSpace.orthogonalProjectionOnto_mem_subspace_eq_self
    IBMCenteredSourceRepresentation.intrinsicOne
  change IntrinsicSpace.orthogonalProjectionOnto one = _ at ho
  rw [hf, ho]

theorem duality (r : ι → ℝ≥0) (hv : Summable (fun k => |w k|))
    (F : jointDerivative.domain) :
    inner ℝ (IBMFourierCylinderSeries.observation a r β w -
      (∫ ω, (IBMFourierCylinderSeries.observation a r β w : JointL2) ω
        ∂IBMSourceLaws.jointMeasure) • IBMCenteredSourceRepresentation.intrinsicOne)
      (F : IntrinsicSpace) = inner ℝ (integrand a β w r) (jointDerivative F) := by
  obtain ⟨hi, hvv⟩ := reconstruction a β w r hv
  have h := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense
    ⟨integrand a β w r, hi⟩ F
  rwa [hvv] at h

end OperatorDerivativeRewrite.Foundation.IBMFourierHybridReconstruction
