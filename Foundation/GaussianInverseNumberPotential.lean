import Foundation.GaussianQuadraticSourceHodge
import Foundation.GaussianConditionalGraph
import Foundation.GaussianOneObservationRecoveryCompactness

/-! The bounded inverse-number potential constructed from actual divergence recovery. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianInverseNumberPotential
open InfiniteGaussian GaussianNumberSectors GaussianDivergenceRecovery GaussianSourceHodge
open GaussianQuadraticSourceHodge GaussianConditionalGraph

def potentialOperator : GaussianL2 →L[ℝ] GaussianL2 :=
  recoveryOperator.adjoint.comp recoveryOperator

theorem projection_zero_positive (n : ℕ) (hn : n ≠ 0) (f : GaussianL2) :
    projection 0 (projection n f)=0 := by
  apply (sector 0).eq_starProjection_of_mem_of_inner_eq_zero (sector 0).zero_mem
  intro w hw
  rw [sub_zero]
  exact sectors_orthogonal hn ⟨_,projection_mem n f⟩ ⟨w,hw⟩

theorem adjoint_inverseGradient (f : GaussianL2) (n : ℕ) :
    recoveryOperator.adjoint ((inverseGradientComponent f n : (gradient n).range) : GaussianVectorL2)=
      (n : ℝ)⁻¹ • projection n f := by
  change recoveryOperator.adjoint ((n : ℝ)⁻¹ • projectedGradient n f)=_
  rw [map_smul,recovery_adjoint_derivative (projectedGradient_graph n f).1]
  by_cases hn : n=0
  · simp [hn]
  · rw [projection_zero_positive n hn,sub_zero]

theorem potential_hasSum (f : GaussianL2) :
    HasSum (fun n : ℕ => (n : ℝ)⁻¹ • projection n f) (potentialOperator f) := by
  have hs := (inverseGradient_summable f).hasSum.map
    recoveryOperator.adjoint.toAddMonoidHom recoveryOperator.adjoint.continuous
  change HasSum (fun n => recoveryOperator.adjoint
    ((inverseGradientComponent f n : (gradient n).range) : GaussianVectorL2))
    (recoveryOperator.adjoint (recovery f)) at hs
  simp only [adjoint_inverseGradient] at hs
  change HasSum (fun n : ℕ => (n : ℝ)⁻¹ • projection n f)
    (recoveryOperator.adjoint (recovery f))
  exact hs

theorem potential_derivative_graph (f : GaussianL2) :
    (potentialOperator f,recovery f)∈closedCylindricalDerivative.graph := by
  have hs := potential_gradient_graph (recovery f)
  have he : gradientProjection (recovery f)=recovery f :=
    gradientRange.starProjection_eq_self_iff.mpr (recovery_mem_gradientRange f)
  rw [he] at hs
  exact hs

theorem potential_number_graph (f : GaussianL2) :
    (potentialOperator f,recovery f)∈closedCylindricalDerivative.graph ∧
      (recovery f,f-projection 0 f)∈hilbertDivergence.graph :=
  ⟨potential_derivative_graph f,recovery_graph f⟩

theorem potential_conditional_commute {I : Type*} (h : I → CoefficientSpace) (f : GaussianL2) :
    potentialOperator (conditionalProjection h f)=conditionalProjection h (potentialOperator f) := by
  have hs := (potential_hasSum f).map (conditionalProjection h).toAddMonoidHom
    (conditionalProjection h).continuous
  change HasSum (fun n : ℕ => conditionalProjection h ((n : ℝ)⁻¹ • projection n f))
    (conditionalProjection h (potentialOperator f)) at hs
  simp only [map_smul,← projection_conditional_commute] at hs
  exact (potential_hasSum (conditionalProjection h f)).unique hs

theorem potential_preserves_generated {I : Type*} (h : I → CoefficientSpace)
    {f : GaussianL2} (hf : f∈generated h) : potentialOperator f∈generated h := by
  have he : conditionalProjection h f=f := (generated h).starProjection_eq_self_iff.mpr hf
  rw [← he,potential_conditional_commute]
  exact (generated h).starProjection_apply_mem _

theorem potential_positive (f : GaussianL2) :
    inner ℝ (potentialOperator f) f=‖recovery f‖^2 := by
  change inner ℝ (recoveryOperator.adjoint (recovery f)) f=_
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (recovery f) (recovery f)=_
  exact real_inner_self_eq_norm_sq _

theorem single_observation_potential_compact (u : CoefficientSpace) (hu : ‖u‖^2=1) :
    IsCompactOperator (potentialOperator.comp (conditionalProjection (fun _ : Unit => u))) := by
  change IsCompactOperator (recoveryOperator.adjoint.comp
    (recoveryOperator.comp (conditionalProjection (fun _ : Unit => u))))
  exact (GaussianOneObservationRecoveryCompactness.single_observation_recovery_compact u hu).clm_comp
    recoveryOperator.adjoint

end OperatorDerivativeRewrite.Foundation.GaussianInverseNumberPotential
