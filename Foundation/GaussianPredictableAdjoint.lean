import Foundation.GaussianContinuousRigidity
import Foundation.HilbertRepresentation

/-! The concrete bounded predictable adjoint and its exact relation to the full
closed Gaussian derivative. Surjectivity onto centered L2 is not assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianPredictableAdjoint
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianProductDerivative
open GaussianPredictableFull GaussianPredictableL2Completion GaussianTimeDivergence
open GaussianContinuousRigidity GaussianSensitivityCore
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

def predictableField : fullPredictable →ₗᵢ[ℝ] GaussianVectorL2 :=
  fieldEmbedding.comp fullPredictable.subtypeₗᵢ

/-- The actual bounded adjoint on all scalar Gaussian L2. -/
def predictableAdjoint : GaussianL2 →L[ℝ] fullPredictable :=
  itoIntegral.toContinuousLinearMap.adjoint

/-- Pull back the orthogonal projection onto the embedded predictable field subspace. -/
def predictableProjection : GaussianVectorL2 →L[ℝ] fullPredictable :=
  predictableField.toContinuousLinearMap.adjoint

def divergenceMap : TimeProbabilityL2 →L[ℝ] (GaussianVectorL2 × GaussianL2) :=
  fieldEmbedding.toContinuousLinearMap.prod integralExtension

/-- Agreement for every genuinely predictable L2 field, without a Malliavin hypothesis. -/
theorem predictableField_divergence_graph (u : fullPredictable) :
    (predictableField u, itoIntegral u) ∈ hilbertDivergence.graph := by
  have h : closedProductSteps ≤ hilbertDivergence.graph.comap divergenceMap.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rw [productStepSpan, Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro z ⟨n, r, p, s, t, hrs, hst, rfl⟩
      change (fieldEmbedding (GaussianTimeProductL2.productTensor (intervalVector s t)
        (pastCoefficient r p)), integralExtension (pastStep s t r hrs p)) ∈ hilbertDivergence.graph
      rw [fieldEmbedding_tensor, integralExtension_eq, ito_pastStep s t hst]
      exact pastCoefficient_hilbertDivergence_graph r p s t hrs hst
    · exact hilbertDivergence_isClosed.preimage divergenceMap.continuous
  have hu : (u : TimeProbabilityL2) ∈ closedProductSteps := by
    rw [closedProductSteps_eq_fullPredictable]
    exact u.property
  have hg := h hu
  change (fieldEmbedding u, integralExtension u) ∈ hilbertDivergence.graph at hg
  rw [integralExtension_eq] at hg
  exact hg

/-- On the actual full derivative domain, the bounded adjoint is its predictable projection. -/
theorem predictableAdjoint_eq_projected_derivative
    (F : closedCylindricalDerivative.domain) :
    predictableAdjoint (F : GaussianL2) =
      predictableProjection (closedCylindricalDerivative F) := by
  apply ext_inner_right ℝ
  intro u
  change inner ℝ (itoIntegral.toContinuousLinearMap.adjoint (F : GaussianL2)) u =
    inner ℝ (predictableField.toContinuousLinearMap.adjoint (closedCylindricalDerivative F)) u
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  obtain ⟨v, hv, hδ⟩ := hilbertDivergence.mem_graph_iff.mp (predictableField_divergence_graph u)
  have hp := (closedCylindricalDerivative.adjoint_isFormalAdjoint
    closedCylindricalDerivative_dense_domain).symm F v
  change inner ℝ (closedCylindricalDerivative F) (v : GaussianVectorL2) =
    inner ℝ (F : GaussianL2) (hilbertDivergence v) at hp
  rw [hv, hδ] at hp
  exact hp.symm

theorem predictableAdjoint_integral (u : fullPredictable) :
    predictableAdjoint (itoIntegral u) = u :=
  congrArg (fun L : fullPredictable →L[ℝ] fullPredictable => L u) itoIntegral.adjoint_comp_self

/-- GKW orthogonal decomposition on the whole ambient Gaussian L2, without a PRP claim. -/
theorem representation_residual_orthogonal (F : GaussianL2) :
    F - itoIntegral (predictableAdjoint F) ∈ itoIntegral.toLinearMap.rangeᗮ :=
  HilbertRepresentation.representation_residual_orthogonal itoIntegral F

theorem representation_norm_decomposition (F : GaussianL2) :
    ‖F‖ ^ 2 = ‖predictableAdjoint F‖ ^ 2 +
      ‖F - itoIntegral (predictableAdjoint F)‖ ^ 2 :=
  HilbertRepresentation.representation_norm_decomposition itoIntegral F

end OperatorDerivativeRewrite.Foundation.GaussianPredictableAdjoint
