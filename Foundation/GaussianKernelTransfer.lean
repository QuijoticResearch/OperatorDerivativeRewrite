import Foundation.GaussianDeterministicIntegral
import Foundation.GaussianPastStepCompletion

/-! Covariance transfer through an actual bounded time-kernel map.
The bounded adjoint here acts on deterministic parameter spaces and is NOT
the unbounded Malliavin derivative or a fractional predictable projection. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianKernelTransfer
open InfiniteGaussian GaussianTimeHilbert GaussianHilbertProcess
open GaussianTimeProductL2 GaussianContinuousRigidity GaussianDeterministicIntegral
attribute [local instance] timeHilbert_secondCountable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- An arbitrary actual bounded kernel map; neither injectivity nor surjectivity is assumed. -/
def realization (K : E →L[ℝ] TimeHilbert) : E →L[ℝ] GaussianL2 :=
  (isonormalEmbedding TimeHilbert).toContinuousLinearMap.comp K

def covarianceOperator (K : E →L[ℝ] TimeHilbert) : E →L[ℝ] E := K.adjoint.comp K

omit [CompleteSpace E] in
theorem realization_inner (K : E →L[ℝ] TimeHilbert) (x y : E) :
    inner ℝ (realization K x) (realization K y) = inner ℝ (K x) (K y) :=
  (isonormalEmbedding TimeHilbert).inner_map_map _ _

omit [CompleteSpace E] in
theorem realization_norm (K : E →L[ℝ] TimeHilbert) (x : E) :
    ‖realization K x‖ = ‖K x‖ := (isonormalEmbedding TimeHilbert).norm_map _

omit [CompleteSpace E] in
theorem realization_zero_iff (K : E →L[ℝ] TimeHilbert) (x : E) :
    realization K x = 0 ↔ K x = 0 := by
  rw [← norm_eq_zero, realization_norm, norm_eq_zero]

omit [CompleteSpace E] in
theorem realization_product_integrable (K : E →L[ℝ] TimeHilbert) (x y : E) :
    Integrable (fun ω => realization K x ω * realization K y ω) gaussianProduct :=
  mul_L2_integrable (Lp.memLp _) (Lp.memLp _)

omit [CompleteSpace E] in
theorem realization_centered (K : E →L[ℝ] TimeHilbert) (x : E) :
    ∫ ω, realization K x ω ∂gaussianProduct = 0 := isonormal_integral (K x)

theorem realization_covariance (K : E →L[ℝ] TimeHilbert) (x y : E) :
    cov[realization K x, realization K y; gaussianProduct] =
      inner ℝ x (covarianceOperator K y) := by
  rw [show cov[realization K x, realization K y; gaussianProduct] =
      inner ℝ (K x) (K y) from isonormal_covariance (K x) (K y)]
  exact (K.adjoint_inner_right x (K y)).symm

theorem realization_normal (K : E →L[ℝ] TimeHilbert) :
    (realization K).adjoint.comp (realization K) = covarianceOperator K := by
  ext x
  apply ext_inner_left ℝ
  intro y
  change inner ℝ y ((realization K).adjoint (realization K x)) =
    inner ℝ y (K.adjoint (K x))
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    realization_inner]

theorem covariance_energy (K : E →L[ℝ] TimeHilbert) (x : E) :
    inner ℝ x (covarianceOperator K x) = ‖K x‖ ^ 2 := by
  rw [covarianceOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

theorem covariance_zero_iff (K : E →L[ℝ] TimeHilbert) (x : E) :
    covarianceOperator K x = 0 ↔ K x = 0 := by
  constructor
  · intro hx
    have he := covariance_energy K x
    rw [hx, inner_zero_right] at he
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (K x)])
  · intro hx
    simp [covarianceOperator, hx]

omit [CompleteSpace E] in
/-- Genuine graph membership and the actual source derivative value. No
new derivative is defined by prescribing this output. -/
theorem realization_derivative (K : E →L[ℝ] TimeHilbert) (x : E) :
    (realization K x, fieldEmbedding (productTensor (K x) gaussianOne)) ∈
      closedCylindricalDerivative.graph := firstChaos_closedDerivative_graph (K x)

end OperatorDerivativeRewrite.Foundation.GaussianKernelTransfer
