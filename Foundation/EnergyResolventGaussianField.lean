import Foundation.ClosedOperatorEnergyResolvent
import Foundation.GaussianHilbertProcess
import Foundation.GaussianFirstChaosRecovery

/-! A genuine Gaussian field whose covariance is the closed-derivative energy resolvent. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.EnergyResolventGaussianField
open ClosedOperatorEnergyResolvent InfiniteGaussian GaussianHilbertProcess
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [SecondCountableTopology F]

def feature (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) : E →L[ℝ] WithLp 2 (E × F) :=
  (projection T hT).comp input

theorem feature_inner (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x y : E) :
    inner ℝ (feature T hT x) (feature T hT y) = inner ℝ x (resolvent T hT y) := by
  change inner ℝ (WithLp.toLp 2 (resolvent T hT x, gradient T hT x))
    (WithLp.toLp 2 (resolvent T hT y, gradient T hT y)) = _
  rw [WithLp.prod_inner_apply]
  have hh := weak_identity T hT x ⟨resolvent T hT y, resolvent_mem_domain T hT y⟩
  rwa [derivative_resolvent] at hh

def embedding (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) : E →L[ℝ] GaussianL2 :=
  (isonormalEmbedding (WithLp 2 (E × F))).toContinuousLinearMap.comp (feature T hT)

def field (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) : SampleSpace → ℝ := embedding T hT x

theorem field_measurable (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    Measurable (field T hT x) := (Lp.stronglyMeasurable (embedding T hT x)).measurable

theorem field_gaussian (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) :
    IsGaussianProcess (field T hT) gaussianProduct :=
  (isonormal_isGaussianProcess (H := WithLp 2 (E × F))).comp_right (feature T hT)

theorem field_centered (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    (∫ ω, field T hT x ω ∂gaussianProduct)=0 := isonormal_integral (feature T hT x)

theorem field_product_integrable (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x y : E) :
    Integrable (fun ω => field T hT x ω * field T hT y ω) gaussianProduct :=
  isonormal_product_integrable (feature T hT x) (feature T hT y)

theorem field_covariance (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x y : E) :
    cov[field T hT x, field T hT y; gaussianProduct]=inner ℝ x (resolvent T hT y) := by
  change cov[isonormal _ (feature T hT x), isonormal _ (feature T hT y); gaussianProduct]=_
  rw [isonormal_covariance, feature_inner]

theorem embedding_inner (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x y : E) :
    inner ℝ (embedding T hT x) (embedding T hT y)=inner ℝ x (resolvent T hT y) := by
  change inner ℝ (isonormalEmbedding _ (feature T hT x))
    (isonormalEmbedding _ (feature T hT y))=_
  rw [isonormalEmbedding_inner, feature_inner]

theorem field_law (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    gaussianProduct.map (field T hT x) =
      gaussianReal 0 ⟨inner ℝ x (resolvent T hT x), resolvent_positive T hT x⟩ := by
  change gaussianProduct.map (isonormal _ (feature T hT x))=_
  rw [isonormal_law]
  have hh := feature_inner T hT x x
  rw [real_inner_self_eq_norm_sq] at hh
  congr 1
  exact Subtype.ext hh

theorem field_add_ae (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x y : E) :
    field T hT (x+y) =ᵐ[gaussianProduct] fun ω => field T hT x ω + field T hT y ω := by
  change (embedding T hT (x+y) : SampleSpace → ℝ)=ᵐ[_] _
  rw [map_add]
  exact Lp.coeFn_add _ _

theorem field_smul_ae (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (a : ℝ) (x : E) :
    field T hT (a • x) =ᵐ[gaussianProduct] fun ω => a * field T hT x ω := by
  change (embedding T hT (a • x) : SampleSpace → ℝ)=ᵐ[_] _
  rw [map_smul]
  exact Lp.coeFn_smul _ _

theorem embedding_continuous (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) :
    Continuous (embedding T hT) := (embedding T hT).continuous

theorem variance_positive (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (x : E) (hx : x≠0) :
    0 < inner ℝ x (resolvent T hT x) := by
  by_contra hn
  have hv := le_of_not_gt hn
  have hr : ‖resolvent T hT x‖=0 := by
    nlinarith [energy_identity T hT x, sq_nonneg ‖gradient T hT x‖,
      norm_nonneg (resolvent T hT x)]
  exact hx (resolvent_injective T hT hd ((norm_eq_zero.mp hr).trans (map_zero _).symm))

def sourceDerivative (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) : GaussianVectorL2 :=
  scalarTensor (SeparableHilbertEmbedding.hilbertEmbedding (WithLp 2 (E × F))
    (feature T hT x)) gaussianOne

theorem source_derivative_graph (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    (embedding T hT x, sourceDerivative T hT x) ∈ closedCylindricalDerivative.graph :=
  GaussianFirstChaosRecovery.firstChaos_derivative_graph _

theorem source_divergence_graph (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    (sourceDerivative T hT x, embedding T hT x) ∈ hilbertDivergence.graph :=
  GaussianFirstChaosRecovery.firstChaos_divergence_graph _

theorem source_recovery (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    GaussianDivergenceRecovery.recovery (embedding T hT x)=sourceDerivative T hT x :=
  GaussianFirstChaosRecovery.recovery_firstChaos _

end OperatorDerivativeRewrite.Foundation.EnergyResolventGaussianField
