import Foundation.IBMSchwartzFullReflectedIto
import Foundation.IBMSceneryNativeAdjoint

/-! All-source-chaos Schwartz reflected Ito identities realized in the actual
joint IBM law and ORIGINAL clock adjoint. Only the compensated sum has an
unconditional mollifier limit; no individual singular limit is inferred. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzNativeJointIto
open InfiniteGaussian GaussianComplexHorizonIto IBMTimeAveragedObservable
open IBMIntrinsicOperators IBMSchwartzFullReflectedIto
local instance : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable GaussianTimeProcess.naturalFiltration
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] realPredictableL2_secondCountable

def flatten (T : ℝ≥0) : GaussianSourceClockIto.Domain T →ₗᵢ[ℝ]
    Lp ℝ 2 ((predictableMeasure T).prod gaussianProduct) :=
  (ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct).symm.toLinearIsometry.comp
    (GaussianSourceClockIto.trimEquiv T).toLinearIsometry

theorem integral_agreement (T : ℝ≥0) (u : GaussianSourceClockIto.Domain T) :
    IBMSceneryClockIto.jointIntegral T (flatten T u) =
      jointRealization (GaussianSourceClockIto.integral T u) := by
  change ProductL2Curry.swap gaussianProduct gaussianProduct
    ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
      (GaussianParameterizedIto.realIntegral gaussianProduct T
        ((ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct)
          ((ProductL2Curry.curryEquiv (predictableMeasure T) gaussianProduct).symm
            (GaussianSourceClockIto.trimEquiv T u))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

def scalarInput (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :=
  flatten T (integrand g a n T)

def field (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : FieldSpace :=
  IBMSceneryNativeAdjoint.field T (scalarInput g a n T)

theorem clock_mem (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    field g a n T ∈ clockDerivative.adjoint.domain :=
  IBMSceneryNativeAdjoint.clock_mem T _

theorem clock_value (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    clockDerivative.adjoint ⟨field g a n T,clock_mem g a n T⟩ =
      jointRealization (integralValue g a n T) :=
  (IBMSceneryNativeAdjoint.clock_value T _).trans
    (integral_agreement T (integrand g a n T))

def correction (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : JointL2 :=
  jointRealization (IBMSchwartzBochnerDomain.wholeClass g a n T)

def endpoint (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : JointL2 :=
  jointRealization (endpointClass g a n T)

def limit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : JointL2 :=
  jointRealization (endpointLimitClass g a T)

theorem finite_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    endpoint g a n T =
      clockDerivative.adjoint ⟨field g a n T,clock_mem g a n T⟩ + correction g a n T := by
  rw [clock_value]
  exact congrArg jointRealization (finite_mollifier_identity g a n T) |>.trans
    (map_add jointRealization _ _)

theorem compensated_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n =>
      clockDerivative.adjoint ⟨field g a n T,clock_mem g a n T⟩ + correction g a n T)
      atTop (𝓝 (limit g a T)) := by
  have h := jointRealization.continuous.tendsto (endpointLimitClass g a T)
    |>.comp (endpointClass_tendsto g a T)
  simpa only [← finite_identity, endpoint, limit, Function.comp_def] using h

theorem actual_limit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    limit g a T =ᵐ[IBMSourceLaws.jointMeasure]
      fun w => g (a+IBMConstructedSources.ibmValue T w)-g a := by
  apply jointRealization_ae_of_sections
  · exact (g.continuous.measurable.comp
      ((IBMConstructedSources.ibmValue_jointly_measurable.comp
        (measurable_const.prodMk measurable_id)).const_add a)).sub_const _
  · exact endpointLimitClass_actual_sections g a T

theorem native_sections (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ X ∂gaussianProduct,
      (fun Y => clockDerivative.adjoint ⟨field g a n T,clock_mem g a n T⟩ (X,Y))
        =ᵐ[gaussianProduct] GaussianPredictableHorizon.itoIntegral T
          (IBMSceneryClockIto.sectionPredictable T (scalarInput g a n T) X) := by
  have hv : clockDerivative.adjoint ⟨field g a n T,clock_mem g a n T⟩ =
      IBMSceneryClockIto.jointIntegral T (scalarInput g a n T) :=
    IBMSceneryNativeAdjoint.clock_value T _
  rw [hv]
  exact IBMSceneryClockIto.joint_sections_native T _

theorem correction_cauchy_iff (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    CauchySeq (fun n => correction g a n T) ↔
      CauchySeq (fun n => scalarInput g a n T) := by
  simpa only [Metric.cauchySeq_iff, correction, jointRealization.isometry.dist_eq,
    scalarInput, (flatten T).isometry.dist_eq] using (whole_cauchy_iff_integrand g a T)

end OperatorDerivativeRewrite.Foundation.IBMSchwartzNativeJointIto
