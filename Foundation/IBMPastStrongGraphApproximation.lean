import Foundation.ScaledGraphResolventDomain
import Foundation.IBMNativeFieldSamples

/-! ORIGINAL native graph convergence of the existing fixed-past resolvent on
EVERY admissible past observable. This is a different family from integrals
of pointwise changing-past resolvents; no convergence equivalence is asserted. -/
noncomputable section
open Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPastStrongGraphApproximation
open IBMTimeAveragedObservable IBMPastIntrinsicOperators IBMPastGraphRegularization
open IBMJointIntrinsicDerivative IBMRampSimpsonNativeAverage
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
local instance (T : ℝ≥0) : CompleteSpace (pastSpace T) := (pastSpace_closed T).completeSpace_coe

theorem native_gradient_norm_le (T : ℝ≥0) (n : ℕ) (f : (pastDerivative T).domain) :
    ‖gradient T n (f:pastSpace T)‖ ≤ ‖pastDerivative T f‖ :=
  ScaledGraphResolventDomain.nativeGradient_norm_le
    (pastDerivative T) (pastDerivative_closed T) (pastDerivative_dense T) n f

theorem native_gradient_tendsto (T : ℝ≥0) (f : (pastDerivative T).domain) :
    Tendsto (fun n => gradient T n (f:pastSpace T)) atTop (𝓝 (pastDerivative T f)) :=
  ScaledGraphResolventDomain.nativeGradient_tendsto
    (pastDerivative T) (pastDerivative_closed T) (pastDerivative_dense T) f

theorem original_graph_tendsto (T : ℝ≥0) (f : (pastDerivative T).domain) :
    Tendsto (fun n => (regularizer T n (f:pastSpace T),gradient T n (f:pastSpace T)))
      atTop (𝓝 ((f:pastSpace T),pastDerivative T f)) :=
  ScaledGraphResolventDomain.original_graph_tendsto
    (pastDerivative T) (pastDerivative_closed T) (pastDerivative_dense T) f

def average (T : ℝ≥0) : pastSpace T :=
  ⟨intrinsicAverage T,by
    change (intrinsicAverage T : JointL2) ∈ IBMNaturalFiltrationObstruction.past T
    rw [← nativeAverage_eq_intrinsicAverage]
    exact IBMPastAverageCore.nativeAverage_mem_past le_rfl⟩

theorem average_domain (T : ℝ≥0) : average T ∈ (pastDerivative T).domain :=
  average_mem_joint_domain T

theorem average_derivative (T : ℝ≥0) :
    pastDerivative T ⟨average T,average_domain T⟩ = averageGradient T := rfl

def averageInput (T : ℝ≥0) (n : ℕ) : pastSpace T := regularizer T n (average T)
def averageField (T : ℝ≥0) (n : ℕ) : JointFieldSpace := gradient T n (average T)

theorem averageInput_domain (T : ℝ≥0) (n : ℕ) :
    averageInput T n ∈ (pastDerivative T).domain := regularizer_domain T n (average T)

theorem averageField_native (T : ℝ≥0) (n : ℕ) :
    pastDerivative T ⟨averageInput T n,averageInput_domain T n⟩ = averageField T n := rfl

theorem averageField_norm_le (T : ℝ≥0) (n : ℕ) : ‖averageField T n‖ ≤ ‖averageGradient T‖ := by
  change ‖gradient T n (average T)‖ ≤ ‖averageGradient T‖
  simpa only [average_derivative] using native_gradient_norm_le T n ⟨average T,average_domain T⟩

theorem averageField_tendsto (T : ℝ≥0) :
    Tendsto (averageField T) atTop (𝓝 (averageGradient T)) := by
  change Tendsto (fun n => gradient T n (average T)) atTop (𝓝 (averageGradient T))
  simpa only [average_derivative] using native_gradient_tendsto T ⟨average T,average_domain T⟩

theorem average_graph_tendsto (T : ℝ≥0) :
    Tendsto (fun n => (averageInput T n,averageField T n))
      atTop (𝓝 (average T,averageGradient T)) := by
  change Tendsto (fun n => (regularizer T n (average T),gradient T n (average T)))
    atTop (𝓝 (average T,averageGradient T))
  simpa only [average_derivative] using original_graph_tendsto T ⟨average T,average_domain T⟩

theorem average_actual_L2_tendsto (T : ℝ≥0) :
    Tendsto (fun n => ((averageInput T n).val : JointL2)) atTop (𝓝 (nativeAverage T)) := by
  have h := (continuous_subtype_val.comp continuous_subtype_val).tendsto (average T)
    |>.comp (regularizer_tendsto T (average T))
  simpa only [Function.comp_def,averageInput,average,nativeAverage_eq_intrinsicAverage] using h

theorem averageInput_past (T : ℝ≥0) (n : ℕ) :
    ((averageInput T n).val : JointL2) ∈ IBMNaturalFiltrationObstruction.past T :=
  (averageInput T n).property

end OperatorDerivativeRewrite.Foundation.IBMPastStrongGraphApproximation
