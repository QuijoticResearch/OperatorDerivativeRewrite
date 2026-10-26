import Foundation.ScaledGraphResolvent
import Foundation.IBMPastIntrinsicOperators
import Foundation.IBMClockNativeSmoothing
import Foundation.ClosedOperatorEscapeEnergy

/-! Canonical adapted actual IBM endpoint approximations in BOTH original native
derivative domains. Exact past-adjoint corrections converge in graph norm;
clock gradients of the rough positive-time endpoint approximations escape.
These fixed-horizon native identities are not a physical-time Ito formula. -/
noncomputable section
open Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPastGraphRegularization
open IBMTimeAveragedObservable IBMPastIntrinsicOperators IBMJointIntrinsicDerivative
open ScaledGraphResolvent
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
attribute [local irreducible] ScaledGraphResolvent.regularize ScaledGraphResolvent.nativeGradient
attribute [local irreducible] IBMPastIntrinsicOperators.pastDerivative LinearPMap.adjoint
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable IBMConstructedSources.clockPath_measurable).completeSpace_coe
local instance (T : ℝ≥0) : CompleteSpace (pastSpace T) := (pastSpace_closed T).completeSpace_coe

def regularizer (T : ℝ≥0) (n : ℕ) : pastSpace T →L[ℝ] pastSpace T :=
  regularize (E := pastSpace T) (F := JointFieldSpace) (pastDerivative T) (pastDerivative_closed T) n

theorem regularizer_domain (T : ℝ≥0) (n : ℕ) (f : pastSpace T) :
    regularizer T n f ∈ (pastDerivative T).domain := by
  unfold regularizer
  exact regularize_mem (E := pastSpace T) (F := JointFieldSpace) (pastDerivative T) (pastDerivative_closed T) n f

theorem regularizer_tendsto (T : ℝ≥0) (f : pastSpace T) :
    Tendsto (fun n => regularizer T n f) atTop (𝓝 f) := by
  unfold regularizer
  exact regularize_tendsto (E := pastSpace T) (F := JointFieldSpace) (pastDerivative T) (pastDerivative_closed T) (pastDerivative_dense T) f

def endpoint (T : ℝ≥0) : pastSpace T :=
  ⟨intrinsicCurve T,IBMPastAverageCore.point_mem_past le_rfl⟩

def approximation (T : ℝ≥0) (n : ℕ) : JointL2 := (regularizer T n (endpoint T)).val

theorem approximation_past (T : ℝ≥0) (n : ℕ) :
    approximation T n ∈ IBMNaturalFiltrationObstruction.past T :=
  (regularizer T n (endpoint T)).property

theorem approximation_common_domain (T : ℝ≥0) (n : ℕ) :
    approximation T n ∈ IBMFiniteAverageCore.intrinsicCore := by
  exact ((past_domain_iff T _).1 (regularizer_domain T n (endpoint T))).1

theorem actual_endpoint_tendsto (T : ℝ≥0) :
    Tendsto (approximation T) atTop (𝓝 (intrinsicCurve T : JointL2)) := by
  have hc : Continuous (fun f : pastSpace T => (f.val:JointL2)) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact hc.tendsto (endpoint T) |>.comp (regularizer_tendsto T (endpoint T))

def gradient (T : ℝ≥0) (n : ℕ) (f : pastSpace T) : JointFieldSpace :=
  nativeGradient (E := pastSpace T) (F := JointFieldSpace) (pastDerivative T) (pastDerivative_closed T) n f

def correction (T : ℝ≥0) (n : ℕ) (f : pastSpace T) : JointFieldSpace := (scale n)^2 • gradient T n f

theorem correction_domain (T : ℝ≥0) (n : ℕ) (f : pastSpace T) :
    correction T n f ∈ (pastDivergence T).domain := by
  unfold correction gradient pastDivergence
  exact weighted_gradient_mem_adjoint (E := pastSpace T) (F := JointFieldSpace)
    (pastDerivative T) (pastDerivative_closed T) n f

theorem native_divergence_correction (T : ℝ≥0) (n : ℕ) (f : pastSpace T) :
    pastDivergence T ⟨correction T n f,correction_domain T n f⟩ = f-regularizer T n f := by
  simpa only [correction,gradient,pastDivergence,regularizer] using
    native_adjoint_identity (E := pastSpace T) (F := JointFieldSpace)
    (pastDerivative T) (pastDerivative_closed T) (pastDerivative_dense T) n f

theorem approximation_clock_domain (T : ℝ≥0) (n : ℕ) :
    approximation T n ∈ IBMIntrinsicOperators.clockDerivative.domain := by
  rw [IBMIntrinsicOperators.clockDerivative_domain]
  exact ((IBMFiniteAverageCore.mem_intrinsicCore_iff _).1 (approximation_common_domain T n)).2.1

def clockGradient (T : ℝ≥0) (n : ℕ) : IBMIntrinsicOperators.FieldSpace :=
  IBMIntrinsicOperators.clockDerivative ⟨approximation T n,approximation_clock_domain T n⟩

theorem actual_clock_gradient_escape (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ‖clockGradient T n‖) atTop atTop := by
  apply ClosedOperatorEscapeEnergy.output_norm_tendsto_atTop IBMIntrinsicOperators.clockDerivative
    IBMIntrinsicOperators.clockDerivative_closed IBMIntrinsicOperators.clockDerivative_dense
    (fun n => IBMIntrinsicOperators.clockDerivative.mem_graph
      ⟨approximation T n,approximation_clock_domain T n⟩) (actual_endpoint_tendsto T)
  exact IBMClockNativeSmoothing.actual_unsmoothed_not_clock_domain T hT

theorem correction_graph_tendsto_zero (T : ℝ≥0) (f : pastSpace T) :
    Tendsto (fun n => (correction T n f,
      pastDivergence T ⟨correction T n f,correction_domain T n f⟩)) atTop (𝓝 (0,0)) := by
  have hv : Tendsto (fun n => correction T n f) atTop (𝓝 0) := by
    unfold correction gradient
    exact weighted_gradient_tendsto_zero (E := pastSpace T) (F := JointFieldSpace)
      (pastDerivative T) (pastDerivative_closed T) f
  have hd : Tendsto (fun n => pastDivergence T ⟨correction T n f,correction_domain T n f⟩)
      atTop (𝓝 0) := by
    simp only [native_divergence_correction]
    apply tendsto_subtype_rng.2
    apply tendsto_subtype_rng.2
    change Tendsto (fun n => (f.val:JointL2)-((regularizer T n f).val:JointL2)) atTop (𝓝 0)
    have hc : Continuous (fun g : pastSpace T => (g.val:JointL2)) :=
      continuous_subtype_val.comp continuous_subtype_val
    have ht := hc.tendsto f |>.comp (regularizer_tendsto T f)
    have hf : Tendsto (fun _ : ℕ => (f.val:JointL2)) atTop (𝓝 (f.val:JointL2)) := tendsto_const_nhds
    simpa only [Function.comp_def,sub_self] using hf.sub ht
  exact hv.prodMk_nhds hd

end OperatorDerivativeRewrite.Foundation.IBMPastGraphRegularization
