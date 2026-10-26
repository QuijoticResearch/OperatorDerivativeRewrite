import Foundation.IBMPastTimeRealization
import Foundation.BochnerClosedOperator
import Foundation.IBMRampSimpsonNativeAverage

/-! Actual native TWO-source derivative fields of the existing IBM regularizers
on finite physical-time windows. The operator and Gaussian charts are unchanged. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPastTimeGradient
open IBMTimeAveragedObservable IBMPastGraphRegularization IBMPastIntrinsicOperators
open IBMJointIntrinsicDerivative IBMPastTimeRealization IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
local instance (T : ℝ≥0) : CompleteSpace (pastSpace T) := (pastSpace_closed T).completeSpace_coe

def input (n : ℕ) (t : ℝ) : IntrinsicSpace := (regularizer t.toNNReal n (endpoint t.toNNReal)).val
def field (n : ℕ) (t : ℝ) : JointFieldSpace := gradient t.toNNReal n (endpoint t.toNNReal)

theorem input_stronglyMeasurable (n : ℕ) : StronglyMeasurable (input n) := by
  have h : StronglyMeasurable (fun T =>
      ((regularizer T n (endpoint T)).val : IntrinsicSpace)) :=
    (WithLp.fstL 2 ℝ IntrinsicSpace JointFieldSpace).continuous.comp_stronglyMeasurable
      (IBMPastHorizonGraph.nativePair_stronglyMeasurable n)
  exact h.comp_measurable continuous_real_toNNReal.measurable

theorem field_stronglyMeasurable (n : ℕ) : StronglyMeasurable (field n) :=
  (IBMPastHorizonGraph.gradient_stronglyMeasurable n).comp_measurable
    continuous_real_toNNReal.measurable

theorem field_norm_le (n : ℕ) (t : ℝ) :
    ‖field n t‖ ≤ ‖timeTarget t‖ / ScaledGraphResolvent.scale n := by
  have hb := ScaledGraphResolvent.scaled_gradient_bound
    (E := pastSpace t.toNNReal) (F := JointFieldSpace)
    (pastDerivative t.toNNReal) (pastDerivative_closed t.toNNReal) n (endpoint t.toNNReal)
  change ‖ScaledGraphResolvent.scale n • field n t‖ ≤ ‖timeTarget t‖ at hb
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (ScaledGraphResolvent.scale_pos n)] at hb
  exact (le_div_iff₀ (ScaledGraphResolvent.scale_pos n)).mpr (by simpa only [mul_comm] using hb)

theorem input_memLp (n : ℕ) (H : ℝ) : MemLp (input n) 2 (window H) := by
  apply (memLp_two_iff_integrable_sq_norm (input_stronglyMeasurable n).aestronglyMeasurable).mpr
  change Integrable (fun t => ‖timeInput n t‖^2) (window H)
  exact (timeInput_memLp n H).norm.integrable_sq

theorem field_memLp (n : ℕ) (H : ℝ) : MemLp (field n) 2 (window H) := by
  apply (memLp_two_iff_integrable_sq_norm (field_stronglyMeasurable n).aestronglyMeasurable).mpr
  apply ((target_sq_integrable H).div_const ((ScaledGraphResolvent.scale n)^2)).mono'
    (((field_stronglyMeasurable n).norm.pow 2).aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    change ‖‖field n t‖^2‖ ≤ ‖timeTarget t‖^2 / (ScaledGraphResolvent.scale n)^2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [div_pow] using pow_le_pow_left₀ (norm_nonneg _) (field_norm_le n t) 2

theorem input_field_graph (n : ℕ) (t : ℝ) : (input n t,field n t) ∈ jointDerivative.graph := by
  apply (ObservableRestriction.derivative_graph jointDerivative (pastSpace t.toNNReal)
    (regularizer t.toNNReal n (endpoint t.toNNReal)) (field n t)).mp
  exact (pastDerivative t.toNNReal).mem_graph
    ⟨regularizer t.toNNReal n (endpoint t.toNNReal),
      regularizer_domain t.toNNReal n (endpoint t.toNNReal)⟩

theorem time_lift_graph (n : ℕ) (H : ℝ) :
    ((input_memLp n H).toLp (input n),(field_memLp n H).toLp (field n)) ∈
      (BochnerClosedOperator.lift (window H) jointDerivative).graph := by
  rw [BochnerClosedOperator.mem_lift_graph_iff]
  filter_upwards [MemLp.coeFn_toLp (input_memLp n H),MemLp.coeFn_toLp (field_memLp n H)]
    with t hi hg
  rw [hi,hg]
  exact input_field_graph n t

def integratedInput (n : ℕ) (H : ℝ) : IntrinsicSpace := ∫ t, input n t ∂window H
def integratedField (n : ℕ) (H : ℝ) : JointFieldSpace := ∫ t, field n t ∂window H

theorem integrated_graph (n : ℕ) (H : ℝ) :
    (integratedInput n H,integratedField n H) ∈ jointDerivative.graph := by
  let G := jointDerivative.graph
  let : CompleteSpace G := jointDerivative_closed.completeSpace_coe
  let g (t : ℝ) : G := ⟨(input n t,field n t),input_field_graph n t⟩
  have hm : StronglyMeasurable g :=
    (Embedding.comp_stronglyMeasurable_iff Topology.IsEmbedding.subtypeVal).mp
      ((input_stronglyMeasurable n).prodMk (field_stronglyMeasurable n))
  have hu := (input_memLp n H).integrable (by norm_num)
  have hv := (field_memLp n H).integrable (by norm_num)
  have hp := hu.prodMk hv
  have hg : Integrable g (window H) := hp.norm.mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun _ => le_rfl)
  have he := G.subtypeL.integral_comp_comm hg
  have hf := (ContinuousLinearMap.fst ℝ IntrinsicSpace JointFieldSpace).integral_comp_comm hp
  have hs := (ContinuousLinearMap.snd ℝ IntrinsicSpace JointFieldSpace).integral_comp_comm hp
  have hpair : (integratedInput n H,integratedField n H) = ((∫ t, g t ∂window H : G) :
      IntrinsicSpace × JointFieldSpace) := by
    apply Prod.ext
    · exact hf.trans (congrArg Prod.fst he)
    · exact hs.trans (congrArg Prod.snd he)
  rw [hpair]
  exact (∫ t, g t ∂window H : G).property

theorem integratedInput_domain (n : ℕ) (H : ℝ) : integratedInput n H ∈ jointDerivative.domain :=
  LinearPMap.mem_domain_of_mem_graph (integrated_graph n H)

theorem integrated_derivative (n : ℕ) (H : ℝ) :
    jointDerivative ⟨integratedInput n H,integratedInput_domain n H⟩ = integratedField n H :=
  ((LinearPMap.image_iff (integratedInput_domain n H)).mpr (integrated_graph n H)).symm

theorem integratedInput_actual_class (n : ℕ) (H : ℝ) :
    (integratedInput n H : JointL2) = integratedSampleClass n H := by
  rw [integratedSampleClass_eq]
  exact (IntrinsicSpace.subtypeL.integral_comp_comm
    ((input_memLp n H).integrable (by norm_num))).symm

theorem integratedInput_tendsto (H : ℝ) :
    Tendsto (fun n => integratedInput n H) atTop (𝓝 (intrinsicAverage H)) := by
  apply tendsto_subtype_rng.mpr
  simpa only [integratedInput_actual_class,nativeAverage_eq_intrinsicAverage] using
    integratedSampleClass_tendsto H

/-- These are ACTUAL native derivatives of actual time-integral approximants.
Convergence is in the full-adjoint graph TEST DUAL norm, not native field norm. -/
theorem integratedField_graphDual_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMIntrinsicGraphDual.embed (integratedField n T)) atTop
      (𝓝 (IBMIntrinsicGraphDual.embed (IBMRampSimpsonNativeAverage.averageGradient T))) := by
  have h := IBMIntrinsicGraphDual.graph_dual_limit (intrinsicAverage T)
    (fun n => ⟨integratedInput n T,integratedInput_domain n T⟩) (integratedInput_tendsto T)
  simpa only [integrated_derivative,← IBMRampSimpsonNativeAverage.averageGradient_embed] using h

theorem integratedField_graphDual_error (n : ℕ) (T : ℝ≥0) :
    ‖IBMIntrinsicGraphDual.embed (integratedField n T) -
      IBMIntrinsicGraphDual.embed (IBMRampSimpsonNativeAverage.averageGradient T)‖ ≤
      ‖integratedInput n T-intrinsicAverage T‖ := by
  have h := IBMIntrinsicGraphDual.graph_dual_error (intrinsicAverage T)
    ⟨integratedInput n T,integratedInput_domain n T⟩
  simpa only [integrated_derivative,← IBMRampSimpsonNativeAverage.averageGradient_embed] using h

end OperatorDerivativeRewrite.Foundation.IBMPastTimeGradient
