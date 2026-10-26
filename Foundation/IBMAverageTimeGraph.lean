import Foundation.IBMPastStrongGraphApproximation
import Foundation.IBMPastHorizonGraph
import Foundation.BochnerL2Dominated

/-! Actual averaged IBM as a native-domain time curve. Fixed-past resolvents
retain the original derivative and the original Gaussian coupling. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMAverageTimeGraph
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative
open IBMPastIntrinsicOperators IBMPastHorizonGraph IBMPastStrongGraphApproximation
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : SecondCountableTopology InfiniteGaussian.GaussianVectorL2 :=
  Lp.SecondCountableTopology (E := InfiniteGaussian.CoefficientSpace) (p := 2)
    (μ := InfiniteGaussian.gaussianProduct)
local instance : SecondCountableTopology IBMIntrinsicOperators.FieldSpace :=
  Lp.SecondCountableTopology (E := InfiniteGaussian.GaussianVectorL2) (p := 2)
    (μ := InfiniteGaussian.gaussianProduct)
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
local instance (T : ℝ≥0) : CompleteSpace (pastSpace T) := (pastSpace_closed T).completeSpace_coe

/-- The existing monotone graph projection applies to any measurable past curve. -/
theorem nativePair_curve_stronglyMeasurable (n : ℕ) (u : ∀ T, pastSpace T)
    (hu : StronglyMeasurable (fun T => (u T).val)) :
    StronglyMeasurable (fun T => nativePair n T (u T)) := by
  borelize Ambient
  have hp : StronglyMeasurable (fun p : Ambient × ℝ≥0 =>
      (horizonGraph n p.2).starProjection p.1) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun x : Ambient => fun T : ℝ≥0 => (horizonGraph n T).starProjection x)
      (fun T => (horizonGraph n T).starProjection.continuous) (projection_stronglyMeasurable n)
  have hi := (ClosedOperatorEnergyResolvent.input (E := IntrinsicSpace)
    (F := JointFieldSpace)).continuous.comp_stronglyMeasurable hu
  have hm := hp.comp_measurable (hi.measurable.prodMk measurable_id)
  change StronglyMeasurable (fun T => (horizonGraph n T).starProjection
    (WithLp.toLp 2 (((u T).val:IntrinsicSpace),(0:JointFieldSpace)))) at hm
  simpa only [projection_nativePair] using hm

theorem average_continuous : Continuous (fun T : ℝ≥0 => intrinsicAverage (T:ℝ)) := by
  have hc := (intervalIntegral.differentiable_integral_of_continuous
    (a := (0:ℝ)) (intrinsicCurve_continuous.comp continuous_real_toNNReal)).continuous
  have he (T : ℝ≥0) : intrinsicAverage (T:ℝ) =
      ∫ t in (0:ℝ)..(T:ℝ), intrinsicCurve t.toNNReal := by
    rw [intervalIntegral.integral_of_le T.coe_nonneg]
    rfl
  simp_rw [he]
  exact hc.comp NNReal.continuous_coe

theorem averagePair_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (fun T => nativePair n T (average T)) :=
  nativePair_curve_stronglyMeasurable n average average_continuous.stronglyMeasurable

theorem averageInput_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (fun T => (averageInput T n).val) :=
  (WithLp.fstL 2 ℝ IntrinsicSpace JointFieldSpace).continuous.comp_stronglyMeasurable
    (averagePair_stronglyMeasurable n)

theorem averageField_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (fun T => averageField T n) := by
  have h := (WithLp.sndL 2 ℝ IntrinsicSpace JointFieldSpace).continuous.comp_stronglyMeasurable
    (averagePair_stronglyMeasurable n)
  have hs := h.const_smul ((ScaledGraphResolvent.scale n)⁻¹)
  convert hs using 1
  funext T
  change averageField T n = (ScaledGraphResolvent.scale n)⁻¹ •
    (ScaledGraphResolvent.scale n • averageField T n)
  rw [smul_smul,inv_mul_cancel₀ (ScaledGraphResolvent.scale_pos n).ne',one_smul]

theorem averageGradient_stronglyMeasurable :
    StronglyMeasurable IBMRampSimpsonNativeAverage.averageGradient :=
  stronglyMeasurable_of_tendsto (f := fun n T => averageField T n) atTop
    (fun n => averageField_stronglyMeasurable n)
    (tendsto_pi_nhds.mpr fun T => averageField_tendsto T)

theorem averageGradient_source (T : ℝ≥0) :
    IBMRampSimpsonNativeAverage.averageGradient T 0 = sourceGradient (sourceAverage T) := by
  have h := ((joint_graph_iff _ _).mp (jointDerivative.mem_graph
    ⟨intrinsicAverage T,IBMRampSimpsonNativeAverage.average_mem_joint_domain T⟩)).1
  have ho := (ObservableRestriction.derivative_graph _ _ _ _).mp h
  have ht := (AdjointUnitaryTransport.mem_pullback_graph _ _ _ _).mp ho
  have he : IBMIntrinsicOperators.sourceUnitary (intrinsicAverage T : JointL2) =
      sourceAverage T := by
    rw [← nativeAverage_eq_intrinsicAverage]
    exact IBMNonlinearAverageGraph.nativeAverage_source_representation T
  exact IBMFiniteAverageCore.partialDerivative.mem_graph_snd_inj ht
    (sourceAverage_source_graph T) he

theorem averageGradient_clock (T : ℝ≥0) :
    IBMRampSimpsonNativeAverage.averageGradient T 1 = IBMClockPhysicalOccupation.gradient T := by
  have h := ((joint_graph_iff _ _).mp (jointDerivative.mem_graph
    ⟨intrinsicAverage T,IBMRampSimpsonNativeAverage.average_mem_joint_domain T⟩)).2
  have ho := (ObservableRestriction.derivative_graph _ _ _ _).mp h
  have ht := (AdjointUnitaryTransport.mem_pullback_graph _ _ _ _).mp ho
  have he : IBMIntrinsicOperators.clockUnitary (intrinsicAverage T : JointL2) =
      IBMFirstSourceClockGraph.flip (sourceAverage T) := by
    rw [← nativeAverage_eq_intrinsicAverage]
    exact IBMClockAverageGraph.nativeAverage_clock_representation T
  exact IBMFiniteAverageCore.partialDerivative.mem_graph_snd_inj ht
    (IBMClockPhysicalOccupation.gradient_graph T) he

def energyEnvelope (T : ℝ≥0) : ℝ := ‖sourceGradient (sourceAverage T)‖^2 +
  8 * IBMFoldedTransitionBound.peak 1 * (T:ℝ)^2 * Real.sqrt T

theorem energyEnvelope_continuous : Continuous energyEnvelope := by
  have hc := (intervalIntegral.differentiable_integral_of_continuous
    (a := (0:ℝ)) (source_time_continuous.comp continuous_real_toNNReal)).continuous
  have hs : Continuous (fun T : ℝ≥0 => sourceAverage T) := by
    have he (T : ℝ≥0) : sourceAverage T = ∫ t in (0:ℝ)..(T:ℝ),
        IBMRandomTimeHilbert.randomSourceL2 t.toNNReal := sourceAverage_eq_interval T.coe_nonneg
    simp_rw [he]
    exact hc.comp NNReal.continuous_coe
  exact ((sourceGradient.continuous.comp hs).norm.pow 2).add
    (((continuous_const.mul (NNReal.continuous_coe.pow 2))).mul
      (Real.continuous_sqrt.comp NNReal.continuous_coe))

theorem averageGradient_energy (T : ℝ≥0) :
    ‖IBMRampSimpsonNativeAverage.averageGradient T‖^2 ≤ energyEnvelope T := by
  have hc := (IBMClockAverageGraph.source_average_clock_domain T.coe_nonneg).choose_spec
  have he : ‖IBMClockPhysicalOccupation.gradient T‖^2 ≤
      8 * IBMFoldedTransitionBound.peak 1 * (T:ℝ)^2 * Real.sqrt T := hc
  rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two,averageGradient_source,averageGradient_clock]
  exact add_le_add le_rfl he

theorem averageGradient_time_memLp (H : ℝ) :
    MemLp (fun t : ℝ => IBMRampSimpsonNativeAverage.averageGradient t.toNNReal)
      2 (IBMClockOverlapEnergy.window H) := by
  have hm := averageGradient_stronglyMeasurable.comp_measurable continuous_real_toNNReal.measurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply ((energyEnvelope_continuous.comp continuous_real_toNNReal).integrableOn_Icc
    (a := (0:ℝ)) (b := H)).mono_set Ioc_subset_Icc_self |>.mono'
      ((hm.norm.pow 2).aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    change ‖‖IBMRampSimpsonNativeAverage.averageGradient t.toNNReal‖^2‖ ≤
      energyEnvelope t.toNNReal
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact averageGradient_energy t.toNNReal

theorem averageField_time_memLp (n : ℕ) (H : ℝ) :
    MemLp (fun t : ℝ => averageField t.toNNReal n) 2 (IBMClockOverlapEnergy.window H) := by
  have hm := (averageField_stronglyMeasurable n).comp_measurable
    continuous_real_toNNReal.measurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply ((averageGradient_time_memLp H).norm.integrable_sq).mono'
    ((hm.norm.pow 2).aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    change ‖‖averageField t.toNNReal n‖^2‖ ≤
      ‖IBMRampSimpsonNativeAverage.averageGradient t.toNNReal‖^2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (averageField_norm_le t.toNNReal n) 2

def fieldClass (n : ℕ) (H : ℝ) : Lp JointFieldSpace 2 (IBMClockOverlapEnergy.window H) :=
  (averageField_time_memLp n H).toLp (fun t => averageField t.toNNReal n)

def gradientClass (H : ℝ) : Lp JointFieldSpace 2 (IBMClockOverlapEnergy.window H) :=
  (averageGradient_time_memLp H).toLp
    (fun t => IBMRampSimpsonNativeAverage.averageGradient t.toNNReal)

theorem fieldClass_ae (n : ℕ) (H : ℝ) : fieldClass n H =ᵐ[IBMClockOverlapEnergy.window H]
    (fun t => averageField t.toNNReal n) := MemLp.coeFn_toLp _

theorem gradientClass_ae (H : ℝ) : gradientClass H =ᵐ[IBMClockOverlapEnergy.window H]
    (fun t => IBMRampSimpsonNativeAverage.averageGradient t.toNNReal) := MemLp.coeFn_toLp _

attribute [local irreducible] fieldClass gradientClass
  IBMPastStrongGraphApproximation.averageField IBMRampSimpsonNativeAverage.averageGradient

theorem fieldClass_tendsto (H : ℝ) :
    Tendsto (fun n => fieldClass n H) atTop (𝓝 (gradientClass H)) := by
  apply BochnerL2Dominated.tendsto_of_ae_norm_bound
  · intro n
    filter_upwards [fieldClass_ae n H,
      gradientClass_ae H] with t hn ht
    rw [hn,ht]
    exact averageField_norm_le t.toNNReal n
  · filter_upwards [ae_all_iff.mpr (fun n =>
        fieldClass_ae n H),
      gradientClass_ae H] with t hn ht
    rw [ht]
    exact (averageField_tendsto t.toNNReal).congr'
      (Eventually.of_forall fun n => (hn n).symm)

theorem averageInput_norm_le (T : ℝ≥0) (n : ℕ) :
    ‖(averageInput T n).val‖ ≤ ‖intrinsicAverage T‖ :=
  ScaledGraphResolvent.regularize_contraction (pastDerivative T) (pastDerivative_closed T)
    n (average T)

theorem average_time_memLp (H : ℝ) :
    MemLp (fun t : ℝ => intrinsicAverage (t.toNNReal:ℝ)) 2 (IBMClockOverlapEnergy.window H) := by
  have hc := average_continuous.comp continuous_real_toNNReal
  exact (memLp_two_iff_integrable_sq_norm hc.stronglyMeasurable.aestronglyMeasurable).mpr
    ((hc.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)

theorem averageInput_time_memLp (n : ℕ) (H : ℝ) :
    MemLp (fun t : ℝ => (averageInput t.toNNReal n).val) 2 (IBMClockOverlapEnergy.window H) := by
  have hm := (averageInput_stronglyMeasurable n).comp_measurable
    continuous_real_toNNReal.measurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply ((average_time_memLp H).norm.integrable_sq).mono' ((hm.norm.pow 2).aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    change ‖‖(averageInput t.toNNReal n).val‖^2‖ ≤ ‖intrinsicAverage (t.toNNReal:ℝ)‖^2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (averageInput_norm_le t.toNNReal n) 2

def inputClass (n : ℕ) (H : ℝ) : Lp IntrinsicSpace 2 (IBMClockOverlapEnergy.window H) :=
  (averageInput_time_memLp n H).toLp (fun t => (averageInput t.toNNReal n).val)

def averageClass (H : ℝ) : Lp IntrinsicSpace 2 (IBMClockOverlapEnergy.window H) :=
  (average_time_memLp H).toLp (fun t => intrinsicAverage (t.toNNReal:ℝ))

theorem inputClass_ae (n : ℕ) (H : ℝ) : inputClass n H =ᵐ[IBMClockOverlapEnergy.window H]
    (fun t => (averageInput t.toNNReal n).val) := MemLp.coeFn_toLp _

theorem averageClass_ae (H : ℝ) : averageClass H =ᵐ[IBMClockOverlapEnergy.window H]
    (fun t => intrinsicAverage (t.toNNReal:ℝ)) := MemLp.coeFn_toLp _

attribute [local irreducible] inputClass averageClass
  IBMPastStrongGraphApproximation.averageInput

theorem inputClass_tendsto (H : ℝ) :
    Tendsto (fun n => inputClass n H) atTop (𝓝 (averageClass H)) := by
  apply BochnerL2Dominated.tendsto_of_ae_norm_bound
  · intro n
    filter_upwards [inputClass_ae n H,
      averageClass_ae H] with t hn ht
    rw [hn,ht]
    exact averageInput_norm_le t.toNNReal n
  · filter_upwards [ae_all_iff.mpr (fun n =>
        inputClass_ae n H),
      averageClass_ae H] with t hn ht
    rw [show (fun n => inputClass n H t) =
      (fun n => (averageInput t.toNNReal n).val) from funext hn,ht]
    have hv := continuous_subtype_val.tendsto (average t.toNNReal) |>.comp
      (IBMPastGraphRegularization.regularizer_tendsto t.toNNReal (average t.toNNReal))
    simpa only [averageInput,Function.comp_def,
      IBMPastStrongGraphApproximation.average] using hv

theorem time_graph_tendsto (H : ℝ) :
    Tendsto (fun n => (inputClass n H,fieldClass n H)) atTop
      (𝓝 (averageClass H,gradientClass H)) :=
  (inputClass_tendsto H).prodMk_nhds (fieldClass_tendsto H)

theorem time_native_graph (n : ℕ) (H : ℝ) :
    (inputClass n H,fieldClass n H) ∈
      (BochnerClosedOperator.lift (IBMClockOverlapEnergy.window H) jointDerivative).graph := by
  rw [BochnerClosedOperator.mem_lift_graph_iff]
  filter_upwards [inputClass_ae n H,
    fieldClass_ae n H] with t hi hg
  rw [hi,hg]
  apply (ObservableRestriction.derivative_graph jointDerivative (pastSpace t.toNNReal) _ _).mp
  rw [← averageField_native t.toNNReal n]
  exact (pastDerivative t.toNNReal).mem_graph ⟨averageInput t.toNNReal n,averageInput_domain _ _⟩

theorem time_target_graph (H : ℝ) :
    (averageClass H,gradientClass H) ∈
      (BochnerClosedOperator.lift (IBMClockOverlapEnergy.window H) jointDerivative).graph := by
  rw [BochnerClosedOperator.mem_lift_graph_iff]
  filter_upwards [averageClass_ae H,
    gradientClass_ae H] with t hi hg
  rw [hi,hg]
  simpa only [IBMRampSimpsonNativeAverage.averageGradient] using jointDerivative.mem_graph
    ⟨_,IBMRampSimpsonNativeAverage.average_mem_joint_domain t.toNNReal⟩

end OperatorDerivativeRewrite.Foundation.IBMAverageTimeGraph
