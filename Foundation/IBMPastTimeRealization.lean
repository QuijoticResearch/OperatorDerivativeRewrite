import Foundation.IBMPastSampleRealization
import Foundation.AmbientNullAugmentation
import Foundation.FiniteMeasureL2Integration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual IBM native regularizers in local physical-time/sample L2.
The null augmentation is inside the ORIGINAL ambient sigma-algebra, not full
completion or right-continuous augmentation. No temporal stochastic driver is inferred. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPastTimeRealization
open IBMTimeAveragedObservable IBMPastGraphRegularization IBMPastSampleRealization
open IBMPastIntrinsicOperators IBMJointIntrinsicDerivative IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
local instance (T : ℝ≥0) : CompleteSpace (pastSpace T) := (pastSpace_closed T).completeSpace_coe

def augmentedFiltration := AmbientNullAugmentation.filtration IBMSourceLaws.jointMeasure
  IBMNaturalFiltrationObstruction.naturalFiltration

theorem sample_stronglyAdapted (n : ℕ) :
    StronglyAdapted augmentedFiltration (fun T ω => sample n (T,ω)) := by
  intro T
  apply Measurable.stronglyMeasurable
  exact AmbientNullAugmentation.measurable_of_raw_aestronglyMeasurable
    (IBMNaturalFiltrationObstruction.naturalFiltration T) IBMSourceLaws.jointMeasure
    ((sample_stronglyMeasurable n).measurable.comp measurable_prodMk_left) (sample_past n T)

def timeInput (n : ℕ) (t : ℝ) : JointL2 := approximation t.toNNReal n
def timeTarget (t : ℝ) : JointL2 := (intrinsicCurve t.toNNReal : JointL2)

theorem timeTarget_continuous : Continuous timeTarget :=
  continuous_subtype_val.comp (intrinsicCurve_continuous.comp continuous_real_toNNReal)

theorem input_norm_le (n : ℕ) (t : ℝ) : ‖timeInput n t‖ ≤ ‖timeTarget t‖ := by
  exact ScaledGraphResolvent.regularize_contraction (E := pastSpace t.toNNReal)
    (F := JointFieldSpace) (pastDerivative t.toNNReal) (pastDerivative_closed t.toNNReal)
    n (endpoint t.toNNReal)

theorem timeInput_stronglyMeasurable (n : ℕ) : StronglyMeasurable (timeInput n) :=
  (IBMPastHorizonGraph.approximation_stronglyMeasurable n).comp_measurable
    continuous_real_toNNReal.measurable

theorem target_sq_integrable (H : ℝ) :
    Integrable (fun t => ‖timeTarget t‖^2) (window H) :=
  (timeTarget_continuous.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem timeTarget_memLp (H : ℝ) : MemLp timeTarget 2 (window H) :=
  (memLp_two_iff_integrable_sq_norm
    timeTarget_continuous.stronglyMeasurable.aestronglyMeasurable).mpr
    (target_sq_integrable H)

theorem timeInput_memLp (n : ℕ) (H : ℝ) : MemLp (timeInput n) 2 (window H) := by
  apply (memLp_two_iff_integrable_sq_norm
    (timeInput_stronglyMeasurable n).aestronglyMeasurable).mpr
  apply (target_sq_integrable H).mono'
    (((timeInput_stronglyMeasurable n).norm.pow 2).aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    change ‖‖timeInput n t‖^2‖ ≤ ‖timeTarget t‖^2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (input_norm_le n t) 2

def timeClass (n : ℕ) (H : ℝ) : Lp JointL2 2 (window H) :=
  (timeInput_memLp n H).toLp (timeInput n)
def targetClass (H : ℝ) : Lp JointL2 2 (window H) :=
  (timeTarget_memLp H).toLp timeTarget

theorem timeClass_ae (n : ℕ) (H : ℝ) : timeClass n H =ᵐ[window H] timeInput n :=
  MemLp.coeFn_toLp _
theorem targetClass_ae (H : ℝ) : targetClass H =ᵐ[window H] timeTarget :=
  MemLp.coeFn_toLp _

private theorem error_bound (n : ℕ) (t : ℝ) :
    ‖timeInput n t - timeTarget t‖^2 ≤ 4*‖timeTarget t‖^2 := by
  have hn := norm_sub_le (timeInput n t) (timeTarget t)
  have hb := input_norm_le n t
  nlinarith [norm_nonneg (timeInput n t-timeTarget t),norm_nonneg (timeTarget t)]

theorem error_energy_tendsto (H : ℝ) :
    Tendsto (fun n => ∫ t, ‖timeInput n t-timeTarget t‖^2 ∂window H) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (F := fun n t => ‖timeInput n t-timeTarget t‖^2) (f := fun _ => (0:ℝ))
    (fun t => 4*‖timeTarget t‖^2)
    (fun n => by
      convert (((timeInput_stronglyMeasurable n).sub
        timeTarget_continuous.stronglyMeasurable).norm.pow 2).aestronglyMeasurable using 1)
    ((target_sq_integrable H).const_mul 4)
    (fun n => Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact error_bound n t)
    (Eventually.of_forall fun t => by
      have ht := ((actual_endpoint_tendsto t.toNNReal).sub_const
        (intrinsicCurve t.toNNReal : JointL2)).norm.pow 2
      simpa only [timeInput,timeTarget,sub_self,norm_zero,zero_pow (by norm_num : 2≠0)] using ht)
  simpa only [integral_zero] using h

private theorem error_norm_sq (n : ℕ) (H : ℝ) :
    ‖timeClass n H-targetClass H‖^2 = ∫ t, ‖timeInput n t-timeTarget t‖^2 ∂window H := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (timeClass n H) (targetClass H),timeClass_ae n H,targetClass_ae H]
    with t he hn ht
  rw [he]
  simp only [Pi.sub_apply,hn,ht,real_inner_self_eq_norm_sq]

theorem timeClass_tendsto (H : ℝ) : Tendsto (fun n => timeClass n H) atTop (𝓝 (targetClass H)) := by
  have hs : Tendsto (fun n => ‖timeClass n H-targetClass H‖^2) atTop (𝓝 0) := by
    simpa only [error_norm_sq] using error_energy_tendsto H
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Function.comp_def,dist_eq_norm,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hn

def timeSample (n : ℕ) (z : ℝ × IBMSourceLaws.JointSample) : ℝ :=
  sample n (z.1.toNNReal,z.2)
def timeValue (z : ℝ × IBMSourceLaws.JointSample) : ℝ :=
  IBMConstructedSources.ibmValue z.1.toNNReal z.2

theorem timeSample_stronglyMeasurable (n : ℕ) : StronglyMeasurable (timeSample n) :=
  (sample_stronglyMeasurable n).comp_measurable
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)

theorem timeValue_stronglyMeasurable : StronglyMeasurable timeValue :=
  (IBMConstructedSources.ibmValue_jointly_measurable.comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      measurable_snd)).stronglyMeasurable

def spaceTimeClass (n : ℕ) (H : ℝ) :
    Lp ℝ 2 ((window H).prod IBMSourceLaws.jointMeasure) :=
  (ProductL2Curry.curryEquiv (window H) IBMSourceLaws.jointMeasure).symm (timeClass n H)
def targetSpaceTimeClass (H : ℝ) :
    Lp ℝ 2 ((window H).prod IBMSourceLaws.jointMeasure) :=
  (ProductL2Curry.curryEquiv (window H) IBMSourceLaws.jointMeasure).symm (targetClass H)

theorem spaceTimeClass_ae (n : ℕ) (H : ℝ) :
    spaceTimeClass n H =ᵐ[(window H).prod IBMSourceLaws.jointMeasure] timeSample n := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (Lp.stronglyMeasurable (spaceTimeClass n H)).measurable
    (timeSample_stronglyMeasurable n).measurable)).mpr
  filter_upwards [ProductL2Curry.curryEquiv_symm_coeFn (window H) IBMSourceLaws.jointMeasure
    (timeClass n H),timeClass_ae n H] with t hc ht
  rw [ht] at hc
  exact hc.symm.trans (sample_ae n t.toNNReal)

theorem targetSpaceTimeClass_ae (H : ℝ) :
    targetSpaceTimeClass H =ᵐ[(window H).prod IBMSourceLaws.jointMeasure] timeValue := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (Lp.stronglyMeasurable (targetSpaceTimeClass H)).measurable
    timeValue_stronglyMeasurable.measurable)).mpr
  filter_upwards [ProductL2Curry.curryEquiv_symm_coeFn (window H) IBMSourceLaws.jointMeasure
    (targetClass H),targetClass_ae H] with t hc ht
  rw [ht] at hc
  exact hc.symm.trans (joint_point_actual_ae t.toNNReal)

theorem timeSample_memLp (n : ℕ) (H : ℝ) :
    MemLp (timeSample n) 2 ((window H).prod IBMSourceLaws.jointMeasure) :=
  (Lp.memLp (spaceTimeClass n H)).ae_eq (spaceTimeClass_ae n H)

theorem timeValue_memLp (H : ℝ) :
    MemLp timeValue 2 ((window H).prod IBMSourceLaws.jointMeasure) :=
  (Lp.memLp (targetSpaceTimeClass H)).ae_eq (targetSpaceTimeClass_ae H)

theorem sample_product_L2_tendsto (H : ℝ) :
    Tendsto (fun n => (timeSample_memLp n H).toLp (timeSample n)) atTop
      (𝓝 ((timeValue_memLp H).toLp timeValue)) := by
  have he (n : ℕ) : (timeSample_memLp n H).toLp (timeSample n) = spaceTimeClass n H := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (spaceTimeClass_ae n H).symm
  have ht : (timeValue_memLp H).toLp timeValue = targetSpaceTimeClass H := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp _).trans (targetSpaceTimeClass_ae H).symm
  simp only [he,ht]
  exact (ProductL2Curry.curryEquiv (window H) IBMSourceLaws.jointMeasure).symm.continuous
    |>.tendsto (targetClass H) |>.comp (timeClass_tendsto H)

theorem sample_product_error_tendsto (H : ℝ) :
    Tendsto (fun n => eLpNorm (timeSample n-timeValue) 2
      ((window H).prod IBMSourceLaws.jointMeasure)) atTop (𝓝 0) :=
  (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' timeSample (fun n => timeSample_memLp n H)
    timeValue (timeValue_memLp H)).mp (sample_product_L2_tendsto H)

theorem integratedSample_memLp (n : ℕ) (H : ℝ) :
    MemLp (fun ω => ∫ t, timeSample n (t,ω) ∂window H) 2 IBMSourceLaws.jointMeasure :=
  FiniteMeasureL2Integration.column_integral_memLp _ (timeSample_memLp n H)

theorem sample_columns_integrable (n : ℕ) (H : ℝ) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, Integrable (fun t => timeSample n (t,ω)) (window H) :=
  ((timeSample_memLp n H).integrable (by norm_num)).prod_left_ae

theorem value_columns_integrable (H : ℝ) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, Integrable (fun t => timeValue (t,ω)) (window H) :=
  ((timeValue_memLp H).integrable (by norm_num)).prod_left_ae

def integratedSampleClass (n : ℕ) (H : ℝ) : JointL2 :=
  (integratedSample_memLp n H).toLp (fun ω => ∫ t, timeSample n (t,ω) ∂window H)

theorem integratedSampleClass_eq (n : ℕ) (H : ℝ) :
    integratedSampleClass n H = ∫ t, timeInput n t ∂window H := by
  have hi : Integrable (timeInput n) (window H) := (timeInput_memLp n H).integrable (by norm_num)
  have he := BochnerL2RepresentativeFubini.integral_coeFn_ae (timeInput n) hi
    (timeSample n) (timeSample_stronglyMeasurable n).aestronglyMeasurable
    (Eventually.of_forall fun t => sample_ae n t.toNNReal)
  apply Lp.ext
  exact (MemLp.coeFn_toLp (integratedSample_memLp n H)).trans he.symm

theorem timeTarget_integral (H : ℝ) : (∫ t, timeTarget t ∂window H) = nativeAverage H := by
  rw [nativeAverage_eq_intrinsicAverage]
  exact IntrinsicSpace.subtypeL.integral_comp_comm (intrinsicCurve_integrable H)

theorem nativeAverage_ae_timeIntegral (H : ℝ) :
    nativeAverage H =ᵐ[IBMSourceLaws.jointMeasure] fun ω => ∫ t, timeValue (t,ω) ∂window H := by
  rw [← timeTarget_integral]
  exact BochnerL2RepresentativeFubini.integral_coeFn_ae timeTarget
    ((timeTarget_memLp H).integrable (by norm_num)) timeValue
    timeValue_stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall fun t => joint_point_actual_ae t.toNNReal)

theorem integratedSampleClass_tendsto (H : ℝ) :
    Tendsto (fun n => integratedSampleClass n H) atTop (𝓝 (nativeAverage H)) := by
  have h := tendsto_integral_of_dominated_convergence
    (μ := window H) (F := timeInput) (f := timeTarget) (fun t => ‖timeTarget t‖)
    (fun n => (timeInput_stronglyMeasurable n).aestronglyMeasurable)
    (timeTarget_continuous.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (fun n => Eventually.of_forall fun t => input_norm_le n t)
    (Eventually.of_forall fun t => actual_endpoint_tendsto t.toNNReal)
  simpa only [integratedSampleClass_eq,timeTarget_integral] using h

end OperatorDerivativeRewrite.Foundation.IBMPastTimeRealization
