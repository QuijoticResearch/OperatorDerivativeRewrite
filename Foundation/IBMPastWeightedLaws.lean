import Foundation.IBMPastEndpointCore
import Foundation.IBMFiniteWeightedLaws

/-! Finite positive weighted laws in the actual IBM past: no Gaussian IBM law. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPastWeightedLaws
open InfiniteGaussian IBMTimeAveragedObservable IBMPastAverageCore
open IBMFiniteWeightedLaws
set_option backward.isDefEq.respectTransparency false

theorem annihilator_point_fourier_moments {I : Type*} [Fintype I]
    (T : ℝ≥0) (H : JointL2) (hH : H ∈ (pastCore T)ᗮ) (w t : I → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hT : ∀ i, t i ≤ T) :
    (∫ ω, H ω * Real.cos (∑ i, w i * IBMConstructedSources.ibmValue (t i).toNNReal ω)
      ∂IBMSourceLaws.jointMeasure) = 0 ∧
    (∫ ω, H ω * Real.sin (∑ i, w i * IBMConstructedSources.ibmValue (t i).toNNReal ω)
      ∂IBMSourceLaws.jointMeasure) = 0 := by
  have hHc : H ∈ (pastCore T).topologicalClosureᗮ := by
    rwa [Submodule.orthogonal_closure]
  have htest (v : IBMSourceLaws.JointSample → ℝ)
      (hv : ∃ F : JointL2, F ∈ (pastCore T).topologicalClosure ∧
        F =ᵐ[IBMSourceLaws.jointMeasure] v) :
      (∫ ω, H ω * v ω ∂IBMSourceLaws.jointMeasure) = 0 := by
    obtain ⟨F, hf, ha⟩ := hv
    have hz := (pastCore T).topologicalClosure.inner_left_of_mem_orthogonal hf hHc
    rw [L2.inner_def] at hz
    calc
      _ = ∫ ω, inner ℝ (H ω) (F ω) ∂IBMSourceLaws.jointMeasure := by
        apply integral_congr_ae
        filter_upwards [ha] with ω hω
        rw [hω]
        simp [RCLike.inner_apply, mul_comm]
      _ = 0 := hz
  constructor
  · apply htest
    exact IBMPastEndpointCore.point_cylinder_closure T w t ht hT Real.cos (fun x => -Real.sin x)
      Real.hasDerivAt_cos Real.continuous_sin.neg 1 1
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x)
      (fun x => by simpa only [norm_neg, Real.norm_eq_abs] using Real.abs_sin_le_one x)
  · apply htest
    exact IBMPastEndpointCore.point_cylinder_closure T w t ht hT Real.sin Real.cos
      Real.hasDerivAt_sin Real.continuous_cos 1 1
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x)

theorem annihilator_finite_weighted_laws {I : Type*} [Fintype I]
    (T : ℝ≥0) (H : JointL2) (hH : H ∈ (pastCore T)ᗮ) (t : I → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hT : ∀ i, t i ≤ T) :
    (IBMSourceLaws.jointMeasure.withDensity (fun ω => ENNReal.ofReal (H ω))).map
      (pointObservation t) =
      (IBMSourceLaws.jointMeasure.withDensity (fun ω => ENNReal.ofReal (-H ω))).map
        (pointObservation t) := by
  have hi : Integrable H IBMSourceLaws.jointMeasure := (Lp.memLp H).integrable (by simp)
  let μ := IBMSourceLaws.jointMeasure.withDensity (fun ω => ENNReal.ofReal (H ω))
  let ν := IBMSourceLaws.jointMeasure.withDensity (fun ω => ENNReal.ofReal (-H ω))
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hi.neg.hasFiniteIntegral
  apply finite_measure_eq_of_cos_sin
  · intro w
    rw [integral_map (pointObservation_measurable t).aemeasurable (by fun_prop),
      integral_map (pointObservation_measurable t).aemeasurable (by fun_prop)]
    apply weighted_integral_balance _ H _ (Lp.stronglyMeasurable H).measurable hi
      (((Real.continuous_cos.comp (continuous_id.inner continuous_const)).measurable.comp
        (pointObservation_measurable t)).aestronglyMeasurable) 1
      (ae_of_all _ (fun ω => by
        change |Real.cos (inner ℝ (pointObservation t ω) w)| ≤ 1
        exact Real.abs_cos_le_one _))
    convert (annihilator_point_fourier_moments T H hH (fun i => w i) t ht hT).1 using 1
    simp [Function.comp_def, pointObservation, PiLp.inner_apply, mul_comm]
  · intro w
    rw [integral_map (pointObservation_measurable t).aemeasurable (by fun_prop),
      integral_map (pointObservation_measurable t).aemeasurable (by fun_prop)]
    apply weighted_integral_balance _ H _ (Lp.stronglyMeasurable H).measurable hi
      (((Real.continuous_sin.comp (continuous_id.inner continuous_const)).measurable.comp
        (pointObservation_measurable t)).aestronglyMeasurable) 1
      (ae_of_all _ (fun ω => by
        change |Real.sin (inner ℝ (pointObservation t ω) w)| ≤ 1
        exact Real.abs_sin_le_one _))
    convert (annihilator_point_fourier_moments T H hH (fun i => w i) t ht hT).2 using 1
    simp [Function.comp_def, pointObservation, PiLp.inner_apply, mul_comm]

/-- Actual set integrals of the annihilator vanish on every finite nonnegative-time
IBM observation event. This is stronger than just vanishing Fourier moments. -/
theorem annihilator_finite_event {I : Type*} [Fintype I]
    (T : ℝ≥0) (H : JointL2) (hH : H ∈ (pastCore T)ᗮ) (t : I → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hT : ∀ i, t i ≤ T)
    (S : Set (EuclideanSpace ℝ I)) (hS : MeasurableSet S) :
    (∫ ω in pointObservation t ⁻¹' S, H ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  have hi : Integrable H IBMSourceLaws.jointMeasure := (Lp.memLp H).integrable (by simp)
  let v : IBMSourceLaws.JointSample → ℝ := fun ω =>
    S.indicator (fun _ => (1 : ℝ)) (pointObservation t ω)
  have htest : Measurable (S.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hS
  have hv : Measurable v := htest.comp (pointObservation_measurable t)
  have hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖v ω‖ ≤ 1 := ae_of_all _ fun ω => by
    by_cases h : pointObservation t ω ∈ S <;> simp [v, h]
  have heq : (∫ ω, v ω ∂IBMSourceLaws.jointMeasure.withDensity (fun ω => ENNReal.ofReal (H ω))) =
      ∫ ω, v ω ∂IBMSourceLaws.jointMeasure.withDensity (fun ω => ENNReal.ofReal (-H ω)) := by
    have ha := congrArg (fun ρ : Measure (EuclideanSpace ℝ I) =>
      ∫ y, S.indicator (fun _ => (1 : ℝ)) y ∂ρ)
      (annihilator_finite_weighted_laws T H hH t ht hT)
    rw [integral_map (pointObservation_measurable t).aemeasurable htest.aestronglyMeasurable,
      integral_map (pointObservation_measurable t).aemeasurable htest.aestronglyMeasurable] at ha
    exact ha
  have hz : (∫ ω, H ω * v ω ∂IBMSourceLaws.jointMeasure) = 0 := by
    rw [← weighted_integral_difference _ H v (Lp.stronglyMeasurable H).measurable hi
      hv.aestronglyMeasurable 1 hb, heq, sub_self]
  rw [← integral_indicator (hS.preimage (pointObservation_measurable t))]
  convert hz using 1
  congr 1
  funext ω
  by_cases h : pointObservation t ω ∈ S <;> simp [v, h]

end OperatorDerivativeRewrite.Foundation.IBMPastWeightedLaws
