import Foundation.GaussianCriticalExponential

/-! An unbounded predictable delayed step with normalized terminal likelihood and failed Novikov. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianUnboundedDelayedStep
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianTimeProductL2
  GaussianPredictableFull GaussianPredictableAdjoint GaussianPredictableStep
  GaussianCriticalExponential
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def evaluation : (Iic (1 : ℝ≥0) → ℝ) → ℝ := fun z => z ⟨1, by simp⟩

def theta : ℝ≥0 → SampleSpace → ℝ := stepProcess process 1 2 evaluation

def rawTheta (s : ℝ) (ω : SampleSpace) : ℝ :=
  (Ioc (1 : ℝ) 2).indicator (fun _ => process 1 ω) s

theorem evaluation_measurable : Measurable evaluation := measurable_pi_apply _

theorem theta_predictable : IsStronglyPredictable naturalFiltration theta :=
  stepProcess_stronglyPredictable (fun t => (process_stronglyMeasurable t).measurable)
    1 2 evaluation_measurable

theorem theta_eq_raw (t : ℝ≥0) (ω : SampleSpace) : theta t ω = rawTheta t ω := by
  have hm : t ∈ Ioc (1 : ℝ≥0) 2 ↔ (t : ℝ) ∈ Ioc (1 : ℝ) 2 := by
    simp only [mem_Ioc]
    norm_cast
  by_cases h : t ∈ Ioc (1 : ℝ≥0) 2
  · simp [theta, stepProcess, pastCoefficient, pastProcess, evaluation, rawTheta, h, hm.mp h]
  · have hn : (t : ℝ) ∉ Ioc (1 : ℝ) 2 := fun ht => h (hm.mpr ht)
    simp [theta, stepProcess, rawTheta, h, hn]

theorem observation_not_essentially_bounded (C : ℝ) :
    ¬ ∀ᵐ ω ∂gaussianProduct, |process 1 ω| ≤ C := by
  intro h
  apply actual_critical_not_integrable
  apply (integrable_const (Real.exp (C^2/2))).mono'
    (critical_measurable.comp (process_stronglyMeasurable 1).measurable).aestronglyMeasurable
  filter_upwards [h] with ω hω
  have hC : 0 ≤ C := (abs_nonneg (process 1 ω)).trans hω
  have hs : (process 1 ω)^2 ≤ C^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (process 1 ω)) hC).mpr hω
  change ‖critical (process 1 ω)‖ ≤ Real.exp (C^2/2)
  rw [Real.norm_eq_abs, abs_of_pos (critical_positive _)]
  exact Real.exp_le_exp.mpr (by linarith)

theorem energy_two (ω : SampleSpace) :
    (∫ s in (0 : ℝ)..2, rawTheta s ω ^ 2) = process 1 ω ^ 2 := by
  have he : (fun s : ℝ => rawTheta s ω ^ 2) =
      (Ioc (1 : ℝ) 2).indicator (fun _ => process 1 ω ^ 2) := by
    funext s
    by_cases h : s ∈ Ioc (1 : ℝ) 2 <;> simp [rawTheta, h]
  rw [he, VolterraRandomStepDrift.integral_step]

theorem energy_integral :
    (∫ ω, (∫ s in (0 : ℝ)..2, rawTheta s ω ^ 2) ∂gaussianProduct) = 1 := by
  simp_rw [energy_two]
  have h := process_product_integral 1 1
  simpa only [pow_two, min_self, NNReal.coe_one] using h

theorem observation_past :
    AEStronglyMeasurable[naturalFiltration 1] (wienerL2 1) gaussianProduct :=
  (process_stronglyAdapted 1).aestronglyMeasurable

def thetaField : fullPredictable :=
  ⟨productTensor (intervalVector 1 2) (wienerL2 1),
    past_step_mem_fullPredictable 1 2 (wienerL2 1) observation_past⟩

theorem thetaField_coeFn : (thetaField : TimeProbabilityL2) =ᵐ[timeProbability]
    fun z => rawTheta z.1 z.2 := by
  have ht := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn 1 2)
  filter_upwards [productTensor_coeFn (intervalVector 1 2) (wienerL2 1), ht] with z hp ht
  change productTensor (intervalVector 1 2) (wienerL2 1) z = _
  simp only [Function.comp_apply] at ht
  rw [hp, ht]
  by_cases hz : z.1 ∈ Ioc (1 : ℝ) 2 <;> simp [rawTheta, process, hz]

theorem stochastic_integral_value : itoIntegral thetaField =ᵐ[gaussianProduct]
    fun ω => process 1 ω * (process 2 ω-process 1 ω) := by
  have h := itoIntegral_past_step 1 2 (by norm_num) (wienerL2 1) observation_past
  exact h

theorem density_terminal_form : linearDensity =ᵐ[gaussianProduct] fun ω =>
    Real.exp (-itoIntegral thetaField ω - (∫ s in (0 : ℝ)..2, rawTheta s ω ^ 2)/2) := by
  filter_upwards [stochastic_integral_value] with ω hω
  rw [hω, energy_two]
  simp only [linearDensity, GaussianRandomDensityKernel.kernel, neg_mul]

theorem novikov_not_integrable :
    ¬ Integrable (fun ω => Real.exp ((∫ s in (0 : ℝ)..2, rawTheta s ω ^ 2)/2))
      gaussianProduct := by
  simp_rw [energy_two]
  exact actual_critical_not_integrable

theorem likelihood_normalized :
    (∫⁻ ω, ENNReal.ofReal
      (Real.exp (-itoIntegral thetaField ω - (∫ s in (0 : ℝ)..2, rawTheta s ω ^ 2)/2))
      ∂gaussianProduct) = 1 := by
  rw [← linearDensity_normalized]
  apply lintegral_congr_ae
  exact density_terminal_form.symm.fun_comp ENNReal.ofReal

end OperatorDerivativeRewrite.Foundation.GaussianUnboundedDelayedStep
