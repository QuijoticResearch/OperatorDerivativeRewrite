import Foundation.VolterraRandomStepDrift
import Foundation.GaussianBrownianPRP
import Foundation.GaussianLipschitzIntegrands

/-! The random Volterra drift inside the actual raw Brownian predictable/PRP spaces. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianRandomStepDrift
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianTimeProductL2
  GaussianPredictableFull GaussianPredictableAdjoint GaussianLipschitzIntegrands
  GaussianBrownianGeneratedSpace GaussianBrownianPRP VolterraRandomStepDrift
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

def A : GaussianL2 := valueL2 Real.lipschitzWith_sin 1

def actualDrift : GaussianL2 := -A

theorem A_coeFn : A=ᵐ[gaussianProduct] fun ω => Real.sin (process 1 ω) :=
  valueL2_coeFn Real.lipschitzWith_sin 1

theorem A_past : AEStronglyMeasurable[naturalFiltration 1] A gaussianProduct :=
  valueL2_past Real.lipschitzWith_sin 1

def thetaField : fullPredictable :=
  ⟨productTensor (intervalVector 1 2) A,past_step_mem_fullPredictable 1 2 A A_past⟩

theorem thetaField_coeFn : (thetaField : TimeProbabilityL2)=ᵐ[timeProbability]
    fun z => rawTheta process z.1 z.2 := by
  have ht := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn 1 2)
  have ha := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp A_coeFn
  filter_upwards [productTensor_coeFn (intervalVector 1 2) A,ht,ha] with z hp ht ha
  change productTensor (intervalVector 1 2) A z=_
  simp only [Function.comp_apply] at ht ha
  rw [hp,ht,ha]
  by_cases hz : z.1∈Ioc (1 : ℝ) 2 <;> simp [rawTheta,coefficient,hz]

theorem theta_predictable : IsStronglyPredictable naturalFiltration (theta process) := by
  exact VolterraRandomStepDrift.theta_predictable process (fun t => (process_stronglyMeasurable t).measurable)

theorem stochastic_integral_value : itoIntegral thetaField=ᵐ[gaussianProduct]
    fun ω => Real.sin (process 1 ω)*(process 2 ω-process 1 ω) := by
  filter_upwards [itoIntegral_past_step 1 2 (by norm_num) A A_past,A_coeFn] with ω hi ha
  change itoIntegral thetaField ω=_ at hi
  rw [hi,ha]

theorem actualDrift_coeFn : actualDrift=ᵐ[gaussianProduct] fun ω => -Real.sin (process 1 ω) := by
  filter_upwards [Lp.coeFn_neg A,A_coeFn] with ω hn ha
  change (-A) ω=_
  rw [hn,Pi.neg_apply,ha]

theorem actualDrift_integral_value : actualDrift=ᵐ[gaussianProduct] drift process 2 := by
  filter_upwards [actualDrift_coeFn] with ω hω
  rw [drift_two]
  exact hω

theorem actualDrift_brownian : actualDrift∈brownianL2 := by
  have hm : Measurable[brownianSigma] (fun ω => -Real.sin (process 1 ω)) :=
    (Real.measurable_sin.comp (process_brownian_measurable 1)).neg
  exact hm.stronglyMeasurable.aestronglyMeasurable.congr actualDrift_coeFn.symm

theorem actualDrift_not_deterministic : ¬∃ c : ℝ, actualDrift=c • gaussianOne := by
  rintro ⟨c,hc⟩
  apply actual_drift_not_constant c
  filter_upwards [actualDrift_integral_value,Lp.coeFn_smul c gaussianOne,gaussianOne_coeFn]
    with ω hv hs ho
  rw [hc,hs,Pi.smul_apply,ho,smul_eq_mul,mul_one] at hv
  exact hv.symm

theorem actual_variance_positive : 0<Var[drift process 2; gaussianProduct] :=
  drift_variance_positive process (fun t => (process_stronglyMeasurable t).measurable) (process_hasLaw 1)

theorem actual_novikov_integrable :
    Integrable (fun ω => Real.exp ((∫ s in (0 : ℝ)..2, rawTheta process s ω^2)/2)) gaussianProduct :=
  novikov_integrable process (fun t => (process_stronglyMeasurable t).measurable)

theorem actualDrift_representation : ∃! U : fullPredictable,
    itoIntegral U=actualDrift-(∫ ω, actualDrift ω ∂gaussianProduct) • gaussianOne :=
  brownian_representation_exists_unique actualDrift actualDrift_brownian

end OperatorDerivativeRewrite.Foundation.GaussianRandomStepDrift
