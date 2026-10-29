import Foundation.FourCubeHaarProductCoordinates
import Foundation.FourCubeHaarQuadraticLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Dominated convergence for actual cutoff Haar densities at the fixed pinned cell. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeHaarLaplaceDensity
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open FourCubePinnedHaar FourCubePinnedCoercivity FourCubeHemisphereCoercivity
open FourCubeHaarProductCoordinates FourCubeHaarQuadraticLimit
open OneSidedPinnedInterior (Free)

def coordinateCutoff : Set Field := {Y | ∀ e : Free,chartRate (Y e) ≤ 2}

def scaledCutoff (t : ℝ) : Set Field := (fun Y : Field => t • Y) ⁻¹' coordinateCutoff

def scaledDensity (t : ℝ) : Field → ℝ := by
  classical
  exact (scaledCutoff t).indicator (fun Y => productDensity (t • Y)*Real.exp (-ray Y t/t^2))

def gaussianDensity (Y : Field) : ℝ := productDensity 0*Real.exp (-quadraticForm Y/2)

theorem chartDensity_continuous : Continuous chartDensity := by
  have hq : Continuous chartRate := by unfold chartRate; fun_prop
  exact continuous_const.div (continuous_const.mul (hq.pow 2)) (fun y => by
    have hh := chartRate_positive y
    have hp := Real.pi_pos
    positivity)

theorem chartDensity_positive (y : Triple) : 0 < chartDensity y := by
  unfold chartDensity
  have hq := chartRate_positive y
  have hp := Real.pi_pos
  positivity

theorem chartDensity_le_zero (y : Triple) : chartDensity y ≤ chartDensity 0 := by
  have hq := chartRate_ge_one y
  have hk : 0 < 2*Real.pi^2 := by positivity
  have hs : 1 ≤ (chartRate y)^2 := by nlinarith
  have hd := mul_le_mul_of_nonneg_left hs hk.le
  simp only [mul_one] at hd
  have hh := one_div_le_one_div_of_le hk hd
  simpa only [chartDensity,chartRate,Pi.zero_apply,zero_pow (by norm_num : 2 ≠ 0),
    add_zero,one_pow,mul_one] using hh

theorem productDensity_continuous : Continuous productDensity := by
  unfold productDensity
  exact continuous_finset_prod _ (fun e _ => chartDensity_continuous.comp (continuous_apply e))

theorem productDensity_positive (Y : Field) : 0 < productDensity Y :=
  Finset.prod_pos (fun e _ => chartDensity_positive (Y e))

theorem productDensity_le_zero (Y : Field) : productDensity Y ≤ productDensity 0 := by
  apply Finset.prod_le_prod₀
  · intro e _
    exact chartDensity_nonneg (Y e)
  · intro e _
    exact chartDensity_le_zero (Y e)

theorem coordinateCutoff_measurable : MeasurableSet coordinateCutoff := by
  rw [show coordinateCutoff=chartField ⁻¹' localStateDomain from cutoff_preimage.symm]
  exact localStateDomain_measurable.preimage chartField_measurable

theorem scaledCutoff_measurable (t : ℝ) : MeasurableSet (scaledCutoff t) :=
  coordinateCutoff_measurable.preimage
    ((continuous_const_smul t : Continuous (fun Y : Field => t • Y)).measurable)

theorem eventually_scaledCutoff (Y : Field) : ∀ᶠ t : ℝ in 𝓝 0,Y∈scaledCutoff t := by
  have he (e : Free) : ∀ᶠ t : ℝ in 𝓝 0,chartRate (t • Y e) ≤ 2 := by
    have hc : Continuous (fun t : ℝ => chartRate (t • Y e)) := by
      unfold chartRate
      fun_prop
    have hh := hc.continuousAt.tendsto.eventually (eventually_lt_nhds (show chartRate ((0 : ℝ) • Y e)<2 by norm_num [chartRate]))
    exact hh.mono (fun t ht => ht.le)
  simpa only [scaledCutoff,Set.mem_preimage,coordinateCutoff,Set.mem_setOf_eq,Pi.smul_apply]
    using eventually_all.mpr he

theorem scaledDensity_measurable (t : ℝ) : Measurable (scaledDensity t) := by
  have hm : Measurable (fun Y : Field => t • Y) :=
    (continuous_const_smul t : Continuous (fun Y : Field => t • Y)).measurable
  have hr : Measurable (fun Y : Field => ray Y t) :=
    pinnedAction_measurable.comp (chartField_measurable.comp hm)
  exact ((productDensity_measurable.comp hm).mul ((hr.neg.div_const (t^2)).exp)).indicator
    (scaledCutoff_measurable t)

theorem scaledDensity_nonneg (t : ℝ) (Y : Field) : 0 ≤ scaledDensity t Y := by
  classical
  unfold scaledDensity
  by_cases h : Y∈scaledCutoff t
  · rw [Set.indicator_of_mem h]
    exact mul_nonneg (productDensity_nonneg _) (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem h]

theorem scaledDensity_bound (t : ℝ) (ht : t ≠ 0) (Y : Field) :
    scaledDensity t Y ≤ productDensity 0*Real.exp (-quadraticMass Y/372) := by
  classical
  unfold scaledDensity
  by_cases h : Y∈scaledCutoff t
  · rw [Set.indicator_of_mem h]
    have hp : 0 ≤ 1/t^2 := by positivity
    have hc : (1/t^2)*t^2=1 := by field_simp
    have he := scaled_boltzmann_domination (1/t^2) t hp hc Y h
    have he' : Real.exp (-ray Y t/t^2) ≤ Real.exp (-quadraticMass Y/372) := by
      convert! he using 1
      congr 1
      simp only [ray]
      ring
    exact mul_le_mul (productDensity_le_zero _) he' (Real.exp_pos _).le (productDensity_nonneg _)
  · rw [Set.indicator_of_notMem h]
    exact mul_nonneg (productDensity_nonneg _) (Real.exp_pos _).le

theorem scaledDensity_tendsto (Y : Field) :
    Tendsto (fun t : ℝ => scaledDensity t Y) (𝓝[≠] 0) (𝓝 (gaussianDensity Y)) := by
  have hp : Tendsto (fun t : ℝ => productDensity (t • Y)) (𝓝[≠] 0) (𝓝 (productDensity 0)) := by
    have hs : Continuous (fun t : ℝ => t • Y) := continuous_id.smul continuous_const
    have hh := (productDensity_continuous.comp hs).tendsto (0 : ℝ)
    simpa only [Function.comp_def,zero_smul] using hh.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hh := hp.mul (boltzmann_quadratic_limit Y)
  apply hh.congr'
  filter_upwards [(eventually_scaledCutoff Y).filter_mono nhdsWithin_le_nhds] with t ht
  change _=(scaledCutoff t).indicator
    (fun Z => productDensity (t • Z)*Real.exp (-ray Z t/t^2)) Y
  rw [Set.indicator_of_mem ht]

theorem gaussianDensity_bound (Y : Field) :
    gaussianDensity Y ≤ productDensity 0*Real.exp (-quadraticMass Y/372) := by
  apply le_of_tendsto (scaledDensity_tendsto Y)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact scaledDensity_bound t ht Y

theorem gaussianDensity_integrable : Integrable gaussianDensity := by
  have hm : Measurable gaussianDensity := by
    unfold gaussianDensity quadraticForm Matrix.mulVec dotProduct
    fun_prop
  apply (gaussian_envelope_integrable.const_mul (productDensity 0)).mono' hm.aestronglyMeasurable
  filter_upwards with Y
  have hp : 0 < gaussianDensity Y := mul_pos (productDensity_positive 0) (Real.exp_pos _)
  rw [Real.norm_eq_abs,abs_of_pos hp]
  exact gaussianDensity_bound Y

theorem gaussianDensity_integral_positive : 0 < ∫ Y : Field,gaussianDensity Y := by
  have he : (∫ Y : Field,gaussianDensity Y)=
      productDensity 0*(∫ Y : Field,Real.exp (-quadraticForm Y/2)) := integral_const_mul _ _
  have hi : Integrable (fun Y : Field => Real.exp (-quadraticForm Y/2)) := by
    have hh := gaussianDensity_integrable.const_mul ((productDensity 0)⁻¹)
    convert! hh using 1
    funext Y
    simp [gaussianDensity,← mul_assoc,(productDensity_positive 0).ne']
  rw [he]
  exact mul_pos (productDensity_positive 0) (integral_exp_pos hi)

theorem scaledDensity_integral_tendsto :
    Tendsto (fun t : ℝ => ∫ Y : Field,scaledDensity t Y) (𝓝[≠] 0)
      (𝓝 (∫ Y : Field,gaussianDensity Y)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun Y : Field => productDensity 0*Real.exp (-quadraticMass Y/372))
  · exact Filter.Eventually.of_forall (fun t => (scaledDensity_measurable t).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards with Y
    rw [Real.norm_eq_abs,abs_of_nonneg (scaledDensity_nonneg t Y)]
    exact scaledDensity_bound t ht Y
  · exact gaussian_envelope_integrable.const_mul _
  · exact ae_of_all _ scaledDensity_tendsto


theorem scaledDensity_integrable (t : ℝ) (ht : t ≠ 0) : Integrable (scaledDensity t) := by
  apply (gaussian_envelope_integrable.const_mul (productDensity 0)).mono'
    (scaledDensity_measurable t).aestronglyMeasurable
  filter_upwards with Y
  rw [Real.norm_eq_abs,abs_of_nonneg (scaledDensity_nonneg t Y)]
  exact scaledDensity_bound t ht Y

theorem bounded_test_integral_tendsto (f : Field → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ Y,|f Y| ≤ M) :
    Tendsto (fun t : ℝ => ∫ Y : Field,f Y*scaledDensity t Y) (𝓝[≠] 0)
      (𝓝 (∫ Y : Field,f Y*gaussianDensity Y)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun Y : Field => M*(productDensity 0*Real.exp (-quadraticMass Y/372)))
  · exact Filter.Eventually.of_forall (fun t =>
      (hf.mul (scaledDensity_measurable t)).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards with Y
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (scaledDensity_nonneg t Y)]
    exact mul_le_mul (hbound Y) (scaledDensity_bound t ht Y) (scaledDensity_nonneg t Y) hM
  · exact (gaussian_envelope_integrable.const_mul (productDensity 0)).const_mul M
  · exact ae_of_all _ (fun Y => (scaledDensity_tendsto Y).const_mul (f Y))

theorem normalized_bounded_test_tendsto (f : Field → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ Y,|f Y| ≤ M) :
    Tendsto (fun t : ℝ => (∫ Y : Field,f Y*scaledDensity t Y)/(∫ Y : Field,scaledDensity t Y))
      (𝓝[≠] 0) (𝓝 ((∫ Y : Field,f Y*gaussianDensity Y)/(∫ Y : Field,gaussianDensity Y))) :=
  (bounded_test_integral_tendsto f hf M hM hbound).div scaledDensity_integral_tendsto
    gaussianDensity_integral_positive.ne'

end OperatorDerivativeRewrite.Foundation.FourCubeHaarLaplaceDensity
