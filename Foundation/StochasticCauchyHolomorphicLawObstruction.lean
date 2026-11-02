import Foundation.StochasticCauchyAnalyticMartingale
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyHolomorphicLawObstruction
open InfiniteGaussian StochasticCauchyExitOccupation StochasticCauchyExitMoments
open StochasticCauchyBrownianRealization StochasticCauchyGaussianNormalization
private abbrev μ := gaussianProduct.prod gaussianProduct

theorem exit_second_moment (R : ℝ) (hR : 0≤R) : (∫ w,‖exitValue R w‖^2 ∂μ)=R^2 := by
  calc
    _ = ∫ _ : SampleSpace × SampleSpace,R^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [exitValue_boundary R hR] with w hw
      rw [hw]
    _ = _ := by simp

theorem brownian_second_moment (T : ℝ≥0) : (∫ w,‖value T w‖^2 ∂μ)=2*(T:ℝ) := by
  have hb := (value_hasLaw T).integral_comp (f := fun z : ℂ => ‖z‖^2) (by fun_prop)
  have hz := (hasLaw_z T).integral_comp (f := fun z : ℂ => ‖z‖^2) (by fun_prop)
  exact hb.trans (hz.symm.trans (z_second_moment T))

/-- ALL pure complex polynomial moments agree, not just first chaos. -/
theorem polynomial_means_match (R : ℝ) (hR : 0≤R) (T : ℝ≥0) (p : Polynomial ℂ) :
    (∫ w,p.eval (exitValue R w) ∂μ)=(∫ w,p.eval (value T w) ∂μ) :=
  (exit_polynomial_mean p R hR).trans (polynomialProcess_mean p T).symm

/-- Actual measurable-law obstruction; no appeal to a named distribution. -/
theorem exit_not_brownian_law (R : ℝ) (hR : 0≤R) (T : ℝ≥0) (he : R^2≠2*(T:ℝ)) :
    μ.map (exitValue R)≠μ.map (value T) := by
  intro h
  have hi : (∫ z : ℂ,‖z‖^2 ∂μ.map (exitValue R))=∫ w,‖exitValue R w‖^2 ∂μ :=
    integral_map (exitValue_measurable R).aemeasurable (by fun_prop)
  have hb : (∫ z : ℂ,‖z‖^2 ∂μ.map (value T))=∫ w,‖value T w‖^2 ∂μ :=
    integral_map (value_measurable T).aemeasurable (by fun_prop)
  rw [h] at hi
  have hh := hi.symm.trans hb
  rw [exit_second_moment R hR,brownian_second_moment T] at hh
  exact he hh

theorem distinct_exit_laws (R S : ℝ) (hR : 0≤R) (hS : 0≤S) (he : R^2≠S^2) :
    μ.map (exitValue R)≠μ.map (exitValue S) := by
  intro h
  have hr : (∫ z : ℂ,‖z‖^2 ∂μ.map (exitValue R))=∫ w,‖exitValue R w‖^2 ∂μ :=
    integral_map (exitValue_measurable R).aemeasurable (by fun_prop)
  have hs : (∫ z : ℂ,‖z‖^2 ∂μ.map (exitValue S))=∫ w,‖exitValue S w‖^2 ∂μ :=
    integral_map (exitValue_measurable S).aemeasurable (by fun_prop)
  rw [h] at hr
  have hh := hr.symm.trans hs
  rw [exit_second_moment R hR,exit_second_moment S hS] at hh
  exact he hh

theorem entire_exit_memLp (f : ℂ → ℂ) (hf : Differentiable ℂ f) (R : ℝ≥0) :
    MemLp (fun w => f (exitValue R w)) 2 μ := by
  have hp := StochasticCauchyAnalyticDisk.exit_sample_memLp f R (R+1) (lt_add_one R) hf.differentiableOn
  apply (hp.add (memLp_const (f 0))).ae_eq
  filter_upwards [] with w
  change (f (exitValue R w)-f 0)+f 0=f (exitValue R w)
  exact sub_add_cancel _ _

/-- Even ALL ENTIRE test functions fail to separate these compact exit laws;
all their actual sampled integrability domains are derived above. -/
theorem entire_exit_mean (f : ℂ → ℂ) (hf : Differentiable ℂ f) (R : ℝ≥0) :
    (∫ w,f (exitValue R w) ∂μ)=f 0 := by
  have hm := StochasticCauchyAnalyticDisk.exitIntegral_mean_zero f R (R+1) (lt_add_one R) hf.differentiableOn
  have hi := integral_congr_ae (StochasticCauchyAnalyticDisk.exitIntegral_actual f R (R+1) (lt_add_one R) hf.differentiableOn)
  have hz : (∫ w,f (exitValue R w)-f 0 ∂μ)=0 := hi.symm.trans hm
  rw [integral_sub ((entire_exit_memLp f hf R).integrable (by norm_num)) (integrable_const (f 0))] at hz
  simpa using sub_eq_zero.mp hz

theorem entire_tests_do_not_determine_law :
    (∀ f : ℂ → ℂ,Differentiable ℂ f →
      (∫ w,f (exitValue 1 w) ∂μ)=(∫ w,f (exitValue 2 w) ∂μ)) ∧
      μ.map (exitValue 1)≠μ.map (exitValue 2) := by
  constructor
  · intro f hf
    simpa only [NNReal.coe_one,NNReal.coe_ofNat] using (entire_exit_mean f hf 1).trans (entire_exit_mean f hf 2).symm
  · exact distinct_exit_laws 1 2 (by norm_num) (by norm_num) (by norm_num)

/-- The ACTUAL stopped path already fails the time-one Brownian marginal.
All holomorphic stopped-martingale theorems remain valid: clock data matter. -/
theorem stopped_unit_not_brownian :
    μ.map (fun w => value (StochasticCauchyExitClock.clippedClock 1 (StochasticCauchyExitClock.exitTime 1) w) w)≠μ.map (value 1) := by
  let F := fun w => value (StochasticCauchyExitClock.clippedClock 1 (StochasticCauchyExitClock.exitTime 1) w) w
  have hm : MemLp F 2 μ := StochasticCauchyExitClock.stopped_memLp 1 _ (StochasticCauchyExitClock.exitTime_stopping 1)
  have hb : ∀ᵐ w ∂μ,‖F w‖^2≤(1:ℝ) := by
    filter_upwards [StochasticCauchyExitClock.exit_bounded_ae 1 (by norm_num) 1] with w hw
    dsimp only [F]
    nlinarith [norm_nonneg (value (StochasticCauchyExitClock.clippedClock 1 (StochasticCauchyExitClock.exitTime 1) w) w)]
  have hmeas : AEStronglyMeasurable (fun w => ‖F w‖^2) μ := by
    have hh := hm.aestronglyMeasurable
    fun_prop
  have hi : Integrable (fun w => ‖F w‖^2) μ :=
    (integrable_const (1:ℝ)).mono' hmeas (hb.mono fun w hw => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (‖F w‖))] using hw)
  have he : (∫ w,‖F w‖^2 ∂μ)≤1 := by
    simpa using integral_mono_ae hi (integrable_const (1:ℝ)) hb
  intro h
  have hF : (∫ z : ℂ,‖z‖^2 ∂μ.map F)=∫ w,‖F w‖^2 ∂μ :=
    integral_map hm.aemeasurable (by fun_prop)
  have hB : (∫ z : ℂ,‖z‖^2 ∂μ.map (value 1))=∫ w,‖value 1 w‖^2 ∂μ :=
    integral_map (value_measurable 1).aemeasurable (by fun_prop)
  rw [h] at hF
  have hh := hF.symm.trans hB
  rw [brownian_second_moment] at hh
  norm_num at hh
  linarith

/-- A constructed continuous/UI martingale on the original filtration is NOT
Brownian at the unchanged clock, despite the entire holomorphic calculus. -/
theorem identity_process_not_brownian :
    μ.map (StochasticCauchyAnalyticMartingale.process (fun z => z) 1 2 (by norm_num) differentiableOn_id 1)≠μ.map (value 1) := by
  intro h
  have hp := (StochasticCauchyAnalyticMartingale.process_spec (fun z => z) 1 2 (by norm_num) differentiableOn_id).2.2.1 1
  have he : μ.map (StochasticCauchyAnalyticMartingale.process (fun z => z) 1 2 (by norm_num) differentiableOn_id 1)=
      μ.map (fun w => value (StochasticCauchyExitClock.clippedClock 1 (StochasticCauchyExitClock.exitTime (↑(1:ℝ≥0))) w) w) := Measure.map_congr hp
  apply stopped_unit_not_brownian
  simpa only [NNReal.coe_one] using he.symm.trans h

end OperatorDerivativeRewrite.Foundation.StochasticCauchyHolomorphicLawObstruction
