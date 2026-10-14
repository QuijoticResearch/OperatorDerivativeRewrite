import Foundation.FractionalBrownianPredictionBenchmark
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A concrete actual fractional full-past forecast requires more than the current value. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.FractionalCurrentObservationObstruction
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection

theorem source_projection_single (u v : CoefficientSpace) :
    sourceProjection (fun _ : Unit => v) u=(inner ℝ v u/‖v‖^2) • v := by
  have hr : Set.range (fun _ : Unit => v)={v} := by ext x; simp
  have hc : (Submodule.span ℝ {v}).topologicalClosure=Submodule.span ℝ {v} :=
    (Submodule.closed_of_finiteDimensional (Submodule.span ℝ {v})).submodule_topologicalClosure_eq
  change ((Submodule.span ℝ (Set.range (fun _ : Unit => v))).topologicalClosure).starProjection u=_
  simp [hr,hc,Submodule.starProjection_singleton]

def direction (t : ℝ≥0) : CoefficientSpace :=
  FractionalGaussianProcess.direction (1/4) (by norm_num) (by norm_num) t

def past : Set.Iic (2 : ℝ≥0) → CoefficientSpace :=
  FractionalPredictionObstruction.pastDirections (1/4) (by norm_num) (by norm_num) 2

def terminal : GaussianL2 := firstChaosEmbedding (direction 4)

def fullForecast : GaussianL2 := conditionalProjection past terminal

def currentForecast : GaussianL2 := conditionalProjection (fun _ : Unit => direction 2) terminal

theorem covariance_quarter (s t : ℝ) :
    FractionalSpectralGeometry.covariance (1/4) s t=
      (Real.sqrt |s|+Real.sqrt |t|-Real.sqrt |t-s|)/2 := by
  simp only [FractionalSpectralGeometry.covariance,show 2*(1/4 : ℝ)=1/2 by norm_num,
    ← Real.sqrt_eq_rpow]

theorem source_covariances :
    inner ℝ (direction 4) (direction 2)=1 ∧
    inner ℝ (direction 4) (direction 1)=(3-Real.sqrt 3)/2 ∧
    inner ℝ (direction 2) (direction 1)=Real.sqrt 2/2 ∧
    ‖direction 2‖^2=Real.sqrt 2 := by
  have hi (s t : ℝ≥0) : inner ℝ (direction s) (direction t)=
      FractionalSpectralGeometry.covariance (1/4) s t :=
    FractionalWickCovariance.direction_inner (1/4) (by norm_num) (by norm_num) s t
  rw [hi,hi,hi,← real_inner_self_eq_norm_sq,hi]
  simp only [covariance_quarter]
  norm_num


theorem current_forecast_earlier_pairing :
    inner ℝ currentForecast (firstChaosEmbedding (direction 1))=1/2 := by
  rw [currentForecast,terminal,conditional_firstChaos_projection,source_projection_single,
    map_smul,inner_smul_left,LinearIsometry.inner_map_map]
  obtain ⟨h42,h41,h21,h22⟩ := source_covariances
  simp only [starRingEnd_apply,star_trivial]
  rw [show inner ℝ (direction 2) (direction 4)=1 from (real_inner_comm _ _).trans h42,h21,h22]
  have hp : Real.sqrt 2≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2))
  field_simp

theorem full_forecast_earlier_pairing :
    inner ℝ fullForecast (firstChaosEmbedding (direction 1))=(3-Real.sqrt 3)/2 := by
  have hm : firstChaosEmbedding (direction 1)∈generated past := by
    rw [← IBMCubicFirstChaos.wick_one_eq_embedding]
    exact GaussianWickPredictionBound.observed_wick_mem past ⟨1,by norm_num⟩ 1
  have he := (generated past).starProjection_inner_eq_zero terminal
    (firstChaosEmbedding (direction 1)) hm
  change inner ℝ (terminal-fullForecast) (firstChaosEmbedding (direction 1))=0 at he
  rw [inner_sub_left,terminal,LinearIsometry.inner_map_map,source_covariances.2.1] at he
  linarith

theorem full_past_not_current : fullForecast≠currentForecast := by
  intro he
  have hp := full_forecast_earlier_pairing
  rw [he,current_forecast_earlier_pairing] at hp
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
  nlinarith

theorem strict_prediction_energy_gain : ‖currentForecast‖^2<‖fullForecast‖^2 := by
  have hm2 : firstChaosEmbedding (direction 2)∈generated past := by
    rw [← IBMCubicFirstChaos.wick_one_eq_embedding]
    exact GaussianWickPredictionBound.observed_wick_mem past ⟨2,by norm_num⟩ 1
  have hm : currentForecast∈generated past := by
    rw [currentForecast,terminal,conditional_firstChaos_projection,source_projection_single,map_smul]
    exact (generated past).smul_mem _ hm2
  have hmf : currentForecast∈generated (fun _ : Unit => direction 2) :=
    (generated (fun _ : Unit => direction 2)).starProjection_apply_mem terminal
  have hfull := (generated past).starProjection_inner_eq_zero terminal currentForecast hm
  have hcurrent := (generated (fun _ : Unit => direction 2)).starProjection_inner_eq_zero
    terminal currentForecast hmf
  change inner ℝ (terminal-fullForecast) currentForecast=0 at hfull
  change inner ℝ (terminal-currentForecast) currentForecast=0 at hcurrent
  rw [inner_sub_left] at hfull hcurrent
  rw [real_inner_self_eq_norm_sq] at hcurrent
  have hi : inner ℝ fullForecast currentForecast=‖currentForecast‖^2 := by linarith
  have hp : 0<‖fullForecast-currentForecast‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr full_past_not_current))
  rw [norm_sub_sq_real,hi] at hp
  linarith
end OperatorDerivativeRewrite.Foundation.FractionalCurrentObservationObstruction




