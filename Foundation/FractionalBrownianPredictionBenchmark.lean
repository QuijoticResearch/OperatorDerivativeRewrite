import Foundation.FractionalTerminalPredictionRank

/-! Exact Brownian benchmark inside the actual fractional spectral realization. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.FractionalBrownianPredictionBenchmark
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianSingleObservationPrediction GaussianTerminalPredictionSpectrum

def direction (t : ℝ≥0) : CoefficientSpace :=
  FractionalGaussianProcess.direction (1/2) (by norm_num) (by norm_num) t

def past (t : ℝ≥0) : Set.Iic t → CoefficientSpace :=
  FractionalPredictionObstruction.pastDirections (1/2) (by norm_num) (by norm_num) t

theorem covariance_half (s t : ℝ≥0) (h : s≤t) :
    FractionalSpectralGeometry.covariance (1/2) s t=s := by
  unfold FractionalSpectralGeometry.covariance
  norm_num
  rw [abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ)≤t from h))]
  ring

theorem past_pairing (t : ℝ≥0) (ht : t≤1) (i : Set.Iic t) :
    inner ℝ (direction 1) (past t i)=inner ℝ (direction t) (past t i) := by
  change inner ℝ (FractionalGaussianProcess.direction _ _ _ 1)
    (FractionalGaussianProcess.direction _ _ _ i)=inner ℝ
      (FractionalGaussianProcess.direction _ _ _ t) (FractionalGaussianProcess.direction _ _ _ i)
  rw [FractionalWickCovariance.direction_inner,FractionalWickCovariance.direction_inner]
  norm_num only [NNReal.coe_one]
  rw [FractionalSpectralGeometry.covariance_symm (1/2) 1 i,
    FractionalSpectralGeometry.covariance_symm (1/2) t i]
  have h1 := covariance_half i 1 (i.property.trans ht)
  norm_num only [NNReal.coe_one] at h1
  rw [h1,covariance_half i t i.property]

theorem source_projection (t : ℝ≥0) (ht : t≤1) :
    sourceProjection (past t) (direction 1)=direction t := by
  have hm : direction t∈sourceSpan (past t) :=
    (Submodule.span ℝ (Set.range (past t))).le_topologicalClosure
      (Submodule.subset_span ⟨⟨t,by simp⟩,rfl⟩)
  let r := direction 1-direction t
  have hs : Submodule.span ℝ (Set.range (past t))≤(innerSL ℝ r).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change inner ℝ (direction 1-direction t) (past t i)=0
    rw [inner_sub_left,past_pairing t ht i,sub_self]
  have hc := (Submodule.span ℝ (Set.range (past t))).topologicalClosure_minimal hs
    (innerSL ℝ r).isClosed_ker
  have ho : r∈(sourceSpan (past t))ᗮ := by
    apply (sourceSpan (past t)).mem_orthogonal r |>.mpr
    intro f hf
    have hi := hc hf
    change inner ℝ r f=0 at hi
    simpa only [real_inner_comm] using hi
  exact (sourceSpan (past t)).eq_starProjection_of_mem_orthogonal hm ho

theorem linear_forecast (t : ℝ≥0) (ht : t≤1) :
    FractionalPredictionObstruction.forecast (1/2) (by norm_num) (by norm_num) t=
      FractionalGaussianProcess.value (1/2) (by norm_num) (by norm_num) t := by
  change conditionalProjection (past t) (firstChaosEmbedding (direction 1))=firstChaosEmbedding (direction t)
  rw [conditional_firstChaos_projection,source_projection t ht]

theorem direction_energy (t : ℝ≥0) : ‖direction t‖^2=(t : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (FractionalGaussianProcess.direction _ _ _ t)
    (FractionalGaussianProcess.direction _ _ _ t)=_
  rw [FractionalWickCovariance.direction_inner,covariance_half t t le_rfl]

theorem wick_forecast (t : ℝ≥0) (ht : t≤1) (n : ℕ) :
    conditionalProjection (past t) (GaussianTimeSpaceHermite.wick (direction 1) n)=
      (GaussianTimeSpaceHermite.wick (direction t) n : GaussianL2) := by
  rw [conditional_wick_projection,source_projection t ht]

theorem wick_forecast_energy (t : ℝ≥0) (ht : t≤1) (n : ℕ) :
    ‖conditionalProjection (past t) (GaussianTimeSpaceHermite.wick (direction 1) n)‖^2=
      (n.factorial : ℝ)*(t : ℝ)^n := by
  rw [conditional_wick_energy,source_projection t ht,direction_energy]

theorem current_observation_sufficient (t : ℝ≥0) (ht : t≤1) (f : GaussianL2)
    (hf : f∈singleGenerated (direction 1)) :
    conditionalProjection (past t) f=conditionalProjection (fun _ : Unit => direction t) f := by
  rw [conditional_singleObservation_sufficient (past t) (direction 1) f hf,source_projection t ht]

theorem terminal_forecast_energy (t : ℝ≥0) (ht : t≤1) (f : GaussianL2)
    (hf : f∈singleGenerated (direction 1)) :
    HasSum (fun n => (coefficient (direction 1) f n)^2*(n.factorial : ℝ)*(t : ℝ)^n)
      (‖conditionalProjection (past t) f‖^2) := by
  have hu : ‖direction 1‖^2=1 := by simpa using direction_energy 1
  have hs := terminal_prediction_energy_hasSum (past t) (direction 1) hu f hf
  simpa only [source_projection t ht,direction_energy] using hs

end OperatorDerivativeRewrite.Foundation.FractionalBrownianPredictionBenchmark


