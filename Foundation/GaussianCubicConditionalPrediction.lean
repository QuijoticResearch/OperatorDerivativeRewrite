import Foundation.GaussianWickConditionalProjection

/-! Actual posterior covariance corrections for ordinary cubic observables.
Raw cubic forecasts retain their first-chaos prediction component. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianCubicConditionalPrediction
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianTimeSpaceHermite IBMGaussianSteinMoments IBMCubicFirstChaos

def residualVariance {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) : ℝ :=
  ‖u‖^2-‖sourceProjection h u‖^2

def residualCovariance {I : Type*} (h : I → CoefficientSpace) (u v : CoefficientSpace) : ℝ :=
  inner ℝ u v-inner ℝ (sourceProjection h u) (sourceProjection h v)

theorem residualVariance_eq_norm_sq {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    residualVariance h u=‖u-sourceProjection h u‖^2 := by
  have hm : sourceProjection h u ∈ sourceSpan h := (sourceSpan h).starProjection_apply_mem u
  have he := (sourceSpan h).starProjection_inner_eq_zero u (sourceProjection h u) hm
  change inner ℝ (u-sourceProjection h u) (sourceProjection h u)=0 at he
  rw [inner_sub_left,real_inner_self_eq_norm_sq] at he
  rw [residualVariance,norm_sub_sq_real]
  nlinarith

theorem residualCovariance_eq_inner {I : Type*} (h : I → CoefficientSpace) (u v : CoefficientSpace) :
    residualCovariance h u v=inner ℝ (u-sourceProjection h u) (v-sourceProjection h v) := by
  have hu : sourceProjection h u ∈ sourceSpan h := (sourceSpan h).starProjection_apply_mem u
  have hv : sourceProjection h v ∈ sourceSpan h := (sourceSpan h).starProjection_apply_mem v
  have h1 := (sourceSpan h).starProjection_inner_eq_zero u (sourceProjection h v) hv
  have h2 := (sourceSpan h).starProjection_inner_eq_zero v (sourceProjection h u) hu
  change inner ℝ (u-sourceProjection h u) (sourceProjection h v)=0 at h1
  change inner ℝ (v-sourceProjection h v) (sourceProjection h u)=0 at h2
  rw [inner_sub_left] at h1 h2
  rw [real_inner_comm (sourceProjection h u) v,
    real_inner_comm (sourceProjection h u) (sourceProjection h v)] at h2
  rw [residualCovariance,inner_sub_left,inner_sub_right,inner_sub_right]
  linarith

theorem conditional_cube {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    conditionalProjection h (cube u)=(wick (sourceProjection h u) 3 : GaussianL2)+
      (3*‖u‖^2) • (wick (sourceProjection h u) 1 : GaussianL2) := by
  simp only [cube,map_add,map_smul,conditional_wick_projection]

theorem conditional_cube_eq_projected_cube {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    conditionalProjection h (cube u)=cube (sourceProjection h u)+
      (3*residualVariance h u) • firstChaosEmbedding (sourceProjection h u) := by
  rw [conditional_cube]
  simp only [cube,wick_one_eq_embedding,residualVariance]
  module

theorem conditional_mixedCube {I : Type*} (h : I → CoefficientSpace) (u v : CoefficientSpace) :
    conditionalProjection h (mixedCube u v)=mixedCube (sourceProjection h u) (sourceProjection h v)+
      residualVariance h v • firstChaosEmbedding (sourceProjection h u)+
      (2*residualCovariance h u v) • firstChaosEmbedding (sourceProjection h v) := by
  simp only [mixedCube,map_smul,map_add,map_sub,conditional_cube_eq_projected_cube,
    residualVariance,residualCovariance,norm_add_sq_real,norm_sub_sq_real]
  module

theorem conditional_correction {I : Type*} (h : I → CoefficientSpace) (u v w : CoefficientSpace) :
    conditionalProjection h (correction u v w)=
      correction (sourceProjection h u) (sourceProjection h v) (sourceProjection h w)+
        (residualVariance h v+residualCovariance h u w) • firstChaosEmbedding (sourceProjection h u)+
        (2*residualCovariance h u v) • firstChaosEmbedding (sourceProjection h v)+
        ((1/2 : ℝ)*residualVariance h u) • firstChaosEmbedding (sourceProjection h w) := by
  simp only [correction,map_add,map_smul,conditional_mixedCube,residualCovariance,real_inner_comm]
  module

theorem conditional_cube_energy {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    ‖conditionalProjection h (cube u)‖^2=6*(‖sourceProjection h u‖^2)^3+
      9*(‖u‖^2)^2*‖sourceProjection h u‖^2 := by
  rw [conditional_cube,norm_add_sq_real]
  simp only [GaussianWickContinuity.wick_norm_sq,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    inner_smul_right,wick_inner]
  norm_num

theorem conditional_cube_energy_from_linear {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    ‖conditionalProjection h (cube u)‖^2=
      6*(‖conditionalProjection h (firstChaosEmbedding u)‖^2)^3+
        9*(‖u‖^2)^2*‖conditionalProjection h (firstChaosEmbedding u)‖^2 := by
  rw [conditional_cube_energy,conditional_firstChaos_projection,LinearIsometry.norm_map]

theorem conditional_cube_energy_bounds {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    9*(‖u‖^2)^2*‖sourceProjection h u‖^2 ≤ ‖conditionalProjection h (cube u)‖^2 ∧
      ‖conditionalProjection h (cube u)‖^2 ≤ 15*(‖u‖^2)^2*‖sourceProjection h u‖^2 := by
  have hp : ‖sourceProjection h u‖ ≤ ‖u‖ := (sourceSpan h).norm_starProjection_apply_le u
  have hs := (sq_le_sq₀ (norm_nonneg (sourceProjection h u)) (norm_nonneg u)).mpr hp
  have ht := (sq_le_sq₀ (sq_nonneg ‖sourceProjection h u‖) (sq_nonneg ‖u‖)).mpr hs
  have hm := mul_le_mul_of_nonneg_right ht (sq_nonneg ‖sourceProjection h u‖)
  rw [conditional_cube_energy]
  constructor <;> nlinarith [pow_nonneg (sq_nonneg ‖sourceProjection h u‖) 3]

namespace Fractional

def cubeForecast (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ≥0) : GaussianL2 :=
  conditionalProjection (FractionalPredictionObstruction.pastDirections H hH0 hH1 t)
    (cube (FractionalGaussianProcess.direction H hH0 hH1 1))

theorem cubeForecast_energy (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ≥0) :
    ‖cubeForecast H hH0 hH1 t‖^2=
      6*(‖FractionalPredictionObstruction.forecast H hH0 hH1 t‖^2)^3+
        9*‖FractionalPredictionObstruction.forecast H hH0 hH1 t‖^2 := by
  have hn : ‖FractionalGaussianProcess.direction H hH0 hH1 1‖^2=1 := by
    rw [← real_inner_self_eq_norm_sq,FractionalWickCovariance.direction_inner]
    simp [FractionalSpectralGeometry.covariance,show 2*H≠0 by positivity]
  have he := conditional_cube_energy_from_linear
    (FractionalPredictionObstruction.pastDirections H hH0 hH1 t)
    (FractionalGaussianProcess.direction H hH0 hH1 1)
  simpa only [cubeForecast,FractionalPredictionObstruction.forecast,FractionalGaussianProcess.value,
    hn,one_pow,mul_one] using he

theorem cubeForecast_zero (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) : cubeForecast H hH0 hH1 0=0 := by
  have he := cubeForecast_energy H hH0 hH1 0
  rw [FractionalPredictionObstruction.forecast_zero,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),
    zero_pow (by decide : (3 : ℕ)≠0),mul_zero,mul_zero,add_zero] at he
  apply norm_eq_zero.mp
  nlinarith

theorem cubeForecast_energy_lower (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ≥0) :
    9*‖FractionalPredictionObstruction.forecast H hH0 hH1 t‖^2 ≤ ‖cubeForecast H hH0 hH1 t‖^2 := by
  rw [cubeForecast_energy]
  nlinarith [pow_nonneg (sq_nonneg ‖FractionalPredictionObstruction.forecast H hH0 hH1 t‖) 3]

theorem no_higher_cube_prediction_increment_bound (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)
    (α : ℝ) (hα : 2*H < α) (C δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ≥0, 0 < t ∧ (t : ℝ)<δ ∧ t≤1 ∧
      C*(t : ℝ)^α < ‖cubeForecast H hH0 hH1 t-cubeForecast H hH0 hH1 0‖^2 := by
  obtain ⟨t,ht,htδ,ht1,hfail⟩ :=
    FractionalPredictionObstruction.no_higher_power_bound H hH0 hH1 α hα (C/9) δ hδ
  refine ⟨t,ht,htδ,ht1, ?_⟩
  rw [cubeForecast_zero,sub_zero]
  have hb := cubeForecast_energy_lower H hH0 hH1 t
  nlinarith

end Fractional
end OperatorDerivativeRewrite.Foundation.GaussianCubicConditionalPrediction
