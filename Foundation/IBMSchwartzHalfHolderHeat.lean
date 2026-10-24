import Foundation.GaussianHalfHolderScore
import Foundation.IBMSchwartzFullReflectedIto
import Foundation.IBMFoldedHeatTimeEnergy
import Foundation.GaussianBrownianConditionalTransition

/-! The ACTUAL nonlinear folded Brownian scenery is half-Holder in source L2.
Its centered Gaussian score has the integrable terminal energy singularity.
Identification as a heat derivative or canonical Ito coefficient remains separate. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHalfHolderHeat
open InfiniteGaussian IBMCorrectionStein IBMSchwartzSourceDerivative
open IBMQuarticPrimitiveLimit IBMFullSchwartzTerminal

def constant (g : SchwartzMap ℝ ℝ) : ℝ :=
  (Real.toNNReal (SchwartzMap.seminorm ℝ 0 1 g) : ℝ)

theorem constant_nonneg (g : SchwartzMap ℝ ℝ) : 0 ≤ constant g := NNReal.coe_nonneg _

theorem observation_difference (g : SchwartzMap ℝ ℝ) (a : ℝ) (u v : CoefficientSpace) :
    ‖observable g a 0 u-observable g a 0 v‖ ≤ constant g*‖u-v‖ := by
  have hb : ‖observable g a 0 u-observable g a 0 v‖ ≤
      constant g*‖firstChaosEmbedding u-firstChaosEmbedding v‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [observable_coeFn g a 0 u,observable_coeFn g a 0 v,
      Lp.coeFn_sub (observable g a 0 u) (observable g a 0 v),
      Lp.coeFn_sub (firstChaosEmbedding u) (firstChaosEmbedding v)] with X hu hv hs hd
    rw [hs,hd,Pi.sub_apply,Pi.sub_apply,hu,hv]
    exact (shiftedJet_lipschitz g a 0).norm_sub_le _ _
  simpa only [← map_sub,firstChaosEmbedding.norm_map] using hb

def curve (g : SchwartzMap ℝ ℝ) (a r : ℝ) : GaussianL2 := spatialLimit g a |r|

theorem curve_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) : Continuous (curve g a) :=
  (spatialLimit_continuous g a).comp continuous_abs

theorem coefficient_increment (x y : ℝ) :
    ‖baseCoefficient x-baseCoefficient y‖^2 = |x-y| := by
  rw [← firstChaosEmbedding.norm_map, map_sub,base_embedding,base_embedding]
  exact IBMContinuousScenery.sourceScenery_increment_sq y x

theorem curve_holder (g : SchwartzMap ℝ ℝ) (a x y : ℝ) :
    ‖curve g a x-curve g a y‖^2 ≤ (constant g)^2*|x-y| := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (observation_difference g a (baseCoefficient |x|) (baseCoefficient |y|)) 2
  rw [mul_pow,coefficient_increment] at h
  exact h.trans (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) (sq_nonneg _))

theorem curve_bound (g : SchwartzMap ℝ ℝ) (a r : ℝ) :
    ‖curve g a r‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := observable_bound g a 0 _

theorem actual_sections (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (Y : SampleSpace) :
    curve g a (IBMConstructedSources.clockPath Y T) =ᵐ[gaussianProduct]
      fun X => g (a+IBMConstructedSources.ibmValue T (X,Y)) := actual_section g a T Y

attribute [local irreducible] curve GaussianHalfHolderScore.score

def heatScore (g : SchwartzMap ℝ ℝ) (a b v : ℝ) : GaussianL2 :=
  GaussianHalfHolderScore.score (curve g a) b (Real.sqrt v)

theorem heatScore_stronglyMeasurable (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    StronglyMeasurable (fun p : ℝ × ℝ => heatScore g a p.1 p.2) :=
  (GaussianHalfHolderScore.score_stronglyMeasurable (curve g a) (curve_continuous g a)).comp_measurable
    (measurable_fst.prodMk (Real.continuous_sqrt.measurable.comp measurable_snd))

theorem heatScore_zero (g : SchwartzMap ℝ ℝ) (a b : ℝ) : heatScore g a b 0 = 0 := by
  simp [heatScore,GaussianHalfHolderScore.score_zero]

theorem heatScore_energy (g : SchwartzMap ℝ ℝ) (a b v : ℝ) (hv : 0 < v) :
    ‖heatScore g a b v‖^2 ≤
      (constant g*GaussianHalfHolderScore.mass)^2/Real.sqrt v :=
  GaussianHalfHolderScore.score_energy (curve g a) (curve_continuous g a)
    (constant g) (constant_nonneg g) (curve_holder g a) b (Real.sqrt v) (Real.sqrt_pos.mpr hv)

theorem heatScore_energy_nonneg (g : SchwartzMap ℝ ℝ) (a b v : ℝ) (hv : 0 ≤ v) :
    ‖heatScore g a b v‖^2 ≤
      (constant g*GaussianHalfHolderScore.mass)^2/Real.sqrt v := by
  rcases hv.eq_or_lt with h|h
  · rw [← h,heatScore_zero]
    simp
  · exact heatScore_energy g a b v h

theorem conditional_transition (g : SchwartzMap ℝ ℝ) (a : ℝ) (S T : ℝ≥0) (hST : S ≤ T) :
    gaussianProduct[fun Y => curve g a (GaussianTimeProcess.process T Y) |
      GaussianTimeProcess.naturalFiltration S] =ᵐ[gaussianProduct] fun Y =>
      ∫ y, curve g a (GaussianTimeProcess.process S Y+y)
        ∂ProbabilityTheory.gaussianReal 0 (T-S) := by
  apply GaussianBrownianConditionalTransition.conditional_transition S T hST
    (curve g a) (curve_continuous g a).stronglyMeasurable
  exact (integrable_const (SchwartzMap.seminorm ℝ 0 0 g)).mono'
    ((curve_continuous g a).stronglyMeasurable.comp_measurable
      (GaussianTimeProcess.process_stronglyMeasurable T).measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun Y => curve_bound g a _)

theorem energy_envelope_integrable (g : SchwartzMap ℝ ℝ) (T : ℝ) :
    IntervalIntegrable (fun s => (constant g*GaussianHalfHolderScore.mass)^2*
      (T-s)^(-(1/2 : ℝ))) volume 0 T := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
    (by norm_num : -1 < -(1/2 : ℝ))).comp_sub_left T
  simpa only [sub_zero,sub_self] using
    (hi.const_mul ((constant g*GaussianHalfHolderScore.mass)^2)).symm

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHalfHolderHeat
