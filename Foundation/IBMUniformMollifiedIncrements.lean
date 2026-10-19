import Foundation.IBMFullSchwartzTerminal
import Foundation.IBMOffsetTranslation

/-! Actual nonlinear IBM scenery increments, uniformly over the concrete
normalized mollifier family. No mollifier-derivative constant is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMUniformMollifiedIncrements
open InfiniteGaussian IBMContinuousScenery IBMContinuousBulkVariance IBMMollifier
open IBMFullSchwartzTerminal IBMSchwartzSourceDerivative IBMCorrectionStein
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable
set_option backward.isDefEq.respectTransparency false

theorem scenery_increment_norm (r s : ℝ) :
    ‖sourceScenery r - sourceScenery s‖ = Real.sqrt |r - s| := by
  rw [← sourceScenery_increment_sq s r, Real.sqrt_sq (norm_nonneg _)]

/-- Every normalized nonnegative bump contracts Brownian spatial increments.
The constant is independent of BOTH points and of the mollifier index. -/
theorem mollified_increment_norm (n : ℕ) (r s : ℝ) :
    ‖wholeLineScenery (kernel n) r - wholeLineScenery (kernel n) s‖ ≤ Real.sqrt |r - s| := by
  rw [IBMOffsetTranslation.concrete_wholeLineScenery_eq_offset,
    IBMOffsetTranslation.concrete_wholeLineScenery_eq_offset,
    offsetScenery_eq_integral, offsetScenery_eq_integral]
  let a := -(bump n).rOut
  let b := (bump n).rOut
  have hi (x : ℝ) : IntegrableOn (fun u : ℝ => kernel n (-u) • sourceScenery (x + u)) (Icc a b) volume :=
    (((kernel_smooth n).continuous.comp continuous_neg).smul
      (sourceScenery_continuous.comp (continuous_const.add continuous_id))).integrableOn_Icc
  rw [← integral_sub (hi r) (hi s)]
  have hmajor : IntegrableOn (fun u : ℝ => kernel n (-u) * Real.sqrt |r - s|) (Icc a b) volume :=
    (((kernel_smooth n).continuous.comp continuous_neg).mul continuous_const).integrableOn_Icc
  have hb : ∀ᵐ u ∂volume.restrict (Icc a b),
      ‖kernel n (-u) • sourceScenery (r + u) - kernel n (-u) • sourceScenery (s + u)‖ ≤
        kernel n (-u) * Real.sqrt |r - s| := by
    apply ae_of_all
    intro u
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (kernel_nonneg n (-u)), scenery_increment_norm]
    simp only [add_sub_add_right_eq_sub]
    exact le_rfl
  apply (norm_integral_le_of_norm_le hmajor hb).trans_eq
  have hm : (∫ u in Icc a b, kernel n (-u)) = 1 := by
    simpa [a, b] using concreteMollifier_mass n 0
  rw [integral_mul_const, hm, one_mul]

theorem observable_difference_norm (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) (u v : CoefficientSpace) :
    ‖observable g a j u - observable g a j v‖ ≤
      (Real.toNNReal (SchwartzMap.seminorm ℝ 0 1 (jet g j)) : ℝ) * ‖u - v‖ := by
  have hh : ‖observable g a j u - observable g a j v‖ ≤
      (Real.toNNReal (SchwartzMap.seminorm ℝ 0 1 (jet g j)) : ℝ) * ‖firstChaosEmbedding (u - v)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [observable_coeFn g a j u, observable_coeFn g a j v,
      Lp.coeFn_sub (observable g a j u) (observable g a j v),
      Lp.coeFn_sub (firstChaosEmbedding u) (firstChaosEmbedding v)] with ω hu hv hs hd
    rw [map_sub, hd, Pi.sub_apply]
    rw [hs, Pi.sub_apply, hu, hv]
    exact (shiftedJet_lipschitz g a j).norm_sub_le _ _
  simpa only [firstChaosEmbedding.norm_map] using hh

theorem zero_embedding (n : ℕ) (r : ℝ) :
    firstChaosEmbedding (IBMGaussianSteinMoments.tripleCoefficient n r 0) = wholeLineScenery (kernel n) r := by
  rw [IBMJointMollifierGaussian.wholeLineScenery_eq_sourceEmbedding]
  rfl

theorem spatial_increment_norm (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r s : ℝ) :
    ‖spatial g a n r - spatial g a n s‖ ≤
      (Real.toNNReal (SchwartzMap.seminorm ℝ 0 1 (jet g 0)) : ℝ) * Real.sqrt |r - s| := by
  apply (observable_difference_norm g a 0 _ _).trans
  have he : ‖IBMGaussianSteinMoments.tripleCoefficient n r 0 -
      IBMGaussianSteinMoments.tripleCoefficient n s 0‖ =
      ‖wholeLineScenery (kernel n) r - wholeLineScenery (kernel n) s‖ := by
    rw [← firstChaosEmbedding.norm_map, map_sub, zero_embedding, zero_embedding]
  rw [he]
  exact mul_le_mul_of_nonneg_left (mollified_increment_norm n r s) (NNReal.coe_nonneg _)

theorem spatialLimit_increment_norm (g : SchwartzMap ℝ ℝ) (a r s : ℝ) :
    ‖spatialLimit g a r - spatialLimit g a s‖ ≤
      (Real.toNNReal (SchwartzMap.seminorm ℝ 0 1 (jet g 0)) : ℝ) * Real.sqrt |r - s| := by
  exact le_of_tendsto (((spatial_tendsto g a r).sub (spatial_tendsto g a s)).norm)
    (Eventually.of_forall fun n => spatial_increment_norm g a n r s)

end OperatorDerivativeRewrite.Foundation.IBMUniformMollifiedIncrements
