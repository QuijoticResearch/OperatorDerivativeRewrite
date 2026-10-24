import Foundation.IBMTerminalRiemannOccupation

/-! Actual discrete squared-increment energy near the RANDOM terminal
folded-clock boundary tends to zero IN MEAN. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRandomBoundaryEnergy
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMTerminalBracketWeights IBMTerminalRiemannOccupation

def weightedValue (φ : ℝ × ℝ → ℝ) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (N+1), (process (uniformTime T N i.succ) Y-
    process (uniformTime T N i.castSucc) Y)^2 *
      φ (process (uniformTime T N i.castSucc) Y,process T Y)

theorem weightedValue_integrable (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ)
    (hb : ∀ x, ‖φ x‖ ≤ 1) (T : ℝ≥0) (N : ℕ) : Integrable (weightedValue φ T N) gaussianProduct := by
  apply integrable_finset_sum
  intro i hi
  have hd := ((process_memLp (uniformTime T N i.succ) 2 (by norm_num)).sub
    (process_memLp (uniformTime T N i.castSucc) 2 (by norm_num))).integrable_sq
  have hm := (((process_stronglyMeasurable (uniformTime T N i.succ)).measurable.sub
    (process_stronglyMeasurable (uniformTime T N i.castSucc)).measurable).pow_const 2).mul
      (hφ.comp ((process_stronglyMeasurable (uniformTime T N i.castSucc)).measurable.prodMk
        (process_stronglyMeasurable T).measurable))
  apply hd.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun Y => by
    simp only [Pi.mul_apply,Pi.sub_apply,Function.comp_def]
    rw [norm_mul,norm_pow,Real.norm_eq_abs,sq_abs]
    exact mul_le_of_le_one_right (sq_nonneg _) (hb _)

def weightedMean (φ : ℝ × ℝ → ℝ) (T : ℝ≥0) (N : ℕ) : ℝ :=
  ∫ Y, weightedValue φ T N Y ∂gaussianProduct

theorem weightedMean_identity (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ)
    (hb : ∀ x, ‖φ x‖ ≤ 1) (T : ℝ≥0) (N : ℕ) :
    weightedMean φ T N = error φ hφ 1 hb T N+
      ∫ Y, actualSum φ T N Y ∂gaussianProduct := by
  have he : error φ hφ 1 hb T N = weightedMean φ T N-
      ∫ Y, actualSum φ T N Y ∂gaussianProduct := by
    rw [error_actual,weightedMean,← integral_sub (weightedValue_integrable φ hφ hb T N)
      ((actualSum_memLp φ hφ hb T N).integrable (by norm_num))]
    apply integral_congr_ae
    exact ae_of_all _ fun Y => by
      simp only [Pi.sub_apply]
      unfold weightedValue actualSum
      rw [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [uniformTime_step]
      ring
  linarith

theorem outer_weightedMean_nonneg (δ : ℝ) (T : ℝ≥0) (N : ℕ) :
    0 ≤ weightedMean (outerBand δ) T N := by
  apply integral_nonneg
  intro Y
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (sq_nonneg _)
  unfold outerBand
  split_ifs <;> norm_num

theorem outer_weightedMean_tendsto (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N => weightedMean (outerBand (δ N)) T N) atTop (𝓝 0) := by
  have h := (outerBand_error_tendsto δ T hT).add (outer_mean_tendsto δ hδ T)
  simp only [zero_add] at h
  exact h.congr' (Eventually.of_forall fun N =>
    (weightedMean_identity _ (outerBand_measurable (δ N)) (outerBand_bound (δ N)) T N).symm)

theorem outer_energy_integrable (δ : ℝ) (T : ℝ≥0) (N : ℕ) :
    Integrable (weightedValue (outerBand δ) T N) gaussianProduct :=
  weightedValue_integrable _ (outerBand_measurable δ) (outerBand_bound δ) T N

def outerEnergyClass (δ : ℝ) (T : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  (outer_energy_integrable δ T N).toL1 _

theorem outerEnergyClass_actual (δ : ℝ) (T : ℝ≥0) (N : ℕ) :
    outerEnergyClass δ T N =ᵐ[gaussianProduct] weightedValue (outerBand δ) T N :=
  (outer_energy_integrable δ T N).coeFn_toL1

theorem outerEnergyClass_tendsto (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N => outerEnergyClass (δ N) T N) atTop (𝓝 0) := by
  have hn (N : ℕ) : ‖outerEnergyClass (δ N) T N‖ = weightedMean (outerBand (δ N)) T N := by
    rw [outerEnergyClass,L1.norm_of_fun_eq_integral_norm]
    apply integral_congr_ae
    exact ae_of_all _ fun Y => by
      apply Real.norm_of_nonneg
      apply Finset.sum_nonneg
      intro i hi
      apply mul_nonneg (sq_nonneg _)
      unfold outerBand
      split_ifs <;> norm_num
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero,hn] using outer_weightedMean_tendsto δ hδ T hT

end OperatorDerivativeRewrite.Foundation.IBMRandomBoundaryEnergy
