import Foundation.IBMRandomBoundaryEnergy

/-! Actual squared Brownian increment energy near the ORIGIN vanishes
strongly in L1. This reuses the same terminal-anticipative bracket calculus. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMOriginBoundaryEnergy
open InfiniteGaussian IBMTerminalRiemannOccupation IBMTerminalBracketWeights IBMRandomBoundaryEnergy

theorem origin_weightedValue_nonneg (δ : ℝ) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    0 ≤ weightedValue (originBand δ) T N Y := by
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (sq_nonneg _)
  unfold originBand
  split_ifs <;> norm_num

theorem origin_weightedMean_tendsto (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N => weightedMean (originBand (δ N)) T N) atTop (𝓝 0) := by
  have he := varying_error_tendsto (fun N => originBand (δ N))
    (fun N => originBand_measurable (δ N)) 1 (fun N => originBand_bound (δ N)) T hT
  have h := he.add (origin_mean_tendsto δ hδ T)
  simp only [zero_add] at h
  exact h.congr' (Eventually.of_forall fun N =>
    (weightedMean_identity _ (originBand_measurable (δ N)) (originBand_bound (δ N)) T N).symm)

theorem origin_energy_integrable (δ : ℝ) (T : ℝ≥0) (N : ℕ) :
    Integrable (weightedValue (originBand δ) T N) gaussianProduct :=
  weightedValue_integrable _ (originBand_measurable δ) (originBand_bound δ) T N

def originEnergyClass (δ : ℝ) (T : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  (origin_energy_integrable δ T N).toL1 _

theorem originEnergyClass_actual (δ : ℝ) (T : ℝ≥0) (N : ℕ) :
    originEnergyClass δ T N =ᵐ[gaussianProduct] weightedValue (originBand δ) T N :=
  (origin_energy_integrable δ T N).coeFn_toL1

theorem originEnergyClass_tendsto (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N => originEnergyClass (δ N) T N) atTop (𝓝 0) := by
  have hn (N : ℕ) : ‖originEnergyClass (δ N) T N‖ = weightedMean (originBand (δ N)) T N := by
    rw [originEnergyClass,L1.norm_of_fun_eq_integral_norm]
    exact integral_congr_ae (ae_of_all _ fun Y => Real.norm_of_nonneg (origin_weightedValue_nonneg (δ N) T N Y))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero,hn] using origin_weightedMean_tendsto δ hδ T hT

end OperatorDerivativeRewrite.Foundation.IBMOriginBoundaryEnergy
