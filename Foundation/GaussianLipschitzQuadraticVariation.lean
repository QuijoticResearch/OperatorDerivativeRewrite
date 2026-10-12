import Foundation.GaussianLipschitzIntegrands
import Foundation.GaussianWeightedQuadraticVariation

/-! Specialization of the verified adapted quadratic-variation theorem to
actual Lipschitz functions of left Brownian observations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianLipschitzQuadraticVariation
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open GaussianLipschitzIntegrands GaussianWeightedQuadraticVariation
variable {φ : ℝ → ℝ} {K : ℝ≥0}

def weight (φ : ℝ → ℝ) (s : ℝ≥0) (p : Iic s → ℝ) : ℝ := φ (p ⟨s, by simp⟩)

theorem weight_measurable (hφ : LipschitzWith K φ) (s : ℝ≥0) :
    Measurable (weight φ s) := hφ.continuous.measurable.comp (measurable_pi_apply _)

theorem weight_memLp (hφ : LipschitzWith K φ) (s : ℝ≥0) :
    MemLp (GaussianPredictableStep.pastCoefficient process s (weight φ s)) 2 gaussianProduct :=
  composition_memLp hφ (wienerL2 s)

def error (hφ : LipschitzWith K φ) (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  weightedError (uniformTime T N) (fun i => weight φ (uniformTime T N i.castSucc))
    (fun i => weight_measurable hφ _) (fun i => weight_memLp hφ _)

theorem error_coeFn (hφ : LipschitzWith K φ) (T : ℝ≥0) (N : ℕ) :
    error hφ T N =ᵐ[gaussianProduct] fun ω =>
      ∑ i : Fin (N + 1), φ (process (uniformTime T N i.castSucc) ω) *
        ((process (uniformTime T N i.succ) ω - process (uniformTime T N i.castSucc) ω) ^ 2 -
          ((uniformTime T N i.succ : ℝ) - uniformTime T N i.castSucc)) :=
  weightedError_coeFn _ (uniformTime_monotone T N) _ _ _

theorem weight_energy (hφ : LipschitzWith K φ) (s : ℝ≥0) :
    (∫ ω, φ (process s ω) ^ 2 ∂gaussianProduct) = ‖valueL2 hφ s‖ ^ 2 := by
  rw [BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [valueL2_coeFn hφ s] with ω hv
  rw [hv, Real.norm_eq_abs, sq_abs]

/-- No boundedness of phi is assumed: its L2 norms are bounded on compact time
intervals by the already proved Lipschitz-composition continuity. -/
theorem error_tendsto (hφ : LipschitzWith K φ) (T : ℝ≥0) :
    Tendsto (error hφ T) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((valueL2_continuous hφ).comp continuous_real_toNNReal).continuousOn
      (s := Icc 0 (T : ℝ))
  apply weightedError_tendsto_of_mesh (fun N => N + 1) (uniformTime T)
    (uniformTime_monotone T) (fun N i => weight φ (uniformTime T N i.castSucc))
    (fun N i => weight_measurable hφ _) (fun N i => weight_memLp hφ _)
    (M ^ 2) T (sq_nonneg _) (fun N => (T : ℝ) / (N + 1))
  · intro N
    positivity
  · exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  · intro N i
    change (∫ ω, φ (process (uniformTime T N i.castSucc) ω) ^ 2 ∂gaussianProduct) ≤ M ^ 2
    rw [weight_energy]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have hi : uniformTime T N i.castSucc ≤ T := by
      exact (uniformTime_monotone T N (Fin.le_last _)).trans_eq (uniformTime_endpoints T N).2
    simpa only [Function.comp_def, Real.toNNReal_coe] using
      hM (uniformTime T N i.castSucc) ⟨(uniformTime T N i.castSucc).coe_nonneg, hi⟩
  · intro N i
    exact (uniformTime_step T N i).le
  · intro N
    simp only [(uniformTime_endpoints T N).1, (uniformTime_endpoints T N).2,
      NNReal.coe_zero, sub_zero, le_refl]

end OperatorDerivativeRewrite.Foundation.GaussianLipschitzQuadraticVariation


