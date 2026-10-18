import Foundation.IBMBoundaryClockLimit

/-! Actual scenery-averaged Lipschitz coefficients on the shrinking IBM
boundary layer. These are expectations of the original Gaussian scenery,
not supplied scalar coefficient approximations. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMBoundaryAveragedCoefficient
open InfiniteGaussian IBMContinuousScenery IBMVarianceClockGeometry IBMMollifier
open GaussianLipschitzIntegrands GaussianDeterministicGraphCore
variable {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)

def centeredClass (n : ℕ) (r : ℝ) : GaussianL2 :=
  (centered_lipschitz hφ).compLp (sub_self _) (wholeLineScenery (kernel n) r)

def sourceAverage (n : ℕ) (r : ℝ) : ℝ :=
  φ 0 + inner ℝ gaussianOne (centeredClass hφ n r)

theorem centeredClass_coeFn (n : ℕ) (r : ℝ) :
    centeredClass hφ n r =ᵐ[gaussianProduct]
      fun ω => φ (wholeLineScenery (kernel n) r ω) - φ 0 :=
  (centered_lipschitz hφ).coeFn_compLp (sub_self _) _

/-- Literal scenery expectation, on its proved integrable domain. -/
theorem sourceAverage_eq_integral (n : ℕ) (r : ℝ) :
    sourceAverage hφ n r = ∫ ω, φ (wholeLineScenery (kernel n) r ω) ∂gaussianProduct := by
  have hu : Integrable (fun ω => φ (wholeLineScenery (kernel n) r ω)) gaussianProduct :=
    (composition_memLp hφ _).integrable (by norm_num)
  unfold sourceAverage
  rw [gaussianOne_inner_eq_integral, integral_congr_ae (centeredClass_coeFn hφ n r),
    integral_sub hu (integrable_const (φ 0)), integral_const]
  simp

theorem sourceAverage_continuous (n : ℕ) : Continuous (sourceAverage hφ n) := by
  have hc : Continuous (centeredClass hφ n) :=
    ((centered_lipschitz hφ).continuous_compLp (sub_self _)).comp
      (IBMRandomTimeHilbert.mollifiedScenery_continuous n)
  exact continuous_const.add ((innerSL ℝ gaussianOne).continuous.comp hc)

theorem sourceAverage_error (n : ℕ) (r : ℝ) :
    ‖sourceAverage hφ n r - φ 0‖ ≤ (K : ℝ) * ‖wholeLineScenery (kernel n) r‖ := by
  have hnorm : ‖gaussianOne‖ = 1 := by
    have h := gaussianOne_inner_self
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg gaussianOne]
  have h := norm_inner_le_norm (𝕜 := ℝ) gaussianOne (centeredClass hφ n r)
  simp only [sourceAverage, add_sub_cancel_left, hnorm, one_mul] at *
  exact h.trans ((centered_lipschitz hφ).norm_compLp_le (sub_self _) _)

def layerError (n : ℕ) : ℝ := (K : ℝ) * Real.sqrt (2 * (bump n).rOut)

theorem layerError_nonneg (n : ℕ) : 0 ≤ layerError (K := K) n := by
  exact mul_nonneg K.coe_nonneg (Real.sqrt_nonneg _)

theorem layerError_tendsto : Tendsto (layerError (K := K)) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (K : ℝ) * Real.sqrt (2 * (bump n).rOut)) atTop (𝓝 0)
  have h := (Real.continuous_sqrt.continuousAt.tendsto.comp
    (bump_outer_tendsto_zero.const_mul 2)).const_mul (K : ℝ)
  simpa only [Function.comp_apply, mul_zero, Real.sqrt_zero, layerError] using h

/-- Uniform boundary-layer error with no supplied coefficient hypothesis. -/
theorem sourceAverage_layer_error (n : ℕ) (r : ℝ) (hr : |r| ≤ (bump n).rOut) :
    ‖sourceAverage hφ n r - φ 0‖ ≤ layerError (K := K) n := by
  have hd := (variance_lipschitz n).dist_le_mul r 0
  simp only [Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] at hd
  have hv := variance_zero_le n
  have hnorm : ‖wholeLineScenery (kernel n) r‖ ≤ Real.sqrt (2 * (bump n).rOut) := by
    have he : variance n r = ‖wholeLineScenery (kernel n) r‖^2 := rfl
    have hp : 0 ≤ 2 * (bump n).rOut :=
      mul_nonneg (by norm_num) (bump n).rOut_pos.le
    nlinarith [he, Real.sq_sqrt hp, Real.sqrt_nonneg (2 * (bump n).rOut),
      norm_nonneg (wholeLineScenery (kernel n) r),
      le_abs_self (variance n r - variance n 0)]
  exact (sourceAverage_error hφ n r).trans
    (mul_le_mul_of_nonneg_left hnorm K.coe_nonneg)

/-- The actual weighted error is dominated by a vanishing scalar times
the very same nonnegative mollifier used in the verified clock limit. -/
theorem weighted_error_bound (n : ℕ) (r : ℝ) :
    ‖kernel n |r| * (sourceAverage hφ n |r| - φ 0)‖ ≤
      layerError (K := K) n * kernel n |r| := by
  by_cases hz : kernel n |r| = 0
  · simp [hz]
  have hr : |r| < (bump n).rOut := by
    have hm : |r| ∈ Function.support (kernel n) := hz
    rw [show Function.support (kernel n) = Metric.ball 0 (bump n).rOut from
      (bump n).support_normed_eq] at hm
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_abs] using hm
  rw [norm_mul, Real.norm_of_nonneg (kernel_nonneg n _)]
  have he := sourceAverage_layer_error hφ n |r| (by simpa only [abs_abs] using hr.le)
  nlinarith [kernel_nonneg n |r|]

end OperatorDerivativeRewrite.Foundation.IBMBoundaryAveragedCoefficient
