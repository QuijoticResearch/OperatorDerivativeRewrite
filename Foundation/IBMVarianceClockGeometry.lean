import Foundation.IBMBoundaryCurvature
import Foundation.IBMNegativeBulkVariance
import Foundation.RealSteklovApprox
import Foundation.IBMRandomTimeHilbert
import Foundation.BrownianTanakaApproximation
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Global C² variance geometry needed for the actual Brownian clock Itô
formula. Boundary endpoints follow by continuity from the actual covariance
identities, rather than by extrapolating a strict-bulk formula. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMVarianceClockGeometry
open InfiniteGaussian IBMContinuousScenery IBMMollifier IBMBoundaryCurvature
open IBMOffsetTranslation IBMNegativeBulkVariance

def variance (n : ℕ) : ℝ → ℝ := wholeLineVariance (kernel n)

theorem variance_smooth (n : ℕ) : ContDiff ℝ 2 (variance n) := by
  have h : ContDiff ℝ 2 (wholeLineScenery (kernel n)) :=
    (kernel_compactSupport n).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((kernel_smooth n).of_le (by norm_num))
      sourceScenery_locallyIntegrable
  exact h.norm_sq ℝ

theorem variance_second (n : ℕ) : deriv (deriv (variance n)) = fun x => 2 * kernel n x := by
  have hc := (RealSteklovApprox.deriv_contDiff_one _ (variance_smooth n)).continuous_deriv_one
  apply (hc.ae_eq_iff_eq volume (continuous_const.mul (kernel_smooth n).continuous)).mp
  have hn : ∀ᵐ x : ℝ ∂volume, x ≠ (bump n).rOut ∧ x ≠ -(bump n).rOut := by
    rw [ae_iff]
    apply measure_mono_null (t := {(bump n).rOut} ∪ {-(bump n).rOut})
    · intro x hx
      change ¬(x ≠ (bump n).rOut ∧ x ≠ -(bump n).rOut) at hx
      simp only [mem_union, mem_singleton_iff]
      tauto
    · exact (Set.toFinite _).measure_zero volume
  filter_upwards [hn] with x hx
  change deriv (deriv (variance n)) x = 2 * kernel n x
  by_cases hpos : (bump n).rOut < x
  · have hk : kernel n x = 0 := by
      have hs : x ∉ Function.support (kernel n) := by
        rw [show Function.support (kernel n) = Metric.ball 0 (bump n).rOut from
          (bump n).support_normed_eq]
        simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
        intro hh
        linarith [(abs_lt.mp hh).2]
      simpa only [Function.mem_support, not_not] using hs
    simp only [variance, concrete_wholeLineVariance_second_deriv n x hpos, hk, mul_zero]
  · by_cases hneg : x < -(bump n).rOut
    · have hk : kernel n x = 0 := by
        have hs : x ∉ Function.support (kernel n) := by
          rw [show Function.support (kernel n) = Metric.ball 0 (bump n).rOut from
            (bump n).support_normed_eq]
          simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
          intro hh
          linarith [(abs_lt.mp hh).1]
        simpa only [Function.mem_support, not_not] using hs
      simp only [variance, concrete_negative_variance_second_deriv n x hneg, hk, mul_zero]
    · have hi : |x| < (bump n).rOut := by
        apply abs_lt.mpr
        exact ⟨lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hx.2),
          lt_of_le_of_ne (le_of_not_gt hpos) hx.1⟩
      rw [variance, wholeLineVariance_second_deriv (kernel n) (kernel_compactSupport n)
        ((kernel_smooth n).of_le (by norm_num)) x, concrete_covariance_bracket n x hi]

theorem slope_monotone (n : ℕ) : Monotone (deriv (variance n)) :=
  monotone_of_deriv_nonneg
    ((RealSteklovApprox.deriv_contDiff_one _ (variance_smooth n)).differentiable (by norm_num))
    (fun x => by rw [variance_second]; exact mul_nonneg (by norm_num) (kernel_nonneg n x))

theorem slope_bound (n : ℕ) (x : ℝ) : ‖deriv (variance n) x‖ ≤ 1 := by
  by_cases hp : (bump n).rOut < x
  · rw [variance, concrete_wholeLineVariance_deriv n x hp]
    norm_num
  by_cases hn : x < -(bump n).rOut
  · rw [variance, concrete_negative_variance_deriv n x hn]
    norm_num
  have hl := slope_monotone n (show -(bump n).rOut - 1 ≤ x by linarith)
  have hu := slope_monotone n (show x ≤ (bump n).rOut + 1 by linarith)
  change deriv (wholeLineVariance (kernel n)) (-(bump n).rOut - 1) ≤
    deriv (variance n) x at hl
  rw [concrete_negative_variance_deriv n (-(bump n).rOut - 1) (by linarith)] at hl
  change deriv (variance n) x ≤
    deriv (wholeLineVariance (kernel n)) ((bump n).rOut + 1) at hu
  rw [concrete_wholeLineVariance_deriv n ((bump n).rOut + 1) (by linarith)] at hu
  exact abs_le.mpr ⟨hl, hu⟩

theorem variance_lipschitz (n : ℕ) : LipschitzWith 1 (variance n) :=
  lipschitzWith_of_nnnorm_deriv_le ((variance_smooth n).differentiable (by norm_num))
    (fun x => show ‖deriv (variance n) x‖ ≤ (1 : ℝ) from slope_bound n x)

theorem variance_tendsto (x : ℝ) :
    Tendsto (fun n => variance n x) atTop (𝓝 |x|) := by
  have h := ((concreteMollifier_tendsto x).norm.pow 2)
  simpa only [variance, wholeLineVariance, IBMRandomTimeHilbert.sourceScenery_norm_sq] using h

theorem slope_zero (n : ℕ) : deriv (variance n) 0 = 0 := by
  rw [variance, wholeLineVariance_deriv (kernel n) (kernel_compactSupport n)
    ((kernel_smooth n).of_le (by norm_num)), concrete_cross_covariance_zero, mul_zero]

theorem slope_tendsto (x : ℝ) :
    Tendsto (fun n => deriv (variance n) x) atTop (𝓝 (BrownianSignIntegral.signum x)) := by
  by_cases hx : x = 0
  · simp only [hx, slope_zero, BrownianSignIntegral.signum_zero]
    exact tendsto_const_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [bump_outer_tendsto_zero.eventually (eventually_lt_nhds (abs_pos.mpr hx))]
    with n hn
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [abs_of_neg hneg] at hn
    rw [variance, concrete_negative_variance_deriv n x (by linarith)]
    simp [BrownianSignIntegral.signum, hneg, not_lt_of_gt hneg]
  · rw [abs_of_pos hpos] at hn
    rw [variance, concrete_wholeLineVariance_deriv n x hn]
    simp [BrownianSignIntegral.signum, hpos]

theorem slope_sign_bound (n : ℕ) (x : ℝ) :
    ‖deriv (variance n) x‖ ≤ ‖BrownianSignIntegral.signum x‖ := by
  by_cases hx : x = 0
  · simp [hx, slope_zero]
  have he : ‖BrownianSignIntegral.signum x‖ = 1 := by
    rcases lt_or_gt_of_ne hx with hn | hp
    · simp [BrownianSignIntegral.signum, hn, not_lt_of_gt hn]
    · simp [BrownianSignIntegral.signum, hp]
  rw [he]
  exact slope_bound n x

theorem variance_zero_le (n : ℕ) : variance n 0 ≤ (bump n).rOut := by
  have h := concreteMollifier_error_sq_le n 0
  have hz : sourceScenery 0 = 0 := by
    apply norm_eq_zero.mp
    have hh := IBMRandomTimeHilbert.sourceScenery_norm_sq 0
    simpa using hh
  simpa only [hz, sub_zero, variance, wholeLineVariance] using h

theorem variance_bound (n : ℕ) (x : ℝ) : ‖variance n x‖ ≤ |x| + 2 := by
  have h := (variance_lipschitz n).dist_le_mul x 0
  simp only [Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] at h
  have h0 := variance_zero_le n
  have hn : (bump n).rOut ≤ 2 := by
    change 2 / ((n : ℝ) + 1) ≤ 2
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  linarith [le_abs_self (variance n x - variance n 0)]

end OperatorDerivativeRewrite.Foundation.IBMVarianceClockGeometry
