import Foundation.ReflectedDampingSeries

/-! Actual original Brownian Ito for completed damping series. The global C2
extension discharges all stochastic hypotheses; no termwise stochastic-limit
or sum/integral exchange is assumed. Fixed-horizon AE identities only. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.ReflectedDampingSeriesIto
open InfiniteGaussian GaussianPredictableFull ReflectedDampingSeries
variable (b c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)
  (hb : Summable (fun k => |b k|)) (h2 : Summable (cost2 b c))

def firstConstant : ℝ≥0 := ⟨2 * ∑' k, cost1 b c k,
  mul_nonneg (by norm_num) (tsum_nonneg fun k => mul_nonneg (abs_nonneg _) (hc k))⟩

def secondConstant : ℝ≥0 := ⟨∑' k, cost2 b c k,
  tsum_nonneg fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)⟩

def running (T : ℝ≥0) : fullPredictable :=
  GaussianReflectedC2Ito.running (value b c) (value_C2 b c hc hb h2)
    (secondConstant b c) (fun x => by
      rw [value_second b c hc hb h2]; exact second_bound b c hc h2 x) T

theorem actual_ito (T : ℝ≥0) :
    (fun Y => (∑' k, b k * Real.exp (-c k * |IBMConstructedSources.clockPath Y T|)) -
      ∑' k, b k) =ᵐ[gaussianProduct] fun Y =>
        itoIntegral (running b c hc hb h2 T) Y -
          (∑' k, b k * c k) * BrownianMassContinuousLimit.limitPath Y T +
          (1/2 : ℝ) * ∫ s in (0 : ℝ)..(T : ℝ),
            ∑' k, b k * (c k)^2 *
              Real.exp (-c k * |IBMConstructedSources.clockPath Y s.toNNReal|) := by
  have h1 : ∀ x, ‖deriv (deriv (value b c)) x‖ ≤ (secondConstant b c : ℝ) := by
    intro x
    rw [value_second b c hc hb h2]
    exact second_bound b c hc h2 x
  have h0 : ∀ x, ‖deriv (value b c) x‖ ≤ (firstConstant b c hc : ℝ) := by
    intro x
    rw [value_deriv b c hc hb h2]
    exact first_bound b c hc hb h2 x
  have hi := GaussianReflectedC2Ito.reflected_ito_pathwise (value b c)
    (value_C2 b c hc hb h2) (secondConstant b c) h1 (firstConstant b c hc) h0 T
  filter_upwards [hi] with Y hY
  change _ = itoIntegral (running b c hc hb h2 T) Y + _ + _ at hY
  rw [value_second b c hc hb h2] at hY
  simp only [value_nonneg b c (abs_nonneg _), value_zero,
    value_deriv b c hc hb h2, first_zero, second,
    GaussianDampedReflectedIto.curvature, abs_abs] at hY
  convert hY using 1
  simp only [neg_mul, sub_eq_add_neg, mul_assoc]

theorem running_actual (T : ℝ≥0) :
    (running b c hc hb h2 T : GaussianTimeProductL2.TimeProbabilityL2)
      =ᵐ[GaussianTimeProductL2.timeProbability]
        (PredictableRealL2.horizon T).indicator (fun z =>
          BrownianSignIntegral.signum (BrownianClockWeightedEnergy.sigma z) *
            ∑' k, b k * (-c k * Real.exp (-c k * |BrownianClockWeightedEnergy.sigma z|))) := by
  have hi := GaussianReflectedC2Ito.running_coeFn (value b c) (value_C2 b c hc hb h2)
    (secondConstant b c) (fun x => by
      rw [value_second b c hc hb h2]; exact second_bound b c hc h2 x) T
  filter_upwards [hi] with z hz
  change (running b c hc hb h2 T : GaussianTimeProductL2.TimeProbabilityL2) z = _ at hz
  rw [hz]
  by_cases h : z ∈ PredictableRealL2.horizon T
  · simp only [indicator_of_mem h, value_deriv b c hc hb h2, first,
      GaussianDampedReflectedIto.slope_nonneg _ (abs_nonneg _)]
  · simp [h]

end OperatorDerivativeRewrite.Foundation.ReflectedDampingSeriesIto
