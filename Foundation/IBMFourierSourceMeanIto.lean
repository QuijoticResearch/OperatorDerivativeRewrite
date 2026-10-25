import Foundation.ReflectedDampingSeriesIto
import Foundation.IBMFourierClockMeanRegularity

/-! Genuine physical-clock Ito for completed one-time actual IBM Fourier source
means. Absolute weights and fourth-frequency weights suffice. Hidden-clock
predictability and fixed-horizon AE equality are explicit; the unaveraged IBM
observable and observed-IBM filtration are not replaced by its source mean. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFourierSourceMeanIto
open InfiniteGaussian GaussianPredictableFull
variable (a β w : ℕ → ℝ)

def weight (k : ℕ) : ℝ := w k * Real.cos (β k)
def rate (k : ℕ) : ℝ := (a k) ^ 2 / 2

theorem rate_nonneg (k : ℕ) : 0 ≤ rate a k := by unfold rate; positivity

theorem weight_summable (hv : Summable (fun k => |w k|)) :
    Summable (fun k => |weight β w k|) := by
  apply hv.of_nonneg_of_le (fun _ => abs_nonneg _)
  intro k
  rw [weight, abs_mul]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq
    (mul_one _)

theorem fourth_cost (h4 : Summable (fun k => |w k| * (a k) ^ 4)) :
    Summable (ReflectedDampingSeries.cost2 (weight β w) (rate a)) := by
  apply (h4.div_const 4).of_nonneg_of_le
    (fun k => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  intro k
  simp only [weight, abs_mul, rate]
  calc
    _ ≤ |w k| * ((a k) ^ 2 / 2) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq
          (mul_one _)) (sq_nonneg _)
    _ = _ := by ring

def mean (T : ℝ≥0) : GaussianL2 :=
  IBMFourierSourceMeanCalculus.clockMean (fun k (_ : Unit) => a k) β w (fun _ => T)

theorem mean_actual (hv : Summable (fun k => |w k|)) (T : ℝ≥0) :
    mean a β w T =ᵐ[gaussianProduct] fun Y =>
      ∑' k, weight β w k * Real.exp (-rate a k * |IBMConstructedSources.clockPath Y T|) := by
  filter_upwards [IBMFourierClockMeanRegularity.clockMean_actual
    (fun k (_ : Unit) => a k) β w (fun _ => T) hv,
    IBMConstructedSources.clockPath_coordinate_ae T] with Y hY hw
  change mean a β w T Y = _ at hY
  rw [hY, ← hw]
  unfold IBMFourierClockMeanRegularity.value IBMFourierClockMeanRegularity.term
  apply tsum_congr
  intro k
  simp only [IBMFourierClockMeanRegularity.damping,
    IBMFoldedSourceCovariance.variance_expansion, Finset.univ_unique,
    Finset.sum_singleton, min_self, weight, rate]
  congr 2
  ring

def running (hv : Summable (fun k => |w k|))
    (h4 : Summable (fun k => |w k| * (a k) ^ 4)) (T : ℝ≥0) : fullPredictable :=
  ReflectedDampingSeriesIto.running (weight β w) (rate a) (rate_nonneg a)
    (weight_summable β w hv) (fourth_cost a β w h4) T

theorem actual_ito (hv : Summable (fun k => |w k|))
    (h4 : Summable (fun k => |w k| * (a k) ^ 4)) (T : ℝ≥0) :
    (fun Y => mean a β w T Y - ∑' k, weight β w k)
      =ᵐ[gaussianProduct] fun Y => itoIntegral (running a β w hv h4 T) Y -
        (∑' k, weight β w k * rate a k) * BrownianMassContinuousLimit.limitPath Y T +
        (1/2 : ℝ) * ∫ s in (0 : ℝ)..(T : ℝ),
          ∑' k, weight β w k * (rate a k) ^ 2 *
            Real.exp (-rate a k * |IBMConstructedSources.clockPath Y s.toNNReal|) := by
  filter_upwards [mean_actual a β w hv T,
    ReflectedDampingSeriesIto.actual_ito (weight β w) (rate a) (rate_nonneg a)
      (weight_summable β w hv) (fourth_cost a β w h4) T] with Y hm hi
  rw [hm]
  exact hi

end OperatorDerivativeRewrite.Foundation.IBMFourierSourceMeanIto
