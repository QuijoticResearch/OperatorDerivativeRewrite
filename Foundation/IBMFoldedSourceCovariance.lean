import Foundation.IBMFourierSourceMeanCalculus
import Foundation.FractionalCovarianceMatrices

/-! Folded Brownian covariance controls source-averaged IBM without
differentiating the half-Holder source-Hilbert direction map. -/
noncomputable section
open MeasureTheory
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedSourceCovariance
open InfiniteGaussian

def direction (x : ℝ) : CoefficientSpace := IBMActualQuarticMoment.sceneryDirection |x|

theorem gram (x y : ℝ) : inner ℝ (direction x) (direction y) = min |x| |y| := by
  rw [direction,direction,IBMActualQuarticMoment.sceneryDirection,
    IBMActualQuarticMoment.sceneryDirection,LinearIsometry.inner_map_map,
    FractionalSpectralGeometry.normalized_inner]
  exact FractionalCovarianceMatrices.brownian_covariance _ _ (abs_nonneg _) (abs_nonneg _)

variable {ι : Type*} [Fintype ι]

def variance (b : ι → ℝ) (x : ι → ℝ) : ℝ := ‖∑ i, b i • direction (x i)‖^2

theorem variance_nonneg (b : ι → ℝ) (x : ι → ℝ) : 0 ≤ variance b x := sq_nonneg _

theorem variance_expansion (b : ι → ℝ) (x : ι → ℝ) :
    variance b x = ∑ i, ∑ j, b i*b j*min |x i| |x j| := by
  rw [variance,← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,real_inner_smul_left,inner_smul_right,gram,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [min_comm]
  ring

theorem covariance_difference (x y : ι → ℝ) (i j : ι) :
    |(min |x i| |x j|) - (min |y i| |y j|)| ≤ ‖x-y‖ := by
  apply (abs_min_sub_min_le_max _ _ _ _).trans
  apply max_le
  · exact (abs_abs_sub_abs_le_abs_sub _ _).trans (by
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (x-y) i)
  · exact (abs_abs_sub_abs_le_abs_sub _ _).trans (by
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (x-y) j)

theorem variance_difference (b : ι → ℝ) (x y : ι → ℝ) :
    |variance b x-variance b y| ≤ (IBMUniformRidgeNativeBounds.amplitude b)^2*‖x-y‖ := by
  rw [variance_expansion,variance_expansion,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(∑ j, b i*b j*min |x i| |x j|)-(∑ j, b i*b j*min |y i| |y j|)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |b i| * |b j| * ‖x-y‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub,abs_mul,abs_mul]
      exact mul_le_mul_of_nonneg_left (covariance_difference x y i j)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      simp only [IBMUniformRidgeNativeBounds.amplitude,pow_two,
        Finset.sum_mul,Finset.mul_sum,mul_assoc]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem clock_variance (b : ι → ℝ) (r : ι → ℝ≥0) (Y : SampleSpace) :
    ‖IBMFiniteRidgeObservation.direction b r Y‖^2 =
      variance b (fun i => GaussianTimeProcess.process (r i) Y) := rfl

end OperatorDerivativeRewrite.Foundation.IBMFoldedSourceCovariance
