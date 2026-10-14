import Foundation.IBMVarianceCancellation
import Foundation.FractionalCovarianceMatrices

/-! Positive-half-line Brownian bulk variance for shifted finite source averages. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMFiniteBulkVariance
open InfiniteGaussian FractionalSpectralKernel FractionalSpectralGeometry
open GaussianHilbertProcess IBMFiniteScenerySmoothing
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

def shiftedDirection (I : Finset ℝ) (w : ℝ → ℝ) (x : ℝ) : SpectralSpace :=
  ∑ r ∈ I, w r • direction (x + r)

theorem positive_shifted_direction_inner (x r s : ℝ)
    (hr : 0 ≤ x + r) (hs : 0 ≤ x + s) :
    inner ℝ (direction (x + r)) (direction (x + s)) = x + min r s := by
  rw [show inner ℝ (direction (x + r)) (direction (x + s)) =
      covariance (1/2) (x + r) (x + s) by
        simp only [direction, normalized_inner]]
  rw [FractionalCovarianceMatrices.brownian_covariance _ _ hr hs]
  simp [min_add_add_left]

theorem shiftedDirection_inner (I J : Finset ℝ) (w v : ℝ → ℝ) (x : ℝ)
    (hI : ∀ r ∈ I, 0 ≤ x + r) (hJ : ∀ s ∈ J, 0 ≤ x + s) :
    inner ℝ (shiftedDirection I w x) (shiftedDirection J v x) =
      ∑ r ∈ I, ∑ s ∈ J, w r * v s * (x + min r s) := by
  simp only [shiftedDirection, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [positive_shifted_direction_inner x r s (hI r hr) (hJ s hs)]
  ring

theorem shiftedDirection_affine_variance (I : Finset ℝ) (w : ℝ → ℝ) (x : ℝ)
    (hI : ∀ r ∈ I, 0 ≤ x + r) (hmass : ∑ r ∈ I, w r = 1) :
    ‖shiftedDirection I w x‖^2 =
      x + ∑ r ∈ I, ∑ s ∈ I, w r * w s * min r s := by
  rw [← real_inner_self_eq_norm_sq, shiftedDirection_inner I I w w x hI hI]
  simp_rw [mul_add]
  simp only [Finset.sum_add_distrib]
  have hprod : (∑ r ∈ I, ∑ s ∈ I, w r * w s * x) = x := by
    simp_rw [mul_assoc]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, hmass]
    ring
  rw [hprod]

end OperatorDerivativeRewrite.Foundation.IBMFiniteBulkVariance
