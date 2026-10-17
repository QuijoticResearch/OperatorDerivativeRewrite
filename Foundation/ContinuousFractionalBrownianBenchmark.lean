import Foundation.ContinuousFractionalPrediction
import Mathlib.Probability.Moments.Covariance

/-! Law-level checks for the actual continuous fractional process: the half
parameter is Brownian, while the two consecutive unit increments cannot be
independent at any other admissible parameter. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.ContinuousFractionalBrownianBenchmark
open InfiniteGaussian ContinuousFractionalBrownian GaussianAbsoluteMoments
set_option backward.isDefEq.respectTransparency false
variable (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)

theorem process_memLp (t : ℝ≥0) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (process H hH0 hH1 t) p gaussianProduct :=
  ((process_isGaussianProcess H hH0 hH1).hasGaussianLaw_eval t).memLp hp

theorem increment_absolute_moment (s t : ℝ≥0) (p : ℕ) :
    (∫ ω, |process H hH0 hH1 t ω-process H hH0 hH1 s ω|^p ∂gaussianProduct) =
      (|(t : ℝ)-s|^H)^p*standardMoment p := by
  have he : (fun ω => |process H hH0 hH1 t ω-process H hH0 hH1 s ω|^p) =ᵐ[gaussianProduct]
      (fun ω => |FractionalDyadicControl.value H hH0 hH1 t ω-
        FractionalDyadicControl.value H hH0 hH1 s ω|^p) := by
    filter_upwards [process_coordinate_ae H hH0 hH1 t, process_coordinate_ae H hH0 hH1 s]
      with ω ht hs
    rw [ht,hs]
    rfl
  rw [integral_congr_ae he]
  exact FractionalDyadicControl.increment_moment H hH0 hH1 s t p

theorem half_isBrownian :
    IsBrownianReal (process (1/2) (by norm_num) (by norm_num)) gaussianProduct := by
  refine ⟨?_, Eventually.of_forall (process_continuous (1/2) (by norm_num) (by norm_num))⟩
  apply (process_isGaussianProcess (1/2) (by norm_num) (by norm_num)).isPreBrownianReal_of_covariance
  · exact process_centered (1/2) (by norm_num) (by norm_num)
  · intro s t hst
    rw [process_covariance]
    norm_num
    rw [abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst))]
    ring

theorem consecutive_covariance :
    cov[process H hH0 hH1 1,
      (fun ω => process H hH0 hH1 2 ω-process H hH0 hH1 1 ω); gaussianProduct] =
      (2 : ℝ)^(2*H)/2-1 := by
  rw [covariance_fun_sub_right (process_memLp H hH0 hH1 1 2 (by simp))
    (process_memLp H hH0 hH1 2 2 (by simp)) (process_memLp H hH0 hH1 1 2 (by simp)),
    process_covariance, process_covariance]
  norm_num [Real.zero_rpow (by positivity : 2*H ≠ 0)]

theorem independent_consecutive_forces_half
    (hi : IndepFun (process H hH0 hH1 1)
      (fun ω => process H hH0 hH1 2 ω-process H hH0 hH1 1 ω) gaussianProduct) : H = 1/2 := by
  have hz := hi.covariance_eq_zero (process_memLp H hH0 hH1 1 2 (by simp))
    ((process_memLp H hH0 hH1 2 2 (by simp)).sub (process_memLp H hH0 hH1 1 2 (by simp)))
  rw [consecutive_covariance H hH0 hH1] at hz
  have he : (2 : ℝ)^(2*H) = (2 : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]; linarith
  have hh := (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).mp he
  linarith

theorem not_independent_consecutive (hne : H ≠ 1/2) :
    ¬ IndepFun (process H hH0 hH1 1)
      (fun ω => process H hH0 hH1 2 ω-process H hH0 hH1 1 ω) gaussianProduct :=
  fun hi => hne (independent_consecutive_forces_half H hH0 hH1 hi)

end OperatorDerivativeRewrite.Foundation.ContinuousFractionalBrownianBenchmark
