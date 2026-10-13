import Foundation.FractionalGaussianProcess
import Foundation.GaussianQuadraticIncrement
import Mathlib.Analysis.Calculus.Taylor

/-! A legitimate first-order controlled estimate for smooth functions of the
fractional Gaussian process. This is a mean-square theorem about f(X_t), not
about conditional forecasts, and it does not assert sample-path rough regularity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.FractionalControlledEstimate
open InfiniteGaussian FractionalGaussianProcess FractionalSpectralGeometry
open FractionalSpectralKernel SeparableHilbertEmbedding GaussianQuadraticIncrement
attribute [local instance] spectralSpace_secondCountable
variable (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)

def square (h : CoefficientSpace) : GaussianL2 :=
  (centeredSquare h : GaussianL2) + ‖h‖^2 • gaussianOne

theorem square_coeFn (h : CoefficientSpace) :
    square h =ᵐ[gaussianProduct] fun ω => (firstChaosEmbedding h ω)^2 := by
  filter_upwards [centeredSquare_coeFn h,
    Lp.coeFn_add (centeredSquare h : GaussianL2) (‖h‖^2 • gaussianOne),
    Lp.coeFn_smul (‖h‖^2) gaussianOne, gaussianOne_coeFn] with ω hc ha hs ho
  change square h ω = _
  rw [square, ha]
  simp only [Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul, ho, mul_one, hc]
  ring

theorem square_norm_sq (h : CoefficientSpace) : ‖square h‖^2 = 3 * (‖h‖^2)^2 := by
  rw [square, norm_add_sq_real, norm_smul, mul_pow, centeredSquare_norm_sq,
    real_inner_smul_right, real_inner_comm, centeredSquare_centered,
    ← real_inner_self_eq_norm_sq gaussianOne,
    GaussianDeterministicGraphCore.gaussianOne_inner_self]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

def remainder (f : ℝ → ℝ) (x y : ℝ) : ℝ := f y - f x - deriv f x * (y-x)

theorem remainder_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (M : ℝ)
    (hM : ∀ x, ‖deriv (deriv f) x‖ ≤ M) (x y : ℝ) :
    ‖remainder f x y‖ ≤ (M/2) * |y-x|^2 := by
  by_cases hxy : x = y
  · subst y
    simp [remainder]
  obtain ⟨z, _, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy hf.contDiffOn
  have he : taylorWithinEval f 1 (uIcc x y) x y = f x + deriv f x * (y-x) := by
    rw [taylorWithinEval_succ f 0, taylor_within_zero_eval]
    simp only [Nat.zero_add]
    rw [
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
        (hf.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2)).contDiffAt left_mem_uIcc]
    simp [mul_comm]
  rw [he] at hz
  have hr : remainder f x y = deriv (deriv f) z * (y-x)^2 / 2 := by
    norm_num [iteratedDeriv_succ, iteratedDeriv_zero] at hz
    dsimp [remainder]
    linarith
  have hh := mul_le_mul_of_nonneg_right (hM z) (sq_nonneg (y-x))
  rw [hr, norm_div, norm_mul, norm_pow, Real.norm_eq_abs (y-x), sq_abs]
  norm_num
  simp only [Real.norm_eq_abs] at hh
  nlinarith
def incrementDirection (s t : ℝ≥0) : CoefficientSpace :=
  direction H hH0 hH1 t - direction H hH0 hH1 s

theorem increment_coeFn (s t : ℝ≥0) :
    firstChaosEmbedding (incrementDirection H hH0 hH1 s t) =ᵐ[gaussianProduct]
      fun ω => process H hH0 hH1 t ω - process H hH0 hH1 s ω := by
  rw [incrementDirection, map_sub]
  filter_upwards [Lp.coeFn_sub (value H hH0 hH1 t) (value H hH0 hH1 s)] with ω he
  exact he
theorem increment_norm (s t : ℝ≥0) :
    ‖incrementDirection H hH0 hH1 s t‖ = |(t:ℝ)-s|^H := by
  change ‖hilbertEmbedding SpectralSpace _ - hilbertEmbedding SpectralSpace _‖ = _
  rw [← map_sub, (hilbertEmbedding SpectralSpace).norm_map, normalized_sub_norm]

theorem remainder_measurable (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (s t : ℝ≥0) :
    Measurable (fun ω => remainder f (process H hH0 hH1 s ω) (process H hH0 hH1 t ω)) := by
  have hd : Continuous (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.continuous_iteratedDeriv 1 (by norm_num)
  exact ((hf.continuous.measurable.comp (process_measurable H hH0 hH1 t)).sub
    (hf.continuous.measurable.comp (process_measurable H hH0 hH1 s))).sub
    ((hd.measurable.comp (process_measurable H hH0 hH1 s)).mul
      ((process_measurable H hH0 hH1 t).sub (process_measurable H hH0 hH1 s)))

theorem remainder_memLp (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (M : ℝ)
    (hM : ∀ x, ‖deriv (deriv f) x‖ ≤ M) (s t : ℝ≥0) :
    MemLp (fun ω => remainder f (process H hH0 hH1 s ω) (process H hH0 hH1 t ω))
      2 gaussianProduct := by
  apply (Lp.memLp (square (incrementDirection H hH0 hH1 s t))).of_le_mul
    (remainder_measurable H hH0 hH1 f hf s t).aestronglyMeasurable (c := M/2)
  filter_upwards [square_coeFn (incrementDirection H hH0 hH1 s t),
    increment_coeFn H hH0 hH1 s t] with ω hs hi
  simpa only [hs, hi, norm_pow, Real.norm_eq_abs] using
    remainder_bound f hf M hM (process H hH0 hH1 s ω) (process H hH0 hH1 t ω)

def remainderL2 (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (M : ℝ)
    (hM : ∀ x, ‖deriv (deriv f) x‖ ≤ M) (s t : ℝ≥0) : GaussianL2 :=
  (remainder_memLp H hH0 hH1 f hf M hM s t).toLp _

theorem remainderL2_coeFn (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (M : ℝ)
    (hM : ∀ x, ‖deriv (deriv f) x‖ ≤ M) (s t : ℝ≥0) :
    remainderL2 H hH0 hH1 f hf M hM s t =ᵐ[gaussianProduct]
      fun ω => remainder f (process H hH0 hH1 s ω) (process H hH0 hH1 t ω) := MemLp.coeFn_toLp _

theorem remainderL2_norm_sq (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (M : ℝ)
    (hM : ∀ x, ‖deriv (deriv f) x‖ ≤ M) (s t : ℝ≥0) :
    ‖remainderL2 H hH0 hH1 f hf M hM s t‖^2 ≤ 3*(M/2)^2*|(t:ℝ)-s|^(4*H) := by
  have hb : ‖remainderL2 H hH0 hH1 f hf M hM s t‖ ≤
      (M/2) * ‖square (incrementDirection H hH0 hH1 s t)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [remainderL2_coeFn H hH0 hH1 f hf M hM s t,
      square_coeFn (incrementDirection H hH0 hH1 s t),
      increment_coeFn H hH0 hH1 s t] with ω hr hs hi
    simpa only [hr, hs, hi, norm_pow, Real.norm_eq_abs] using
      remainder_bound f hf M hM (process H hH0 hH1 s ω) (process H hH0 hH1 t ω)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, square_norm_sq, increment_norm] at hs
  have he : ((|(t:ℝ)-s|^H) ^ (2:ℕ))^(2:ℕ) = |(t:ℝ)-s|^(4*H) := by
    rw [← pow_mul, ← Real.rpow_mul_natCast (abs_nonneg _)]
    congr 1
    norm_num
    ring
  rw [he] at hs
  nlinarith

end OperatorDerivativeRewrite.Foundation.FractionalControlledEstimate
