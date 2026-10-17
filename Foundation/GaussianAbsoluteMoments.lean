import Foundation.GaussianHilbertProcess
import Mathlib.Probability.HasLaw

/-! Absolute moments of the actual first-chaos variables, with a uniform
standard-normal constant. No path regularity hypothesis is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianAbsoluteMoments
open InfiniteGaussian

def standardMoment (p : ℕ) : ℝ := ∫ x : ℝ, |x|^p ∂gaussianReal 0 1

theorem standard_integrable (p : ℕ) :
    Integrable (fun x : ℝ => |x|^p) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) (p : ℝ≥0∞) (by simp)).integrable_norm_pow'
  simpa only [Real.norm_eq_abs, id_eq] using h

theorem standardMoment_nonnegative (p : ℕ) : 0 ≤ standardMoment p :=
  integral_nonneg (fun x => pow_nonneg (abs_nonneg x) p)

theorem firstChaos_absolute_moment (h : CoefficientSpace) (p : ℕ) :
    (∫ ω, |firstChaosEmbedding h ω|^p ∂gaussianProduct) =
      ‖h‖^p * standardMoment p := by
  let ν := gaussianReal 0 (NNReal.mk (‖h‖^2) (sq_nonneg _))
  have hl : HasLaw (firstChaosEmbedding h) ν gaussianProduct :=
    ⟨(Lp.stronglyMeasurable _).aemeasurable, firstChaos_law h⟩
  have hs : HasLaw (fun x : ℝ => ‖h‖*x) ν (gaussianReal 0 1) := by
    refine ⟨by fun_prop, ?_⟩
    simp [ν, gaussianReal_map_const_mul]
  have hm : AEStronglyMeasurable (fun x : ℝ => |x|^p) ν := by fun_prop
  calc
    _ = ∫ x : ℝ, |x|^p ∂ν := hl.integral_comp hm
    _ = ∫ x : ℝ, |‖h‖*x|^p ∂gaussianReal 0 1 := (hs.integral_comp hm).symm
    _ = ‖h‖^p * standardMoment p := by
      simp only [abs_mul, abs_norm, mul_pow]
      rw [integral_const_mul]
      rfl

theorem firstChaos_absolute_integrable (h : CoefficientSpace) (p : ℕ) :
    Integrable (fun ω => |firstChaosEmbedding h ω|^p) gaussianProduct := by
  have hm := (firstChaos_hasGaussianLaw h).memLp (by simp : (p : ℝ≥0∞) ≠ ∞)
  simpa only [Real.norm_eq_abs] using hm.integrable_norm_pow'

end OperatorDerivativeRewrite.Foundation.GaussianAbsoluteMoments
