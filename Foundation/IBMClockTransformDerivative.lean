import Foundation.IBMGaussianLaplaceBoundary
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation of the actual Gaussian-clock Laplace transform. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockTransformDerivative
open IBMOneTimeFourier IBMGaussianLaplaceBoundary

theorem absolute_integrable : Integrable (fun r : ℝ => |r|) (gaussianReal 0 1) := by
  simpa only [Real.norm_eq_abs,id_eq] using
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).norm

theorem transform_integrable (b : ℝ) (hb : 0 ≤ b) :
    Integrable (fun r : ℝ => Real.exp (-b*|r|)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards with r
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (Real.exp_le_one_iff).mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (abs_nonneg r))

theorem parameter_derivative_integral (b : ℝ) (hb : 0 < b) :
    HasDerivAt (clockTransform 1)
      (∫ r : ℝ, -|r| * Real.exp (-b*|r|) ∂gaussianReal 0 1) b := by
  let F := fun s r : ℝ => Real.exp (-s*|r|)
  let F' := fun s r : ℝ => -|r| * Real.exp (-s*|r|)
  have hs : Ioi (0 : ℝ) ∈ 𝓝 b := Ioi_mem_nhds hb
  have hm : ∀ s, AEStronglyMeasurable (F s) (gaussianReal 0 1) := by
    intro s
    dsimp [F]
    fun_prop
  have hdm : AEStronglyMeasurable (F' b) (gaussianReal 0 1) := by
    dsimp [F']
    fun_prop
  have hbound : ∀ᵐ r ∂gaussianReal 0 1, ∀ s ∈ Ioi (0 : ℝ), ‖F' s r‖ ≤ |r| := by
    filter_upwards with r s hs
    have he : Real.exp (-s*|r|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (abs_nonneg r))
    calc
      ‖F' s r‖ = |r| * Real.exp (-s*|r|) := by
        simp [F',norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      _ ≤ |r| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg r)
      _ = |r| := mul_one _
  have hd : ∀ᵐ r ∂gaussianReal 0 1, ∀ s ∈ Ioi (0 : ℝ),
      HasDerivAt (F · r) (F' s r) s := by
    filter_upwards with r s _
    convert (((hasDerivAt_id s).neg.mul_const |r|).exp) using 1 <;>
      simp [F,F'] <;> ring
  obtain ⟨_, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall hm) (transform_integrable b hb.le) hdm hbound absolute_integrable hd
  exact h

theorem parameter_derivative (b : ℝ) (hb : 0 < b) :
    HasDerivAt (clockTransform 1) (b*clockTransform 1 b-2*gaussianConstant) b := by
  have h := parameter_derivative_integral b hb
  have he : (∫ r : ℝ, -|r| * Real.exp (-b*|r|) ∂gaussianReal 0 1) =
      b*clockTransform 1 b-2*gaussianConstant := by
    have heq : (fun r : ℝ => -|r| * Real.exp (-b*|r|)) =
        fun r => -(|r| * Real.exp (-b*|r|)) := by funext r; ring
    rw [heq,integral_neg,gaussian_boundary_identity b hb.le]
    ring
  rwa [he] at h

end OperatorDerivativeRewrite.Foundation.IBMClockTransformDerivative
