import Foundation.IBMFourierTimeEquation
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The initial square-root cusp of the actual Gaussian-clock transform. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMInitialCusp
open IBMOneTimeFourier IBMGaussianLaplaceBoundary IBMClockTransformDerivative
open IBMClockTimeEvolution IBMFourierTimeEquation

theorem weighted_absolute_integrable :
    Integrable (fun r : ℝ => |r| * Real.exp |r|) (gaussianReal 0 1) := by
  have h := integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
    (X := fun r : ℝ => r) (μ := gaussianReal 0 1) (v := 0) (t := 2) (x := 1)
    (integrable_exp_mul_gaussianReal (0+2)) (integrable_exp_mul_gaussianReal (0-2))
    (by norm_num) (by norm_num) 1
  simpa using h

theorem parameter_derivative_zero :
    HasDerivAt (clockTransform 1) (-2*gaussianConstant) 0 := by
  let F := fun s r : ℝ => Real.exp (-s*|r|)
  let F' := fun s r : ℝ => -|r| * Real.exp (-s*|r|)
  have hs : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hm : ∀ s, AEStronglyMeasurable (F s) (gaussianReal 0 1) := by
    intro s
    dsimp [F]
    fun_prop
  have hi : Integrable (F 0) (gaussianReal 0 1) := by simpa [F] using integrable_const (1 : ℝ)
  have hdm : AEStronglyMeasurable (F' 0) (gaussianReal 0 1) := by
    dsimp [F']
    fun_prop
  have hbound : ∀ᵐ r ∂gaussianReal 0 1, ∀ s ∈ Ioo (-1 : ℝ) 1,
      ‖F' s r‖ ≤ |r| * Real.exp |r| := by
    filter_upwards with r s hs
    have he : -s*|r| ≤ |r| := by nlinarith [abs_nonneg r, hs.1]
    calc
      ‖F' s r‖ = |r| * Real.exp (-s*|r|) := by
        simp [F',norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      _ ≤ |r| * Real.exp |r| := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (abs_nonneg r)
  have hd : ∀ᵐ r ∂gaussianReal 0 1, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (F · r) (F' s r) s := by
    filter_upwards with r s _
    convert (((hasDerivAt_id s).neg.mul_const |r|).exp) using 1 <;>
      simp [F,F'] <;> ring
  obtain ⟨_, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall hm) hi hdm hbound weighted_absolute_integrable hd
  have he : (∫ r : ℝ, F' 0 r ∂gaussianReal 0 1) = -2*gaussianConstant := by
    simp only [F',neg_zero,zero_mul,Real.exp_zero,mul_one]
    rw [integral_neg]
    have hg := gaussian_boundary_identity 0 (by norm_num)
    simpa using congrArg Neg.neg hg
  change HasDerivAt (clockTransform 1) _ 0 at h
  rwa [he] at h

theorem square_time (a s : ℝ) (hs : 0 ≤ s) :
    timeTransform a (s^2) = clockTransform 1 (a*s) := by
  rw [timeTransform_eq a (s^2) (sq_nonneg _),Real.sqrt_sq hs]

theorem no_initial_right_derivative (a d : ℝ) (ha : a ≠ 0) :
    ¬ HasDerivWithinAt (timeTransform a) d (Ici 0) 0 := by
  intro hd
  have hsq : HasDerivWithinAt (fun s : ℝ => s^2) 0 (Ici 0) 0 := by
    simpa [Pi.pow_apply,id_eq] using ((hasDerivAt_id (0 : ℝ)).fun_pow 2).hasDerivWithinAt (s := Ici 0)
  have hc := hd.comp_of_eq 0 hsq (fun s _ => sq_nonneg s) (by norm_num)
  have hp := (parameter_derivative_zero.comp_of_eq 0
    ((hasDerivAt_id (0 : ℝ)).const_mul a) (by simp)).hasDerivWithinAt (s := Ici 0)
  have he : (fun s : ℝ => timeTransform a (s^2)) =ᶠ[𝓝[Ici 0] 0]
      fun s => clockTransform 1 (a*s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact square_time a s hs
  have hp' := hp.congr_of_eventuallyEq he (by simp [timeTransform,clockTransform])
  change HasDerivWithinAt (fun s : ℝ => timeTransform a (s^2)) (d*0) (Ici 0) 0 at hc
  have hu := (hc.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
    (hp'.derivWithin (uniqueDiffWithinAt_Ici 0))
  have hg : 0 < gaussianConstant := by unfold gaussianConstant; positivity
  have hzero : a=0 := by nlinarith
  exact ha hzero

end OperatorDerivativeRewrite.Foundation.IBMInitialCusp
