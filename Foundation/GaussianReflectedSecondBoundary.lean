import Foundation.GaussianRegularizedSecondDerivative
import Foundation.IBMReflectedGaussianSobolev

/-! A concrete nonsmooth reflected Gaussian cylinder retains a nonzero
second-derivative boundary channel after number regularization. -/
noncomputable section
open MeasureTheory Polynomial
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianReflectedSecondBoundary
open GaussianCore GaussianRegularizedSecondDerivative BrownianSignIntegral
set_option backward.isDefEq.respectTransparency false

theorem absolute_memLp : MemLp (fun x : ℝ => |x|) 2 γ := by
  simpa only [eval_X, Real.norm_eq_abs] using (polynomial_memLp X 2 (by simp)).norm

def absoluteClass : GaussianL2 := absolute_memLp.toLp _

theorem sign_memLp : MemLp signum 2 γ :=
  MemLp.of_bound signum_measurable.aestronglyMeasurable 1 (ae_of_all _ signum_bound)

def signClass : GaussianL2 := sign_memLp.toLp _

theorem absolute_closed_graph : (absoluteClass, signClass) ∈ closedDerivative.graph := by
  obtain ⟨hf, hg, hfg⟩ := IBMReflectedGaussianSobolev.reflected_closed_graph
    (f := fun x : ℝ => x) (g := fun _ : ℝ => 1) (fun x => hasDerivAt_id x)
    continuous_const (K := 1) (fun x => by norm_num)
  have heF : hf.toLp _ = absoluteClass := by
    apply Lp.ext
    exact hf.coeFn_toLp.trans absolute_memLp.coeFn_toLp.symm
  have heG : hg.toLp _ = signClass := by
    apply Lp.ext
    filter_upwards [hg.coeFn_toLp, sign_memLp.coeFn_toLp] with x h1 h2
    have h1' : hg.toLp (fun x => 1 * signum x) x = 1 * signum x := h1
    have h2' : signClass x = signum x := h2
    exact h1'.trans ((one_mul _).trans h2'.symm)
  rwa [heF, heG] at hfg

theorem normalizedHermite_one_ae : normalizedHermite 1 =ᵐ[γ] fun x : ℝ => x := by
  have he : normalizedHermite 1 = polynomialL2 X := by
    norm_num [normalizedHermite, hermiteVector, hermitePolynomial_succ, divergencePolynomial]
  rw [he]
  simpa only [eval_X] using polynomialL2_coeFn X

theorem sign_first_coefficient : hermiteCoefficient signClass 1 = ∫ x : ℝ, |x| ∂γ := by
  rw [hermiteCoefficient, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [normalizedHermite_one_ae, sign_memLp.coeFn_toLp] with x h1 h2
  have h2' : signClass x = signum x := h2
  rw [h1, h2']
  simp only [RCLike.inner_apply, conj_trivial]
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [signum, hx, not_lt_of_gt hx, abs_of_neg hx]
  · subst x; simp
  · simp [signum, hx, abs_of_pos hx]

/-- This is an actual nonzero Gaussian constant channel, not a formal delta. -/
theorem absolute_boundary_coefficient :
    hermiteCoefficient (regularizedSecond absoluteClass) 0 = ∫ x : ℝ, |x| ∂γ := by
  have hh := (closedDerivative_graph_iff absoluteClass signClass).mp absolute_closed_graph 1
  rw [regularizedSecond_coefficient]
  have hg : gain 0 = Real.sqrt 2 := by norm_num [gain, weight]
  rw [hg]
  norm_num at hh
  exact hh.symm.trans sign_first_coefficient

theorem absolute_mean_ne_zero : (∫ x : ℝ, |x| ∂γ) ≠ 0 := by
  intro hz
  have hi : Integrable (fun x : ℝ => |x|) γ := absolute_memLp.integrable (by simp)
  have ha : (fun x : ℝ => |x|) =ᵐ[γ] (fun _ : ℝ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg x) hi).mp hz
  have he : (fun x : ℝ => |x|) = (fun _ : ℝ => (0 : ℝ)) :=
    continuous_representation_unique continuous_abs continuous_const ha
  have hh := congrFun he 1
  norm_num at hh

theorem reflected_linear_bulk_second_zero (x : ℝ) :
    deriv (deriv (fun r : ℝ => r)) x = 0 := by simp

/-- Keeping only the bulk second derivative of the linear function and then
reflecting would give zero, contradicting the actual regularized operator. -/
theorem absolute_regularizedSecond_ne_zero : regularizedSecond absoluteClass ≠ 0 := by
  intro hz
  have hh := absolute_boundary_coefficient
  rw [hz] at hh
  simp only [hermiteCoefficient, inner_zero_right] at hh
  exact absolute_mean_ne_zero hh.symm

end OperatorDerivativeRewrite.Foundation.GaussianReflectedSecondBoundary
