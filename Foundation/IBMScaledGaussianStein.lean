import Foundation.HelicalWeightedPressureIBP
import Foundation.RealSteklovApprox

/-! Scaled Gaussian Stein identities, reusing the genuine weighted
integration-by-parts domain already verified for the quarter Gaussian.
No nonzero-scale assumption or unbounded multiplier rule is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.IBMScaledGaussianStein
open HelicalWeightedPressureIBP

theorem bounded_integrable {g : ℝ → ℝ} (hc : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) : Integrable g ν := by
  exact (MemLp.of_bound hc.aestronglyMeasurable M
    (Filter.Eventually.of_forall hM) : MemLp g 1 ν).integrable (by norm_num)

theorem coordinate_mul_integrable {g : ℝ → ℝ} (hc : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) : Integrable (fun x => x*g x) ν := by
  have hi : Integrable (fun x : ℝ => x) ν :=
    (memLp_id_gaussianReal (μ := 0) (v := 1/4) 1).integrable (by norm_num)
  apply Integrable.mono' (hi.abs.mul_const M) (continuous_id.mul hc).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    change ‖x * g x‖ ≤ |x| * M
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg x)

theorem square_mul_integrable {g : ℝ → ℝ} (hc : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) : Integrable (fun x => x^2*g x) ν := by
  have hi : Integrable (fun x : ℝ => x^2) ν := by
    simpa only [id_eq] using
      (memLp_id_gaussianReal (μ := 0) (v := 1/4) 2).integrable_sq
  apply Integrable.mono' (hi.mul_const M) ((continuous_id.pow 2).mul hc).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    change ‖x^2 * g x‖ ≤ x^2 * M
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hM x) (sq_nonneg x)

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {A B C : ℝ}
  (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖deriv φ x‖ ≤ B)
  (hC : ∀ x, ‖deriv (deriv φ) x‖ ≤ C)

include hφ in
theorem scaled_hasDerivAt (a x : ℝ) :
    HasDerivAt (fun t => φ (a*t)) (a * deriv φ (a*x)) x := by
  have h := ((hφ.differentiable (by norm_num) (a*x)).hasDerivAt).comp x
    ((hasDerivAt_id x).const_mul a)
  convert h using 1 <;> first | rfl | ring

include hφ hA hB in
/-- The first Stein identity at every real scale, including scale zero. -/
theorem scaled_first (a : ℝ) :
    (∫ x, (a*x)*φ (a*x) ∂ν) = (a^2/4) * (∫ x, deriv φ (a*x) ∂ν) := by
  have hc : Continuous (fun x => φ (a*x)) :=
    hφ.continuous.comp (continuous_const.mul continuous_id)
  have hdc : Continuous (fun x => deriv φ (a*x)) :=
    (hφ.continuous_deriv (by norm_num)).comp (continuous_const.mul continuous_id)
  have he := HelicalWeightedPressureIBP.stein_integrable
    (scaled_hasDerivAt hφ a)
    (bounded_integrable hc (fun x => hA _))
    ((bounded_integrable hdc (fun x => hB _)).const_mul a)
    (coordinate_mul_integrable hc (fun x => hA _))
  rw [integral_const_mul] at he
  have hf : (fun x : ℝ => (a*x)*φ (a*x)) = fun x => a*(x*φ (a*x)) := by
    funext x; ring
  rw [hf, integral_const_mul]
  linear_combination -(a/4)*he

include hφ hA hB hC in
/-- The second centered identity retains genuine coordinate-square
integrability; it does not infer boundedness of x times a bounded test. -/
theorem scaled_second (a : ℝ) :
    (∫ x, ((a*x)^2-a^2/4)*φ (a*x) ∂ν) =
      (a^4/16)*(∫ x, deriv (deriv φ) (a*x) ∂ν) := by
  have hc : Continuous (fun x => φ (a*x)) :=
    hφ.continuous.comp (continuous_const.mul continuous_id)
  have hd := RealSteklovApprox.deriv_contDiff_one φ hφ
  have hdc : Continuous (fun x => deriv φ (a*x)) :=
    hd.continuous.comp (continuous_const.mul continuous_id)
  have hddc : Continuous (fun x => deriv (deriv φ) (a*x)) :=
    hd.continuous_deriv_one.comp (continuous_const.mul continuous_id)
  have hdd (x : ℝ) : HasDerivAt (fun t => a*deriv φ (a*t))
      (a^2*deriv (deriv φ) (a*x)) x := by
    have he := (((hd.differentiable (by norm_num) (a*x)).hasDerivAt).comp x
      ((hasDerivAt_id x).const_mul a)).const_mul a
    convert he using 1 <;> first | rfl | ring
  have hxg : Integrable (fun x => x*(a*deriv φ (a*x))) ν := by
    have hi := (coordinate_mul_integrable hdc (fun x => hB _)).const_mul a
    convert hi using 1
    funext x; ring
  have he := HelicalWeightedPressureIBP.centered_second
    (scaled_hasDerivAt hφ a) hdd
    (bounded_integrable hc (fun x => hA _))
    ((bounded_integrable hdc (fun x => hB _)).const_mul a)
    ((bounded_integrable hddc (fun x => hC _)).const_mul (a^2))
    (coordinate_mul_integrable hc (fun x => hA _))
    (square_mul_integrable hc (fun x => hA _)) hxg
  have hf : (fun x : ℝ => ((a*x)^2-a^2/4)*φ (a*x)) =
      fun x => a^2*((x^2-1/4)*φ (a*x)) := by
    funext x; ring
  rw [hf, integral_const_mul, he, integral_const_mul]
  ring

end OperatorDerivativeRewrite.Foundation.IBMScaledGaussianStein
