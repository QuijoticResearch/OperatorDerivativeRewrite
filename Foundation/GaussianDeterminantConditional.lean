import Foundation.TensorSymmetryDeterminantMoments
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod

/-! A row of an independent Gaussian determinant can be integrated exactly. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianDeterminantConditional
set_option backward.isDefEq.respectTransparency false

abbrev rowMeasure : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

def determinant (u v : ℝ × ℝ) : ℝ := 2 * (u.1 * v.2 - u.2 * v.1)

def phase (t x : ℝ) : ℂ := Complex.exp ((t * x : ℝ) * Complex.I)

theorem standard_phase_integral (s : ℝ) :
    (∫ x, phase s x ∂gaussianReal 0 1) = Complex.exp (-(s : ℂ)^2 / 2) := by
  have h := charFun_gaussianReal (μ := 0) (v := 1) s
  rw [charFun_apply_real] at h
  simpa [phase, neg_div] using h

theorem determinant_phase_factor (t : ℝ) (u v : ℝ × ℝ) :
    phase t (determinant u v) = phase (-2*t*u.2) v.1 * phase (2*t*u.1) v.2 := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  unfold determinant
  push_cast
  ring

/-- Integrating the second row gives a radial Gaussian damping factor in the first row. -/
theorem row_phase_integral (t : ℝ) (u : ℝ × ℝ) :
    (∫ v, phase t (determinant u v) ∂rowMeasure) =
      Complex.exp ((-2*t^2*(u.1^2+u.2^2) : ℝ) : ℂ) := by
  simp_rw [determinant_phase_factor]
  rw [rowMeasure, integral_prod_mul, standard_phase_integral, standard_phase_integral,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A Gaussian square Laplace transform, before simplifying its positive square root. -/
theorem square_laplace (c : ℝ) :
    (∫ x : ℝ, Real.exp (-c*x^2) ∂gaussianReal 0 1) =
      (Real.sqrt (2*Real.pi))⁻¹ * Real.sqrt (Real.pi / (c+1/2)) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have he (x : ℝ) : gaussianPDFReal 0 1 x • Real.exp (-c*x^2) =
      (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(c+1/2)*x^2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_gaussian]

theorem square_laplace_squared (c : ℝ) (hc : 0 ≤ c) :
    (∫ x : ℝ, Real.exp (-c*x^2) ∂gaussianReal 0 1)^2 = 1/(1+2*c) := by
  rw [square_laplace, mul_pow, inv_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi),
    Real.sq_sqrt (by positivity : 0 ≤ Real.pi/(c+1/2))]
  have hp := Real.pi_pos
  have hd : 0 < c+1/2 := by positivity
  field_simp
  ring

/-- The radial damping factor has a rational Gaussian average. -/
theorem radial_average (t : ℝ) :
    (∫ u : ℝ × ℝ, Real.exp (-2*t^2*(u.1^2+u.2^2)) ∂rowMeasure) =
      1/(1+4*t^2) := by
  have he (u : ℝ × ℝ) : Real.exp (-2*t^2*(u.1^2+u.2^2)) =
      Real.exp (-(2*t^2)*u.1^2) * Real.exp (-(2*t^2)*u.2^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [rowMeasure, integral_prod_mul (fun x : ℝ => Real.exp (-(2*t^2)*x^2))
    (fun x : ℝ => Real.exp (-(2*t^2)*x^2)), ← pow_two,
    square_laplace_squared _ (by positivity)]
  congr 2
  ring

theorem determinant_phase_integrable (t : ℝ) :
    Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => phase t (determinant z.1 z.2))
      (rowMeasure.prod rowMeasure) := by
  apply Integrable.of_bound (by unfold phase determinant; fun_prop) 1
  exact Filter.Eventually.of_forall fun z =>
    le_of_eq (Complex.norm_exp_ofReal_mul_I (t * determinant z.1 z.2))

/-- The characteristic function of the explicit four independent Gaussian model. -/
theorem determinant_phase_integral (t : ℝ) :
    (∫ z : (ℝ × ℝ) × (ℝ × ℝ), phase t (determinant z.1 z.2)
      ∂rowMeasure.prod rowMeasure) = ((1/(1+4*t^2) : ℝ) : ℂ) := by
  rw [integral_prod _ (determinant_phase_integrable t)]
  simp_rw [row_phase_integral, ← Complex.ofReal_exp]
  rw [integral_complex_ofReal, radial_average]

def determinantLaw : Measure ℝ :=
  (rowMeasure.prod rowMeasure).map (fun z => determinant z.1 z.2)

theorem determinantLaw_charFun (t : ℝ) :
    charFun determinantLaw t = ((1/(1+4*t^2) : ℝ) : ℂ) := by
  rw [charFun_apply_real, determinantLaw,
    integral_map (by unfold determinant; fun_prop) (by fun_prop)]
  simpa only [phase, Complex.ofReal_mul] using determinant_phase_integral t

end OperatorDerivativeRewrite.Foundation.GaussianDeterminantConditional
