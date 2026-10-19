import Foundation.RiemannQuarticEvolution

/-! The actual real cosine transform and its zero-free imaginary axis. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticReality
open RiemannQuarticKernel RiemannQuarticDomain RiemannQuarticFlow RiemannQuarticEvolution

def realFlow (t x : ℝ) : ℝ :=
  ∫ u, weighted 0 t 0 u*Real.cos (u*x) ∂halfLine

theorem real_integrand (t x u : ℝ) :
    (weighted 0 t 0 u : ℂ)*Complex.cos ((u : ℂ)*(x : ℂ)) =
      (weighted 0 t 0 u*Real.cos (u*x) : ℝ) := by
  simp only [Complex.ofReal_mul, Complex.ofReal_cos]

theorem real_integrable (t x : ℝ) :
    Integrable (fun u : ℝ => weighted 0 t 0 u*Real.cos (u*x)) halfLine := by
  have h := (cosine_integrable t (x : ℂ)).re
  simpa only [real_integrand, RCLike.re_eq_complex_re, Complex.ofReal_re] using h

theorem flow_real (t x : ℝ) : flow t (x : ℂ) = (realFlow t x : ℂ) := by
  rw [flow_eq_cosine_integral]
  simp_rw [real_integrand]
  exact integral_ofReal

theorem flow_im_zero (t x : ℝ) : (flow t (x : ℂ)).im = 0 := by
  rw [flow_real, Complex.ofReal_im]

def imaginaryValue (t y : ℝ) : ℝ :=
  ∫ u, weighted 0 t 0 u*Real.cosh (u*y) ∂halfLine

theorem imaginary_integrand (t y u : ℝ) :
    (weighted 0 t 0 u : ℂ)*Complex.cos ((u : ℂ)*(Complex.I*(y : ℂ))) =
      (weighted 0 t 0 u*Real.cosh (u*y) : ℝ) := by
  rw [show (u : ℂ)*(Complex.I*(y : ℂ))=((u*y : ℝ) : ℂ)*Complex.I by push_cast; ring,
    Complex.cos_mul_I, ← Complex.ofReal_cosh, ← Complex.ofReal_mul]

theorem imaginary_integrable (t y : ℝ) :
    Integrable (fun u : ℝ => weighted 0 t 0 u*Real.cosh (u*y)) halfLine := by
  have h := (cosine_integrable t (Complex.I*(y : ℂ))).re
  simpa only [imaginary_integrand, RCLike.re_eq_complex_re, Complex.ofReal_re] using h

theorem flow_imaginary (t y : ℝ) :
    flow t (Complex.I*(y : ℂ)) = (imaginaryValue t y : ℂ) := by
  rw [flow_eq_cosine_integral]
  simp_rw [imaginary_integrand]
  exact integral_ofReal

theorem imaginaryValue_pos (t y : ℝ) : 0 < imaginaryValue t y := by
  have hp (u : ℝ) (hu : 0 ≤ u) : 0 < weighted 0 t 0 u*Real.cosh (u*y) := by
    unfold weighted
    exact mul_pos (mul_pos (by simp only [pow_zero, zero_mul, add_zero, one_mul]; positivity)
      (kernel_pos u hu)) (Real.cosh_pos _)
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (μ := volume) (s := Ici (0 : ℝ))
    (by filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu; exact (hp u hu).le)
    (imaginary_integrable t y)).mpr
  have hs : Icc (0 : ℝ) 1 ⊆
      Function.support (fun u : ℝ => weighted 0 t 0 u*Real.cosh (u*y)) ∩ Ici 0 := by
    intro u hu
    exact ⟨(hp u hu.1).ne', hu.1⟩
  exact lt_of_lt_of_le (by simp : 0 < volume (Icc (0 : ℝ) 1)) (measure_mono hs)

theorem flow_ne_zero_on_imaginary_axis (t y : ℝ) : flow t (Complex.I*(y : ℂ)) ≠ 0 := by
  rw [flow_imaginary]
  exact_mod_cast (imaginaryValue_pos t y).ne'

end OperatorDerivativeRewrite.Foundation.RiemannQuarticReality
