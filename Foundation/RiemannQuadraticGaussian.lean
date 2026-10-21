import Foundation.RiemannEvenEvolution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine Gaussian translation of the arithmetic quadratic flow and all Fourier jets.
Actual product integrability is established before every Fubini interchange. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Complex Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticGaussian
open RiemannEvenDomain RiemannEvenFlow
open RiemannQuarticFlow (halfLine)

def law (s : ℝ≥0) : Measure ℝ := gaussianReal 0 (2*s)

instance law_probability (s : ℝ≥0) : IsProbabilityMeasure (law s) := by
  unfold law
  infer_instance

theorem gaussian_phase_integrable (s : ℝ≥0) (q : ℂ) :
    Integrable (fun y : ℝ => Complex.exp (q*(y : ℂ))) (law s) := by
  apply integrable_cexp_mul_of_re_mem_integrableExpSet
    (X := fun y : ℝ => y) (by fun_prop)
  simp [law]

theorem gaussian_phase_integral (s : ℝ≥0) (q : ℂ) :
    (∫ y : ℝ, Complex.exp (q*(y : ℂ)) ∂law s) = Complex.exp ((s : ℂ)*q^2) := by
  have h := complexMGF_id_gaussianReal (μ := 0) (v := 2*s) q
  change (∫ y : ℝ, Complex.exp (q*(y : ℂ)) ∂law s) =
    Complex.exp (q*(0 : ℂ)+((2*s : ℝ≥0) : ℂ)*q^2/2) at h
  rw [h]
  congr 1
  push_cast
  ring

theorem gaussian_real_integral (s : ℝ≥0) (b : ℝ) :
    (∫ y : ℝ, Real.exp (b*y) ∂law s) = Real.exp ((s : ℝ)*b^2) := by
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 2*s)) b
  change (∫ y : ℝ, Real.exp (b*y) ∂law s) =
    Real.exp (0*b+((2*s : ℝ≥0) : ℝ)*b^2/2) at h
  rw [h]
  congr 1
  push_cast
  ring

def kernel (t : ℝ) (j : ℕ) (z c : ℂ) (u y : ℝ) : ℂ :=
  integrand 1 j t (z+c*(y : ℂ)) u

theorem kernel_factor (t : ℝ) (j : ℕ) (z c : ℂ) (u y : ℝ) :
    kernel t j z c u y = integrand 1 j t z u *
      Complex.exp ((Complex.I*(u : ℂ)*c)*(y : ℂ)) := by
  unfold kernel integrand
  rw [show Complex.I*(u : ℂ)*(z+c*(y : ℂ)) =
    Complex.I*(u : ℂ)*z+(Complex.I*(u : ℂ)*c)*(y : ℂ) by ring, Complex.exp_add]
  ring

theorem integrand_norm (t : ℝ) (j : ℕ) (z : ℂ) (u : ℝ) (hu : 0 ≤ u) :
    ‖integrand 1 j t z u‖ = weighted 1 j t (-z.im) u := by
  have hw := weighted_nonneg 1 0 t 0 u hu
  have hr : (Complex.I*(u : ℂ)*z).re = -u*z.im := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im]
    ring
  simp only [integrand,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_I,one_mul,Complex.norm_exp]
  rw [abs_of_nonneg hw,abs_of_nonneg hu,hr]
  unfold weighted
  simp only [pow_zero,one_mul,zero_mul,add_zero]
  rw [Real.exp_add]
  ring

theorem kernel_norm_integral (s : ℝ≥0) (t : ℝ) (j : ℕ) (z c : ℂ)
    (u : ℝ) (hu : 0 ≤ u) :
    (∫ y : ℝ, ‖kernel t j z c u y‖ ∂law s) =
      weighted 1 j (t+(s : ℝ)*c.im^2) (-z.im) u := by
  have hphase (y : ℝ) :
      ‖Complex.exp ((Complex.I*(u : ℂ)*c)*(y : ℂ))‖ =
        Real.exp ((-u*c.im)*y) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im]
    ring
  simp_rw [kernel_factor,norm_mul,integrand_norm t j z u hu,hphase]
  rw [integral_const_mul,gaussian_real_integral]
  have he : t*u^2+(-z.im)*u+(s : ℝ)*(-u*c.im)^2 =
      (t+(s : ℝ)*c.im^2)*u^2+(-z.im)*u := by ring
  change (u^j*Real.exp (t*u^2+(-z.im)*u)*RiemannQuarticKernel.kernel u)*
    Real.exp ((s : ℝ)*(-u*c.im)^2) =
    u^j*Real.exp ((t+(s : ℝ)*c.im^2)*u^2+(-z.im)*u)*RiemannQuarticKernel.kernel u
  have hexp : Real.exp ((t+(s : ℝ)*c.im^2)*u^2+(-z.im)*u) =
      Real.exp (t*u^2+(-z.im)*u)*Real.exp ((s : ℝ)*(-u*c.im)^2) := by
    rw [← he,Real.exp_add]
  rw [hexp]
  ring

theorem kernel_integrable (s : ℝ≥0) (t : ℝ) (j : ℕ) (z c : ℂ) :
    Integrable (fun p : ℝ × ℝ => kernel t j z c p.1 p.2) (halfLine.prod (law s)) := by
  have hw : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (weighted 1 0 t 0 p.1 : ℂ)) (halfLine.prod (law s)) :=
    (weighted_integrable 1 0 t 0).ofReal.aestronglyMeasurable.comp_fst
  have hp : Continuous (fun p : ℝ × ℝ => (Complex.I*(p.1 : ℂ))^j*
      Complex.exp (Complex.I*(p.1 : ℂ)*(z+c*(p.2 : ℂ)))) := by fun_prop
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => kernel t j z c p.1 p.2) (halfLine.prod (law s)) := by
    simpa only [kernel,integrand,Pi.mul_def,mul_assoc] using hw.mul hp.aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards with u
    exact ((gaussian_phase_integrable s (Complex.I*(u : ℂ)*c)).const_mul
      (integrand 1 j t z u)).congr (Eventually.of_forall fun y =>
        (kernel_factor t j z c u y).symm)
  · apply (weighted_integrable 1 j (t+(s : ℝ)*c.im^2) (-z.im)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact (kernel_norm_integral s t j z c u hu).symm

theorem kernel_integral (s : ℝ≥0) (t : ℝ) (j : ℕ) (z c : ℂ) (u : ℝ) :
    (∫ y : ℝ, kernel t j z c u y ∂law s) =
      integrand 1 j t z u * Complex.exp ((s : ℂ)*(Complex.I*(u : ℂ)*c)^2) := by
  simp_rw [kernel_factor]
  rw [integral_const_mul,gaussian_phase_integral]

theorem shifted_jet_integrable (s : ℝ≥0) (t : ℝ) (j : ℕ) (z c : ℂ) :
    Integrable (fun y : ℝ => jet 1 j t (z+c*(y : ℂ))) (law s) := by
  simpa only [jet,kernel] using (kernel_integrable s t j z c).integral_prod_right

theorem shifted_jet_average (s : ℝ≥0) (t delta : ℝ) (j : ℕ) (z c : ℂ)
    (hc : c^2 = (delta : ℂ)) :
    (∫ y : ℝ, jet 1 j t (z+c*(y : ℂ)) ∂law s) =
      jet 1 j (t-(s : ℝ)*delta) z := by
  have hproduct := kernel_integrable s t j z c
  calc
    _ = ∫ u : ℝ, ∫ y : ℝ, kernel t j z c u y ∂law s ∂halfLine :=
      (integral_integral_swap hproduct).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [kernel_integral]
      have he : (s : ℂ)*(Complex.I*(u : ℂ)*c)^2 =
          ((-(s : ℝ)*delta*u^2 : ℝ) : ℂ) := by
        calc
          _ = -(s : ℂ)*(u : ℂ)^2*c^2 := by
            ring_nf
            simp [Complex.I_sq]
          _ = _ := by rw [hc]; push_cast; ring
      rw [he,← Complex.ofReal_exp]
      have hw : weighted 1 0 t 0 u * Real.exp (-(s : ℝ)*delta*u^2) =
          weighted 1 0 (t-(s : ℝ)*delta) 0 u := by
        unfold weighted
        simp only [pow_zero,one_mul,zero_mul,add_zero]
        rw [show (t-(s : ℝ)*delta)*u^2 = t*u^2+(-(s : ℝ)*delta*u^2) by ring,
          Real.exp_add]
        ring
      unfold integrand
      have hcast := congrArg Complex.ofReal hw
      rw [Complex.ofReal_mul] at hcast
      linear_combination ((Complex.I*(u : ℂ))^j*
        Complex.exp (Complex.I*(u : ℂ)*z))*hcast

theorem shifted_flow_integrable (s : ℝ≥0) (t : ℝ) (z c : ℂ) :
    Integrable (fun y : ℝ => flow 1 t (z+c*(y : ℂ))) (law s) := by
  have h := ((shifted_jet_integrable s t 0 z c).add
    (shifted_jet_integrable s t 0 (-z) (-c))).div_const 2
  simp only [Pi.add_def] at h
  apply h.congr
  filter_upwards with y
  unfold flow
  congr 2
  congr 1
  ring

theorem shifted_flow_average (s : ℝ≥0) (t delta : ℝ) (z c : ℂ)
    (hc : c^2 = (delta : ℂ)) :
    (∫ y : ℝ, flow 1 t (z+c*(y : ℂ)) ∂law s) =
      flow 1 (t-(s : ℝ)*delta) z := by
  have hn : (-c)^2 = (delta : ℂ) := by simpa only [neg_sq] using hc
  have he (y : ℝ) : flow 1 t (z+c*(y : ℂ)) =
      (jet 1 0 t (z+c*(y : ℂ))+jet 1 0 t (-z+(-c)*(y : ℂ)))/2 := by
    unfold flow
    congr 2
    congr 1
    ring
  simp_rw [he]
  rw [integral_div,integral_add (shifted_jet_integrable s t 0 z c)
    (shifted_jet_integrable s t 0 (-z) (-c)),
    shifted_jet_average s t delta 0 z c hc,
    shifted_jet_average s t delta 0 (-z) (-c) hn]
  rfl

theorem imaginary_gaussian_average (s : ℝ≥0) (t : ℝ) (z : ℂ) :
    (∫ y : ℝ, flow 1 t (z+Complex.I*(y : ℂ)) ∂law s) =
      flow 1 (t+(s : ℝ)) z := by
  simpa only [Complex.ofReal_neg,Complex.ofReal_one,mul_neg_one,sub_neg_eq_add] using
    shifted_flow_average s t (-1) z Complex.I
      (by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using Complex.I_sq)

theorem real_gaussian_average (s : ℝ≥0) (t : ℝ) (z : ℂ) :
    (∫ y : ℝ, flow 1 t (z+(y : ℂ)) ∂law s) =
      flow 1 (t-(s : ℝ)) z := by
  simpa only [one_mul,mul_one] using
    shifted_flow_average s t 1 z 1 (by norm_num)

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticGaussian
