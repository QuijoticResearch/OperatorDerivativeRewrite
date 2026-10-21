import Foundation.RiemannRealOrderCutoffConcentration
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Regularization of the actual cutoff transform before a uniform order limit.
The closed extension at order one is not the actual complex transform there. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderUniformCutoff
open RiemannRealOrderFractionalJets RiemannRealOrderFractionalRemainder
open RiemannRealOrderCutoffBoundary RiemannRealOrderFractionalCoefficient

def scaledBase (x : ℝ) : ℂ := (((x⁻¹ : ℝ) : ℂ)-Complex.I)⁻¹

def regularized (t : ℝ) (z : ℂ) (a : ℝ) : ℂ :=
  (mass a t : ℂ)*z^((2*a-2 : ℝ) : ℂ)

def cutoffFourier (a t x : ℝ) : ℂ := ∫ u : ℝ in Ioi 0,
  cutoff a t u*Complex.exp (Complex.I*(x : ℂ)*(u : ℂ))

theorem scaledBase_tendsto : Tendsto scaledBase atTop (𝓝 Complex.I) := by
  have h : Tendsto (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)-Complex.I) atTop (𝓝 (-Complex.I)) := by
    simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_inv_atTop_zero).sub_const Complex.I
  change Tendsto (fun x : ℝ => (((x⁻¹ : ℝ) : ℂ)-Complex.I)⁻¹) atTop (𝓝 Complex.I)
  simpa using h.inv₀ (by simp)

theorem mass_continuousAt (a t : ℝ) (ha : 0 ≤ a) :
    ContinuousAt (fun b : ℝ => mass b t) a := by
  have hg := (Real.differentiableAt_Gamma (s := 2*a+1)
    (fun m => by have hm := Nat.cast_nonneg (α := ℝ) m; linarith)).continuousAt
  have hc := hg.comp (f := fun b : ℝ => 2*b+1) (by fun_prop)
  exact continuousAt_const.mul hc

theorem regularized_continuousAt (t : ℝ) (p : ℂ × ℝ) (ha : 0 ≤ p.2)
    (hz : p.1 ∈ Complex.slitPlane) :
    ContinuousAt (fun q : ℂ × ℝ => regularized t q.1 q.2) p := by
  have hm := Complex.continuous_ofReal.continuousAt.comp
    ((mass_continuousAt p.2 t ha).comp continuousAt_snd)
  have hp := continuousAt_fst.cpow
    (show ContinuousAt (fun q : ℂ × ℝ => ((2*q.2-2 : ℝ) : ℂ)) p by fun_prop) hz
  exact hm.mul hp

theorem regularized_uniform_limit (t : ℝ) :
    TendstoUniformlyOn (fun x a : ℝ => regularized t (scaledBase x) a)
      (fun a : ℝ => regularized t Complex.I a) atTop (Icc 1 (5/4)) := by
  let A : Set ℝ := Icc 1 (5/4)
  letI : CompactSpace A := isCompact_iff_compactSpace.mp isCompact_Icc
  let U : Set ℂ := {z | 0 < z.im}
  let f : ℂ → A → ℂ := fun z a => regularized t z a
  have hU : U ∈ 𝓝 Complex.I :=
    Complex.continuous_im.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by simp))
  have hc : ContinuousOn (Function.uncurry f) (U ×ˢ univ) := by
    intro p hp
    have hz : p.1 ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr
      (Or.inr (ne_of_gt hp.1))
    have ha : 0 ≤ (p.2 : ℝ) := le_trans (by norm_num) p.2.property.1
    have h := (regularized_continuousAt t (p.1,(p.2 : ℝ)) ha hz).comp
      (f := fun q : ℂ × A => (q.1,(q.2 : ℝ)))
      (show ContinuousAt (fun q : ℂ × A => (q.1,(q.2 : ℝ))) p by fun_prop)
    exact h.continuousWithinAt
  have hlocal : TendstoUniformly f (f Complex.I) (𝓝 Complex.I) :=
    ContinuousOn.tendstoUniformly hU hc
  have hscaled : TendstoUniformly (fun x : ℝ => f (scaledBase x)) (f Complex.I) atTop :=
    fun V hV => scaledBase_tendsto.eventually (hlocal V hV)
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  simpa only [f,Function.comp_def] using hscaled

theorem cutoff_fourier_integrable (a t x : ℝ) (ha : 1 < a) :
    IntegrableOn (fun u : ℝ => cutoff a t u*Complex.exp (Complex.I*(x : ℂ)*(u : ℂ))) (Ioi 0) := by
  apply (cutoff_integrable a t ha).mul_bdd (c := 1) (by fun_prop)
  filter_upwards with u
  simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]

private theorem coefficient_gamma_mass (a t : ℝ) (ha : 1 < a) :
    RiemannRealOrderFractionalFourier.endpointCoefficient a t*(Real.Gamma (2*a-2) : ℂ)=
      (mass a t : ℂ) := by
  rw [RiemannRealOrderFractionalFourier.endpointCoefficient_real,← Complex.ofReal_mul]
  congr 1
  unfold mass
  calc
    _ = t*RiemannQuarticKernel.kernel 0*(falling (2*a) 3*Real.Gamma (2*a-2)) := by ring
    _ = _ := by rw [falling_gamma a ha]

theorem cutoffFourier_eq (a t x : ℝ) (ha : 1 < a) :
    cutoffFourier a t x=(mass a t : ℂ)*
      ((1-Complex.I*(x : ℂ))⁻¹)^((2*a-2 : ℝ) : ℂ) := by
  have he : cutoffFourier a t x=RiemannRealOrderFractionalFourier.endpointCoefficient a t*
      (∫ u : ℝ in Ioi 0, (u^((2*a-2)-1)*Real.exp (-u) : ℝ)*
        Complex.exp (Complex.I*(x : ℂ)*(u : ℂ))) := by
    rw [cutoffFourier,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [cutoff_real a t u hu.le,RiemannRealOrderFractionalFourier.endpointCoefficient_real,
      show 2*a-2-1=2*a-3 by ring]
    push_cast
    ring
  rw [he,FractionalEndpointLaplace.cutoff_fourier_eq (2*a-2) (by linarith),Complex.Gamma_ofReal]
  calc
    _ = (RiemannRealOrderFractionalFourier.endpointCoefficient a t*(Real.Gamma (2*a-2) : ℂ))*
        ((1-Complex.I*(x : ℂ))⁻¹)^((2*a-2 : ℝ) : ℂ) := by ring
    _ = _ := by rw [coefficient_gamma_mass a t ha]

theorem scaled_cutoffFourier_eq (a t x : ℝ) (ha : 1 < a) (hx : 0 < x) :
    ((x^(2*a-2) : ℝ) : ℂ)*cutoffFourier a t x=regularized t (scaledBase x) a := by
  have hn : (1-Complex.I*(x : ℂ)) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp [Complex.mul_re,Complex.mul_im] at hh
  have he : (x : ℂ)*(1-Complex.I*(x : ℂ))⁻¹=scaledBase x := by
    unfold scaledBase
    rw [Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr hx.ne'] <;> ring
  rw [cutoffFourier_eq a t x ha]
  calc
    _ = (mass a t : ℂ)*(((x^(2*a-2) : ℝ) : ℂ)*
        ((1-Complex.I*(x : ℂ))⁻¹)^((2*a-2 : ℝ) : ℂ)) := by ring
    _ = (mass a t : ℂ)*((x : ℂ)*(1-Complex.I*(x : ℂ))⁻¹)^((2*a-2 : ℝ) : ℂ) := by
      rw [FractionalEndpointLaplace.positive_scale_cpow x hx _ (inv_ne_zero hn)]
    _ = _ := by rw [he]; rfl

theorem cutoffFourier_uniform_scaled_limit (t : ℝ) :
    TendstoUniformlyOn (fun x a : ℝ => ((x^(2*a-2) : ℝ) : ℂ)*cutoffFourier a t x)
      (fun a : ℝ => regularized t Complex.I a) atTop (Ioc 1 (5/4)) := by
  apply ((regularized_uniform_limit t).mono Ioc_subset_Icc_self).congr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  intro a ha
  exact (scaled_cutoffFourier_eq a t x ha.1 hx).symm

theorem regularized_I_im (t a : ℝ) : (regularized t Complex.I a).im=leading a t := by
  rw [regularized,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
    Complex.cpow_ofReal_im]
  simp only [Complex.norm_I,Real.one_rpow,Complex.arg_I,one_mul]
  rw [show Real.pi/2*(2*a-2)=Real.pi*(a-1) by ring]
  rfl

theorem cutoff_sine_integrable (a t x : ℝ) (ha : 1 < a) :
    IntegrableOn (fun u : ℝ => cutoff a t u*(Real.sin (x*u) : ℂ)) (Ioi 0) := by
  apply (cutoff_integrable a t ha).mul_bdd (c := 1) (by fun_prop)
  filter_upwards with u
  simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one (x*u)

theorem cutoff_sine_eq_im (a t x : ℝ) (ha : 1 < a) :
    (∫ u : ℝ in Ioi 0, cutoff a t u*(Real.sin (x*u) : ℂ))=
      ((cutoffFourier a t x).im : ℂ) := by
  have hi : (cutoffFourier a t x).im = ∫ u : ℝ in Ioi 0,
      (cutoff a t u*Complex.exp (Complex.I*(x : ℂ)*(u : ℂ))).im :=
    (integral_im (𝕜 := ℂ) (cutoff_fourier_integrable a t x ha)).symm
  rw [hi,← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [cutoff_real a t u hu.le]
  have ho : (Complex.exp (Complex.I*(x : ℂ)*(u : ℂ))).im=Real.sin (x*u) := by
    simp [Complex.exp_im,Complex.mul_re,Complex.mul_im]
  rw [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,ho,
    Complex.ofReal_mul]
  push_cast
  rfl

theorem scaled_cutoff_sine_eq (a t x : ℝ) (ha : 1 < a) (hx : 0 < x) :
    ((x^(2*a-2) : ℝ) : ℂ)*(∫ u : ℝ in Ioi 0,
      cutoff a t u*(Real.sin (x*u) : ℂ))=
        ((regularized t (scaledBase x) a).im : ℂ) := by
  rw [cutoff_sine_eq_im a t x ha]
  have h := congrArg Complex.im (scaled_cutoffFourier_eq a t x ha hx)
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
    Complex.ofReal_mul] using congrArg Complex.ofReal h

/-- Uniform absolute error for the genuine cutoff sine integral. No division by the
vanishing leading coefficient, and no uniform actual-flow remainder claim. -/
theorem cutoff_sine_uniform_scaled_limit (t : ℝ) :
    TendstoUniformlyOn (fun x a : ℝ => ((x^(2*a-2) : ℝ) : ℂ)*
      (∫ u : ℝ in Ioi 0, cutoff a t u*(Real.sin (x*u) : ℂ)))
      (fun a : ℝ => (leading a t : ℂ)) atTop (Ioc 1 (5/4)) := by
  have h := Complex.ofRealCLM.uniformContinuous.comp_tendstoUniformlyOn
    (Complex.uniformContinuous_im.comp_tendstoUniformlyOn
      ((regularized_uniform_limit t).mono Ioc_subset_Icc_self))
  have hh : TendstoUniformlyOn
      (fun x a : ℝ => ((regularized t (scaledBase x) a).im : ℂ))
      (fun a : ℝ => (leading a t : ℂ)) atTop (Ioc 1 (5/4)) := by
    simpa only [Function.comp_def,regularized_I_im,Complex.ofRealCLM_apply] using h
  apply hh.congr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  intro a ha
  exact (scaled_cutoff_sine_eq a t x ha.1 hx).symm

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderUniformCutoff
