import Foundation.RiemannRealOrderFourthReconstruction

/-! Actual fractional asymptotics in the range 3/2<a<2. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFourthAsymptotic
open RiemannThetaComplexKernel RiemannRealOrderFractionalJets
open RiemannRealOrderFractionalRemainder RiemannRealOrderFractionalCoefficient
open RiemannRealOrderFifthDerivative RiemannRealOrderFourthRemainder
open RiemannRealOrderFourthFourier RiemannRealOrderFourthReconstruction

def fourthCoefficient (a t : ℝ) : ℂ :=
  ((t*falling (2*a) 4 : ℝ) : ℂ)*kernelComplex 0

theorem scaled_cosine_gamma_limit (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x^b*(∫ u : ℝ in Ioi 0,
      u^(b-1)*Real.exp (-u)*Real.cos (x*u))) atTop
        (𝓝 (Real.Gamma b*Real.cos (Real.pi*b/2))) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (FractionalEndpointLaplace.scaled_transform_limit b hb)
  have hi (x : ℝ) : (FractionalEndpointLaplace.transform b (1-Complex.I*(x : ℂ))).re=
      ∫ u : ℝ in Ioi 0, u^(b-1)*Real.exp (-u)*Real.cos (x*u) := by
    calc
      _ = ∫ u : ℝ in Ioi 0, (FractionalEndpointLaplace.profile b (1-Complex.I*(x : ℂ)) u).re :=
        (integral_re (𝕜 := ℂ) (FractionalEndpointLaplace.profile_integrable b hb _ (by simp))).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _
        simp [FractionalEndpointLaplace.profile,Complex.mul_re,Complex.mul_im,Complex.exp_re]
        ring
  have hv : (Complex.I^(b : ℂ)*Complex.Gamma (b : ℂ)).re=
      Real.Gamma b*Real.cos (Real.pi*b/2) := by
    rw [Complex.Gamma_ofReal,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,
      sub_zero,Complex.cpow_ofReal_re]
    simp [Complex.arg_I,mul_comm,mul_div_assoc]
  simpa only [Function.comp_def,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,hi,hv] using h

theorem fourthCutoff_cosine_integrable (a t x : ℝ) (ha : 3/2 < a) :
    IntegrableOn (fun u : ℝ => fourthCutoff a t u*(Real.cos (x*u) : ℂ)) (Ioi 0) := by
  apply (fourthCutoff_integrable a t ha).mul_bdd (c := 1) (by fun_prop)
  filter_upwards with u
  simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one (x*u)

theorem fourthCutoff_cosine_eq (a t x : ℝ) :
    (∫ u : ℝ in Ioi 0, fourthCutoff a t u*(Real.cos (x*u) : ℂ))=
      fourthCoefficient a t*((∫ u : ℝ in Ioi 0,
        u^((2*a-3)-1)*Real.exp (-u)*Real.cos (x*u) : ℝ) : ℂ) := by
  calc
    _ = ∫ u : ℝ in Ioi 0, fourthCoefficient a t*
        ((u^((2*a-3)-1)*Real.exp (-u)*Real.cos (x*u) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      change phaseJet a t 4 (u : ℂ)*kernelComplex 0*(Real.exp (-u) : ℂ)*
        (Real.cos (x*u) : ℂ)=_
      rw [phaseJet_real a t u 4 hu.le]
      norm_num only [Nat.cast_ofNat]
      rw [show 2*a-3-1=2*a-4 by ring]
      unfold fourthCoefficient
      push_cast
      ring
    _ = _ := by rw [integral_const_mul]; congr 1; exact integral_complex_ofReal

theorem fourthCosine_decomposition (a t x : ℝ) (ha : 3/2 < a) (ha2 : a ≤ 2) :
    fourthCosine a t x=cosineRemainder a t x+fourthCoefficient a t*
      ((∫ u : ℝ in Ioi 0, u^((2*a-3)-1)*Real.exp (-u)*Real.cos (x*u) : ℝ) : ℂ) := by
  rw [← fourthCutoff_cosine_eq,cosineRemainder,← integral_add
    (cosineRemainder_integrable a t x ha ha2) (fourthCutoff_cosine_integrable a t x ha)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  dsimp only [Pi.add_apply]
  unfold fourthRemainder
  ring

theorem fourthCosine_scaled_limit (a t : ℝ) (ha : 3/2 < a) (ha2 : a < 2) :
    Tendsto (fun x : ℝ => ((x^(2*a-3) : ℝ) : ℂ)*fourthCosine a t x) atTop
      (𝓝 (fourthCoefficient a t*
        ((Real.Gamma (2*a-3)*Real.cos (Real.pi*(2*a-3)/2) : ℝ) : ℂ))) := by
  have hg : Tendsto (fun x : ℝ =>
      ((x^(2*a-3)*(∫ u : ℝ in Ioi 0,
        u^((2*a-3)-1)*Real.exp (-u)*Real.cos (x*u)) : ℝ) : ℂ)) atTop
        (𝓝 ((Real.Gamma (2*a-3)*Real.cos (Real.pi*(2*a-3)/2) : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (scaled_cosine_gamma_limit (2*a-3) (by linarith))
  have h := (scaled_cosineRemainder_limit a t (2*a-3) ha ha2.le (by linarith)).add
    (hg.const_mul (fourthCoefficient a t))
  apply (show Tendsto (fun x : ℝ => ((x^(2*a-3) : ℝ) : ℂ)*cosineRemainder a t x+
      fourthCoefficient a t*((x^(2*a-3)*(∫ u : ℝ in Ioi 0,
        u^((2*a-3)-1)*Real.exp (-u)*Real.cos (x*u)) : ℝ) : ℂ)) atTop
        (𝓝 (fourthCoefficient a t*
          ((Real.Gamma (2*a-3)*Real.cos (Real.pi*(2*a-3)/2) : ℝ) : ℂ))) by
      simpa only [zero_add] using h).congr'
  filter_upwards with x
  rw [fourthCosine_decomposition a t x ha ha2.le]
  push_cast
  ring

theorem falling_four_gamma (a : ℝ) (ha : 3/2 < a) :
    falling (2*a) 4*Real.Gamma (2*a-3)=Real.Gamma (2*a+1) := by
  have hg : Real.Gamma (2*a-2)=(2*a-3)*Real.Gamma (2*a-3) := by
    convert Real.Gamma_add_one (s := 2*a-3) (by linarith) using 1 <;> congr 1 <;> ring
  rw [falling_succ (2*a) 3,mul_assoc]
  norm_num only [Nat.cast_ofNat]
  rw [← hg,falling_gamma a (by linarith)]

theorem fourth_asymptotic_coefficient (a t : ℝ) (ha : 3/2 < a) :
    fourthCoefficient a t*
      ((Real.Gamma (2*a-3)*Real.cos (Real.pi*(2*a-3)/2) : ℝ) : ℂ)=(leading a t : ℂ) := by
  have hk := kernelComplex_real 0
  simp only [Complex.ofReal_zero] at hk
  rw [fourthCoefficient,hk,← Complex.ofReal_mul,← Complex.ofReal_mul]
  congr 1
  rw [show Real.pi*(2*a-3)/2=Real.pi*(a-1)-Real.pi/2 by ring,Real.cos_sub_pi_div_two]
  unfold RiemannRealOrderFractionalCoefficient.leading
  calc
    _ = t*RiemannQuarticKernel.kernel 0*(falling (2*a) 4*Real.Gamma (2*a-3))*
        Real.sin (Real.pi*(a-1)) := by ring
    _ = _ := by rw [falling_four_gamma a ha]

theorem actual_flow_scaled_limit (a t : ℝ) (ha : 3/2 < a) (ha2 : a < 2) :
    Tendsto (fun x : ℝ => ((x^(2*a+1) : ℝ) : ℂ)*RiemannRealOrderFlow.flow a t (x : ℂ))
      atTop (𝓝 (leading a t : ℂ)) := by
  rw [← fourth_asymptotic_coefficient a t ha]
  apply (fourthCosine_scaled_limit a t ha ha2).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← actual_fourth_identity a t x ha ha2.le,
    show 2*a+1=(2*a-3)+4 by ring,Real.rpow_add hx]
  have hp : x^(4 : ℝ)=x^(4 : ℕ) := Real.rpow_natCast x 4
  rw [hp]
  push_cast
  ring

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFourthAsymptotic
