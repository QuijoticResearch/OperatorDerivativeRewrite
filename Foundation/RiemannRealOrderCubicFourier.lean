import Foundation.RiemannRealOrderCubicDensity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Genuine half-line Fourier integration by parts for the actual cubic
arithmetic density. All integrals and endpoint limits have explicit proofs. -/
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderCubicFourier
open RiemannRealOrderCubicDensity
open RiemannQuarticFlow (halfLine)

def fourierIntegral (n : ℕ) (t x : ℝ) : ℂ :=
  ∫ u : ℝ, iteratedDeriv n (density t) (u : ℂ)*
    Complex.exp (Complex.I*(x : ℂ)*(u : ℂ)) ∂halfLine

private theorem oscillator_norm (x u : ℝ) :
    ‖Complex.exp (Complex.I*(x : ℂ)*(u : ℂ))‖ = 1 := by
  simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]

theorem fourier_integrand_integrable (n : ℕ) (t x : ℝ) :
    Integrable (fun u : ℝ => iteratedDeriv n (density t) (u : ℂ)*
      Complex.exp (Complex.I*(x : ℂ)*(u : ℂ))) halfLine := by
  apply (density_iteratedDeriv_integrable n t).norm.mono'
    (((density_iteratedDeriv_continuous n t).mul (by fun_prop)).aestronglyMeasurable)
  filter_upwards [] with u
  exact (show ‖iteratedDeriv n (density t) (u : ℂ)*
    Complex.exp (Complex.I*(x : ℂ)*(u : ℂ))‖ ≤
      ‖iteratedDeriv n (density t) (u : ℂ)‖ from by
        rw [norm_mul,oscillator_norm,mul_one])

theorem fourier_boundary_zero (n : ℕ) (t x : ℝ) :
    Tendsto (fun u : ℝ => iteratedDeriv n (density t) (u : ℂ)*
      Complex.exp (Complex.I*(x : ℂ)*(u : ℂ))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_mul,oscillator_norm,mul_one] using
    tendsto_zero_iff_norm_tendsto_zero.mp (density_iteratedDeriv_tendsto_zero n t)

theorem fourier_recurrence (n : ℕ) (t x : ℝ) :
    (Complex.I*(x : ℂ))*fourierIntegral n t x =
      -iteratedDeriv n (density t) 0-fourierIntegral (n+1) t x := by
  let f : ℝ → ℂ := fun u => iteratedDeriv n (density t) (u : ℂ)
  let g : ℝ → ℂ := fun u => Complex.exp (Complex.I*(x : ℂ)*(u : ℂ))
  let fp : ℝ → ℂ := fun u => iteratedDeriv (n+1) (density t) (u : ℂ)
  let gp : ℝ → ℂ := fun u => (Complex.I*(x : ℂ))*g u
  have hf (u : ℝ) : HasDerivAt f (fp u) u := density_profile_hasDerivAt n t u
  have hg (u : ℝ) : HasDerivAt g (gp u) u := by
    have h := (((hasDerivAt_id u).ofReal_comp).const_mul (Complex.I*(x : ℂ))).cexp
    simpa only [g,gp,id_eq,Complex.ofReal_one,mul_one,mul_comm] using h
  have hfg : IntegrableOn (f*gp) (Ioi 0) := by
    have h := (fourier_integrand_integrable n t x).const_mul (Complex.I*(x : ℂ))
    have he : (f*gp) = fun u : ℝ => (Complex.I*(x : ℂ))*
        (iteratedDeriv n (density t) (u : ℂ)*g u) := by
      funext u
      dsimp [f,gp]
      ring
    rw [he]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mp h
  have hpf : IntegrableOn (fp*g) (Ioi 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mp (fourier_integrand_integrable (n+1) t x)
  have hzero : Tendsto (f*g) (𝓝[>] (0 : ℝ)) (𝓝 (iteratedDeriv n (density t) 0)) := by
    have hc : Continuous (f*g) := (density_iteratedDeriv_continuous n t).mul (by fun_prop)
    have hh : Tendsto (f*g) (𝓝[>] (0 : ℝ)) (𝓝 ((f*g) 0)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [Pi.mul_apply,f,g,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]
      using hh
  have htop : Tendsto (f*g) atTop (𝓝 0) := fourier_boundary_zero n t x
  have h := integral_Ioi_mul_deriv_eq_deriv_mul (fun u _ => hf u) (fun u _ => hg u)
    hfg hpf hzero htop
  have he : (∫ u : ℝ in Ioi 0, f u*gp u) =
      (Complex.I*(x : ℂ))*fourierIntegral n t x := by
    rw [← integral_Ici_eq_integral_Ioi]
    unfold fourierIntegral
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp [f,gp,g]
    ring
  have hep : (∫ u : ℝ in Ioi 0, fp u*g u) = fourierIntegral (n+1) t x := by
    rw [← integral_Ici_eq_integral_Ioi]
    rfl
  rw [he,hep,zero_sub] at h
  exact h

theorem fourier_second_recurrence (n : ℕ) (t x : ℝ) :
    (x : ℂ)^2*fourierIntegral n t x =
      (Complex.I*(x : ℂ))*iteratedDeriv n (density t) 0-
        iteratedDeriv (n+1) (density t) 0-fourierIntegral (n+2) t x := by
  have h0 := fourier_recurrence n t x
  have h1 := fourier_recurrence (n+1) t x
  have he : (Complex.I*(x : ℂ))^2*fourierIntegral n t x =
      -(Complex.I*(x : ℂ))*iteratedDeriv n (density t) 0+
        iteratedDeriv (n+1) (density t) 0+fourierIntegral (n+2) t x := by
    simp only [Nat.add_assoc] at h1
    linear_combination (Complex.I*(x : ℂ))*h0-h1
  have hi : (Complex.I*(x : ℂ))^2 = -(x : ℂ)^2 := by
    rw [mul_pow,Complex.I_sq]
    ring
  rw [hi] at he
  linear_combination -he

def cosineIntegral (n : ℕ) (t x : ℝ) : ℂ :=
  (fourierIntegral n t x+fourierIntegral n t (-x))/2

theorem cosine_integral_genuine (n : ℕ) (t x : ℝ) :
    Integrable (fun u : ℝ => iteratedDeriv n (density t) (u : ℂ)*
      Complex.cos ((u : ℂ)*(x : ℂ))) halfLine ∧
    cosineIntegral n t x = ∫ u : ℝ, iteratedDeriv n (density t) (u : ℂ)*
      Complex.cos ((u : ℂ)*(x : ℂ)) ∂halfLine := by
  have he (u : ℝ) : (iteratedDeriv n (density t) (u : ℂ)*
      Complex.exp (Complex.I*(x : ℂ)*(u : ℂ))+
      iteratedDeriv n (density t) (u : ℂ)*
      Complex.exp (Complex.I*((-x : ℝ) : ℂ)*(u : ℂ)))/2 =
      iteratedDeriv n (density t) (u : ℂ)*Complex.cos ((u : ℂ)*(x : ℂ)) := by
    have hp : Complex.I*(x : ℂ)*(u : ℂ) = ((u : ℂ)*(x : ℂ))*Complex.I := by ring
    have hn : Complex.I*((-x : ℝ) : ℂ)*(u : ℂ) = -((u : ℂ)*(x : ℂ))*Complex.I := by
      push_cast
      ring
    rw [hp,hn]
    simp only [Complex.cos]
    ring
  have hi := ((fourier_integrand_integrable n t x).add
    (fourier_integrand_integrable n t (-x))).div_const 2
  refine ⟨hi.congr (Eventually.of_forall he),?_⟩
  unfold cosineIntegral fourierIntegral
  rw [← integral_add (fourier_integrand_integrable n t x)
    (fourier_integrand_integrable n t (-x)),← integral_div]
  exact integral_congr_ae (Eventually.of_forall he)

theorem cosine_zero_eq_actual_flow (t x : ℝ) :
    cosineIntegral 0 t x = RiemannRealOrderFlow.flow (3/2) t (x : ℂ) := by
  calc
    _ = ∫ u : ℝ, density t (u : ℂ)*Complex.cos ((u : ℂ)*(x : ℂ)) ∂halfLine := by
      simpa only [iteratedDeriv_zero] using (cosine_integral_genuine 0 t x).2
    _ = _ := (actual_flow_density_integral t (x : ℂ)).2.symm

theorem cosine_second_recurrence (n : ℕ) (t x : ℝ) :
    (x : ℂ)^2*cosineIntegral n t x =
      -iteratedDeriv (n+1) (density t) 0-cosineIntegral (n+2) t x := by
  have hp := fourier_second_recurrence n t x
  have hn := fourier_second_recurrence n t (-x)
  simp only [Complex.ofReal_neg] at hn
  unfold cosineIntegral
  linear_combination (1/2 : ℂ)*hp+(1/2 : ℂ)*hn

theorem cosine_fourth_identity (n : ℕ) (t x : ℝ) :
    (x : ℂ)^4*cosineIntegral n t x =
      -(x : ℂ)^2*iteratedDeriv (n+1) (density t) 0+
        iteratedDeriv (n+3) (density t) 0+cosineIntegral (n+4) t x := by
  have h0 := cosine_second_recurrence n t x
  have h2 := cosine_second_recurrence (n+2) t x
  simp only [Nat.add_assoc] at h2
  linear_combination (x : ℂ)^2*h0-h2

theorem actual_flow_fourth_identity (t x : ℝ) :
    (x : ℂ)^4*RiemannRealOrderFlow.flow (3/2) t (x : ℂ) =
      -(x : ℂ)^2*iteratedDeriv 1 (density t) 0+
        iteratedDeriv 3 (density t) 0+cosineIntegral 4 t x := by
  simpa only [Nat.zero_add,cosine_zero_eq_actual_flow] using cosine_fourth_identity 0 t x

theorem fourierIntegral_tendsto_zero (n : ℕ) (t : ℝ) :
    Tendsto (fourierIntegral n t) (cocompact ℝ) (𝓝 0) := by
  have h := (RiemannRealOrderFourierDecay.half_line_genuine_and_decay
    (fun u : ℝ => iteratedDeriv n (density t) (u : ℂ))
    (density_iteratedDeriv_integrable n t)).2
  have he (x : ℝ) : fourierIntegral n t x =
      ∫ u : ℝ, Complex.exp (Complex.I*(u : ℂ)*(x : ℂ))*
        iteratedDeriv n (density t) (u : ℂ) ∂halfLine := by
    apply integral_congr_ae
    filter_upwards [] with u
    rw [show Complex.I*(x : ℂ)*(u : ℂ) = Complex.I*(u : ℂ)*(x : ℂ) by ring]
    ring
  simpa only [← he] using h

theorem cosineIntegral_tendsto_zero (n : ℕ) (t : ℝ) :
    Tendsto (cosineIntegral n t) (cocompact ℝ) (𝓝 0) := by
  have h := fourierIntegral_tendsto_zero n t
  have hn : Tendsto (fun x : ℝ => -x) (cocompact ℝ) (cocompact ℝ) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℝ)
    simpa [Real.dist_eq] using tendsto_dist_right_cocompact_atTop (0 : ℝ)
  change Tendsto (fun x : ℝ => (fourierIntegral n t x+fourierIntegral n t (-x))/2)
    (cocompact ℝ) (𝓝 0)
  simpa only [Function.comp_apply,zero_add,zero_div] using
    (h.add (h.comp hn)).div_const (2 : ℂ)

theorem actual_flow_fourth_remainder_decay (t : ℝ) :
    Tendsto (fun x : ℝ => (x : ℂ)^4*RiemannRealOrderFlow.flow (3/2) t (x : ℂ)+
      (x : ℂ)^2*iteratedDeriv 1 (density t) 0-iteratedDeriv 3 (density t) 0)
      (cocompact ℝ) (𝓝 0) := by
  have he (x : ℝ) : (x : ℂ)^4*RiemannRealOrderFlow.flow (3/2) t (x : ℂ)+
      (x : ℂ)^2*iteratedDeriv 1 (density t) 0-iteratedDeriv 3 (density t) 0 =
      cosineIntegral 4 t x := by
    rw [actual_flow_fourth_identity]
    ring
  simpa only [he] using cosineIntegral_tendsto_zero 4 t

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderCubicFourier
