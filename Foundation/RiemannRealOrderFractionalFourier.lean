import Foundation.RiemannRealOrderFractionalRemainder

/-! Genuine sine-transform integration by parts for the actual canceled
fractional density remainder. No endpoint analyticity is assumed. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalFourier
open RiemannRealOrderFractionalJets RiemannRealOrderFractionalRemainder

private theorem sine_norm_le (x u : ℝ) : ‖(Real.sin (x*u) : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one (x*u)

private theorem cosine_norm_le (x u : ℝ) : ‖(Real.cos (x*u) : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one (x*u)

private theorem sine_integrable (f : ℝ → ℂ) (hf : IntegrableOn f (Ioi 0)) (x : ℝ) :
    IntegrableOn (fun u : ℝ => f u*(Real.sin (x*u) : ℂ)) (Ioi 0) := by
  apply hf.norm.mono' (hf.aestronglyMeasurable.mul (by fun_prop))
  filter_upwards with u
  change ‖f u*_‖ ≤ ‖f u‖
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (sine_norm_le x u)

private theorem cosine_integrable (f : ℝ → ℂ) (hf : IntegrableOn f (Ioi 0)) (x : ℝ) :
    IntegrableOn (fun u : ℝ => f u*(Real.cos (x*u) : ℂ)) (Ioi 0) := by
  apply hf.norm.mono' (hf.aestronglyMeasurable.mul (by fun_prop))
  filter_upwards with u
  change ‖f u*_‖ ≤ ‖f u‖
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (cosine_norm_le x u)

def sineRemainder (a t x : ℝ) : ℂ :=
  ∫ u : ℝ in Ioi 0, remainder a t u*(Real.sin (x*u) : ℂ)

theorem sineRemainder_integrable (a t x : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    IntegrableOn (fun u : ℝ => remainder a t u*(Real.sin (x*u) : ℂ)) (Ioi 0) :=
  sine_integrable _ (remainder_integrable a t ha ha2) x

theorem derivative_cosine_integrable (a t x : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    IntegrableOn (fun u : ℝ => deriv (remainder a t) u*(Real.cos (x*u) : ℂ)) (Ioi 0) :=
  cosine_integrable _ (remainder_derivative_integrable a t ha ha2) x

theorem sineRemainder_ibp (a t x : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    (x : ℂ)*sineRemainder a t x =
      ∫ u : ℝ in Ioi 0, deriv (remainder a t) u*(Real.cos (x*u) : ℂ) := by
  let g : ℝ → ℂ := fun u => (Real.cos (x*u) : ℂ)
  let gp : ℝ → ℂ := fun u => -(x : ℂ)*(Real.sin (x*u) : ℂ)
  have hg (u : ℝ) : HasDerivAt g (gp u) u := by
    convert (((hasDerivAt_id u).const_mul x).cos).ofReal_comp using 1
    · rfl
    · simp [g,gp,Complex.ofReal_mul,mul_comm]
  have hf (u : ℝ) (hu : u ∈ Ioi 0) :
      HasDerivAt (remainder a t) (deriv (remainder a t) u) u :=
    (remainder_hasDerivAt a t u hu).differentiableAt.hasDerivAt
  have hfg : IntegrableOn ((remainder a t)*gp) (Ioi 0) := by
    apply ((sineRemainder_integrable a t x ha ha2).const_mul (-(x : ℂ))).congr
    filter_upwards with u
    simp only [Pi.mul_apply,gp]
    ring
  have hzero : Tendsto ((remainder a t)*g) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous g := by dsimp [g]; fun_prop
    simpa only [mul_zero,zero_mul,Pi.mul_def] using
      (remainder_tendsto_zero a t ha).mul
        (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have htop : Tendsto ((remainder a t)*g) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun u => ?_)
      (tendsto_zero_iff_norm_tendsto_zero.mp (remainder_tendsto_zero_atTop a t ha ha2))
    simp only [Pi.mul_apply,norm_mul,g]
    exact mul_le_of_le_one_right (norm_nonneg _) (cosine_norm_le x u)
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hf (fun u _ => hg u) hfg
    (derivative_cosine_integrable a t x ha ha2) hzero htop
  have he : (∫ u : ℝ in Ioi 0, remainder a t u*gp u) =
      -(x : ℂ)*sineRemainder a t x := by
    rw [sineRemainder,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    dsimp [gp]
    ring
  rw [he] at h
  simp only [sub_zero,zero_sub,neg_zero] at h
  apply neg_injective
  simpa only [neg_mul,g] using h

theorem sineRemainder_norm_bound (a t x : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    |x| * ‖sineRemainder a t x‖ ≤ ∫ u : ℝ in Ioi 0, ‖deriv (remainder a t) u‖ := by
  have h := norm_integral_le_of_norm_le (remainder_derivative_integrable a t ha ha2).norm
    (Eventually.of_forall fun u =>
      show ‖deriv (remainder a t) u*(Real.cos (x*u) : ℂ)‖ ≤ ‖deriv (remainder a t) u‖ from by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (cosine_norm_le x u))
  rw [← sineRemainder_ibp a t x ha ha2,norm_mul,Complex.norm_real,Real.norm_eq_abs] at h
  exact h

theorem scaled_sineRemainder_tendsto_zero (a t b : ℝ) (ha : 1 < a) (ha2 : a ≤ 2)
    (hb : b < 1) :
    Tendsto (fun x : ℝ => ((x^b : ℝ) : ℂ)*sineRemainder a t x) atTop (𝓝 0) := by
  let C := ∫ u : ℝ in Ioi 0, ‖deriv (remainder a t) u‖
  have ht : Tendsto (fun x : ℝ => x^(b-1)*C) atTop (𝓝 0) := by
    simpa only [neg_sub,sub_zero,zero_mul] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hb)).mul_const C
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.eventually_atTop.2 ⟨1,fun x hx => ?_⟩) ht
  have hx0 : 0 < x := by linarith
  have hbound := sineRemainder_norm_bound a t x ha ha2
  rw [abs_of_pos hx0] at hbound
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  calc
    x^b*‖sineRemainder a t x‖ = x^(b-1)*(x*‖sineRemainder a t x‖) := by
      rw [Real.rpow_sub_one hx0.ne' b]
      field_simp
    _ ≤ x^(b-1)*C := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hx0.le _)

def endpointCoefficient (a t : ℝ) : ℂ :=
  ((t*falling (2*a) 3 : ℝ) : ℂ)*RiemannThetaComplexKernel.kernelComplex 0

def thirdSine (a t x : ℝ) : ℂ := ∫ u : ℝ in Ioi 0,
  iteratedDeriv 3 (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)*
    (Real.sin (x*u) : ℂ)

theorem third_derivative_integrable (a t : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    IntegrableOn (fun u : ℝ =>
      iteratedDeriv 3 (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)) (Ioi 0) := by
  apply ((remainder_integrable a t ha ha2).add (cutoff_integrable a t ha)).congr
  filter_upwards with u
  simp only [Pi.add_apply,RiemannRealOrderFractionalJets.remainder,sub_add_cancel]

theorem thirdSine_integrable (a t x : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    IntegrableOn (fun u : ℝ =>
      iteratedDeriv 3 (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)*
        (Real.sin (x*u) : ℂ)) (Ioi 0) :=
  sine_integrable _ (third_derivative_integrable a t ha ha2) x

theorem cutoff_sine_eq (a t x : ℝ) :
    (∫ u : ℝ in Ioi 0, cutoff a t u*(Real.sin (x*u) : ℂ)) =
      endpointCoefficient a t*
        ((∫ u : ℝ in Ioi 0, u^((2*a-2)-1)*Real.exp (-u)*Real.sin (x*u) : ℝ) : ℂ) := by
  calc
    _ = ∫ u : ℝ in Ioi 0, endpointCoefficient a t*
        ((u^((2*a-2)-1)*Real.exp (-u)*Real.sin (x*u) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      change phaseJet a t 3 (u : ℂ)*RiemannThetaComplexKernel.kernelComplex 0*
        (Real.exp (-u) : ℂ)*(Real.sin (x*u) : ℂ) = _
      rw [phaseJet_real a t u 3 hu.le]
      norm_num only [Nat.cast_ofNat]
      rw [show 2*a-2-1=2*a-3 by ring]
      unfold endpointCoefficient
      push_cast
      ring
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact integral_complex_ofReal

theorem thirdSine_decomposition (a t x : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    thirdSine a t x = sineRemainder a t x+endpointCoefficient a t*
      ((∫ u : ℝ in Ioi 0, u^((2*a-2)-1)*Real.exp (-u)*Real.sin (x*u) : ℝ) : ℂ) := by
  rw [← cutoff_sine_eq,sineRemainder,← integral_add
    (sineRemainder_integrable a t x ha ha2) (sine_integrable _ (cutoff_integrable a t ha) x)]
  apply integral_congr_ae
  filter_upwards with u
  simp only [thirdSine,RiemannRealOrderFractionalJets.remainder]
  ring

theorem thirdSine_scaled_limit (a t : ℝ) (ha : 1 < a) (ha3 : a < 3/2) :
    Tendsto (fun x : ℝ => ((x^(2*a-2) : ℝ) : ℂ)*thirdSine a t x) atTop
      (𝓝 (endpointCoefficient a t*
        ((Real.Gamma (2*a-2)*Real.sin (Real.pi*(2*a-2)/2) : ℝ) : ℂ))) := by
  have hR := scaled_sineRemainder_tendsto_zero a t (2*a-2) ha (by linarith) (by linarith)
  have hG := FractionalEndpointLaplace.scaled_sine_limit (2*a-2) (by linarith)
  have hGC := Complex.continuous_ofReal.continuousAt.tendsto.comp hG
  have h := hR.add ((tendsto_const_nhds (x := endpointCoefficient a t)).mul hGC)
  apply (show Tendsto (fun x : ℝ => ((x^(2*a-2) : ℝ) : ℂ)*sineRemainder a t x+
      endpointCoefficient a t*((x^(2*a-2)*
        (∫ u : ℝ in Ioi 0, u^((2*a-2)-1)*Real.exp (-u)*Real.sin (x*u)) : ℝ) : ℂ))
      atTop (𝓝 (endpointCoefficient a t*
        ((Real.Gamma (2*a-2)*Real.sin (Real.pi*(2*a-2)/2) : ℝ) : ℂ))) by
    simpa only [Function.comp_def,zero_add] using h).congr'
  filter_upwards with x
  rw [thirdSine_decomposition a t x ha (by linarith)]
  push_cast
  ring

theorem endpointCoefficient_real (a t : ℝ) : endpointCoefficient a t=
    ((t*falling (2*a) 3*RiemannQuarticKernel.kernel 0 : ℝ) : ℂ) := by
  have hk := RiemannThetaComplexKernel.kernelComplex_real 0
  simp only [Complex.ofReal_zero] at hk
  simp only [endpointCoefficient,hk,Complex.ofReal_mul]

theorem falling_three_pos (a : ℝ) (ha : 1 < a) : 0 < falling (2*a) 3 := by
  have h0 : 0 < 2*a := by linarith
  have h1 : 0 < 2*a-1 := by linarith
  have h2 : 0 < 2*a-2 := by linarith
  simpa [falling,Finset.prod_range_succ] using mul_pos (mul_pos h0 h1) h2

theorem thirdSine_scaled_real_limit (a t : ℝ) (ha : 1 < a) (ha3 : a < 3/2) :
    Tendsto (fun x : ℝ => x^(2*a-2)*(thirdSine a t x).re) atTop
      (𝓝 (t*falling (2*a) 3*RiemannQuarticKernel.kernel 0*
        (Real.Gamma (2*a-2)*Real.sin (Real.pi*(2*a-2)/2)))) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (thirdSine_scaled_limit a t ha ha3)
  simpa only [Function.comp_def,endpointCoefficient_real,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using h

theorem eventually_thirdSine_time_signed_positive (a t : ℝ) (ha : 1 < a)
    (ha3 : a < 3/2) (ht : t ≠ 0) :
    ∀ᶠ x : ℝ in atTop, 0 < t*(thirdSine a t x).re := by
  have hk := RiemannQuarticKernel.kernel_pos 0 (by norm_num)
  have hp := falling_three_pos a ha
  have hg := FractionalEndpointLaplace.sine_coefficient_pos (2*a-2) (by linarith) (by linarith)
  have hc : 0 < t*(t*falling (2*a) 3*RiemannQuarticKernel.kernel 0*
      (Real.Gamma (2*a-2)*Real.sin (Real.pi*(2*a-2)/2))) := by
    have hpos := mul_pos (mul_pos (mul_pos (sq_pos_of_ne_zero ht) hp) hk) hg
    nlinarith
  have hh := ((thirdSine_scaled_real_limit a t ha ha3).const_mul t).eventually (Ioi_mem_nhds hc)
  filter_upwards [hh,eventually_gt_atTop (0 : ℝ)] with x hx hx0
  change 0 < t*(x^(2*a-2)*(thirdSine a t x).re) at hx
  have he : t*(x^(2*a-2)*(thirdSine a t x).re)=x^(2*a-2)*(t*(thirdSine a t x).re) := by ring
  rw [he] at hx
  exact pos_of_mul_pos_right hx (Real.rpow_nonneg hx0.le _)

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalFourier
