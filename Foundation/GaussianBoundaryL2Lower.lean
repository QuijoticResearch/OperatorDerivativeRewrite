import Foundation.GaussianBoundaryL2Decay

/-! Matching-order integrated lower bound for the persistent Gaussian endpoint layer. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.GaussianBoundaryL2Lower
set_option backward.isDefEq.respectTransparency false
open CoerciveMovingBoundary GaussianBoundaryLayer GaussianBoundaryL2Decay

def strip (c : ℝ) : Set ℝ := Ioo (boundaryPoint c) 1

theorem strip_subset (c : ℝ) (hc : 1 ≤ c) : strip c ⊆ Ioo (-1:ℝ) 1 := by
  intro x hx
  have hh := (boundaryPoint_properties c hc).1
  exact ⟨by linarith [hx.1], hx.2⟩

theorem strip_flux_lower (c x : ℝ) (hc : 1 ≤ c) (hx : x ∈ strip c) :
    fluxFloor ≤ |boundarySlope c x| := by
  obtain ⟨hh, hpoint, hscale⟩ := boundaryPoint_properties c hc
  have hxi := strip_subset c hc hx
  have hxx := inside_square x hxi
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hs : (boundaryPoint c)^2 ≤ x^2 :=
    (sq_le_sq₀ (by linarith : 0 ≤ boundaryPoint c) hx0).mpr hx.1.le
  have hr : (radius x)^2=1-x^2 := Real.sq_sqrt (by linarith)
  have hp : (radius (boundaryPoint c))^2=1-(boundaryPoint c)^2 :=
    Real.sq_sqrt (by linarith)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ c by linarith)
  have hsmall : c*(radius x)^2 ≤ 1/2 := by rw [hp] at hscale; rw [hr]; nlinarith
  have he : Real.exp (-5/8) ≤ Real.exp (-5*c*(radius x)^2/4) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have ha : 1/2 ≤ |x| := (show 1/2 ≤ x by linarith [hx.1]).trans (le_abs_self x)
  have hprod := mul_le_mul (show 3*(1/2 : ℝ)/8 ≤ 3*|x| /8 by linarith) he
    (Real.exp_pos _).le (by positivity : 0 ≤ 3*|x| /8)
  have hf : fluxFloor=3*(1/2 : ℝ)/8*Real.exp (-5/8) := by unfold fluxFloor; ring
  rw [← hf] at hprod
  exact hprod.trans (boundarySlope_lower c x (by linarith) hxx)

theorem strip_derivative_lower (a c x : ℝ) (hc : 1 ≤ c) (hx : x ∈ strip c) :
    fluxFloor ≤ |deriv (fullSquareMean a c) x| := by
  have hxx := inside_square x (strip_subset c hc hx)
  have he : fullSquareMean a c=corridorMean c := funext (fullSquareMean_eq a c)
  rw [he, (corridorMean_hasDerivAt c x hxx).deriv]
  exact strip_flux_lower c x hc hx

theorem strip_width (c : ℝ) (hc : 1 ≤ c) : 1/(4*c) ≤ 1-boundaryPoint c := by
  obtain ⟨hh, hx, hscale⟩ := boundaryPoint_properties c hc
  have hp : (radius (boundaryPoint c))^2=1-(boundaryPoint c)^2 :=
    Real.sq_sqrt (by linarith)
  rw [hp] at hscale
  have hs := mul_nonneg (show 0 ≤ c by linarith) (sq_nonneg (1-boundaryPoint c))
  apply (div_le_iff₀ (by positivity : 0 < 4*c)).mpr
  nlinarith

theorem strip_nonempty_width (c : ℝ) (hc : 1 ≤ c) : boundaryPoint c < 1 := by
  have hw := strip_width c hc
  have hp : 0 < (1:ℝ)/(4*c) := by positivity
  linarith

/-- The lower bound is integrated over a positive-width strip, not only a moving point. -/
theorem errorEnergy_lower (a c : ℝ) (hc : 1 ≤ c) :
    fluxFloor^2/(4*c) ≤ errorEnergy a c := by
  have hc0 : 0 ≤ c := by linarith
  have hp := strip_nonempty_width c hc
  have hf := derivative_square_integrable a c hc0
  have hstrip := hf.mono_set (strip_subset c hc)
  have hconstInt : IntegrableOn (fun _ : ℝ => fluxFloor^2) (strip c) :=
    (continuous_const.intervalIntegrable (boundaryPoint c) 1).1.mono_set Ioo_subset_Ioc_self
  have hconst : (∫ x in strip c, (fluxFloor^2 : ℝ))=(1-boundaryPoint c)*fluxFloor^2 := by
    rw [setIntegral_const]
    simp [strip, Measure.real, Real.volume_Ioo, smul_eq_mul, (show 0 ≤ 1-boundaryPoint c by linarith)]
  have hi : (∫ x in strip c, (fluxFloor^2 : ℝ)) ≤
      ∫ x in strip c, (deriv (fullSquareMean a c) x)^2 := by
    apply integral_mono_ae hconstInt hstrip
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have he := (sq_le_sq₀ fluxFloor_pos.le (abs_nonneg (deriv (fullSquareMean a c) x))).mpr
      (strip_derivative_lower a c x hc hx)
    simpa only [sq_abs] using he
  have hs : (∫ x in strip c, (deriv (fullSquareMean a c) x)^2) ≤ errorEnergy a c := by
    apply setIntegral_mono_set hf
    · exact Filter.Eventually.of_forall fun x => sq_nonneg _
    · exact Filter.Eventually.of_forall fun x hx => strip_subset c hc hx
  have hw := mul_le_mul_of_nonneg_right (strip_width c hc) (sq_nonneg fluxFloor)
  have he : fluxFloor^2/(4*c)=(1/(4*c))*fluxFloor^2 := by ring
  rw [he]
  exact hw.trans (by rw [← hconst]; exact hi.trans hs)

theorem errorEnergy_two_sided (a c : ℝ) (hc : 1 ≤ c) :
    fluxFloor^2/(4*c) ≤ errorEnergy a c ∧ errorEnergy a c ≤ 16/(3*c) :=
  ⟨errorEnergy_lower a c hc, errorEnergy_bound a c (by linarith)⟩

theorem scaled_errorEnergy_bounds (a c : ℝ) (hc : 1 ≤ c) :
    fluxFloor^2/4 ≤ c*errorEnergy a c ∧ c*errorEnergy a c ≤ 16/3 := by
  obtain ⟨hl, hu⟩ := errorEnergy_two_sided a c hc
  have hc0 : 0 ≤ c := by linarith
  have hcl : c*(fluxFloor^2/(4*c))=fluxFloor^2/4 := by field_simp
  have hcu : c*(16/(3*c))=(16/3:ℝ) := by field_simp
  exact ⟨by simpa only [hcl] using mul_le_mul_of_nonneg_left hl hc0,
    by simpa only [hcu] using mul_le_mul_of_nonneg_left hu hc0⟩

end OperatorDerivativeRewrite.Foundation.GaussianBoundaryL2Lower
