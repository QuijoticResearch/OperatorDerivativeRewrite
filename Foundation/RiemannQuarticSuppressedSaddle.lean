import Foundation.RiemannQuarticSignedContour
import Foundation.RiemannQuarticHalflineApproximation
import Foundation.RiemannQuarticEndpointSaddle
import Foundation.RiemannQuarticCompactSegment
import Foundation.RiemannQuarticDistantTail
/-! Actual saddle estimates with controlled positive imaginary frequencies.
The real saddle phase retains its exact linear term -u*Im(z). Under
u*Im(z)<=t/8, the actual branch weight is bounded below by peak*exp(-t/4-1).
Combined with broader-y tails and signed contour geometry, this gives an
unshifted half-line relative-error bound for either real-frequency sign.
The linear suppression and all frequency/local-radius conditions are explicit. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticSuppressedSaddle
open RiemannQuarticFrequencyBranch RiemannQuarticPhaseRemainder RiemannQuarticSaddleBranch
open RiemannQuarticQuantitativeSaddle RiemannQuarticSaddleTimes RiemannQuarticContour
open RiemannQuarticDomain RiemannQuarticKernel RiemannQuarticRealSaddle RiemannThetaComplexKernel
open RiemannQuarticEndpointSaddle RiemannQuarticCompactSegment
open RiemannQuarticSignedContour RiemannQuarticHalflineApproximation RiemannQuarticGaussianNormalization

theorem quadratic_phase_real_lower_signed (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z : ℂ) :
    -u*z.im-(‖z‖^2/(8*(t*u^3+1))) ≤
      (Complex.I*(u : ℂ)*z+z^2/(2*deriv (complexSlope t) (u : ℂ))).re := by
  have hQ : 0 < t*u^3+1 := by positivity
  have hl := stationary_slope_deriv_norm_lower t u ht hu hs
  have hn : ‖z^2/(2*deriv (complexSlope t) (u : ℂ))‖ ≤ ‖z‖^2/(8*(t*u^3+1)) := by
    rw [norm_div,norm_pow,norm_mul,Complex.norm_ofNat]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    linarith
  have hab := Complex.abs_re_le_norm (z^2/(2*deriv (complexSlope t) (u : ℂ)))
  have hneg := neg_le_abs (z^2/(2*deriv (complexSlope t) (u : ℂ))).re
  have hlinear : (Complex.I*(u : ℂ)*z).re= -u*z.im := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,mul_zero,zero_sub,mul_one,one_mul,add_zero,sub_zero]
    ring
  rw [Complex.add_re,hlinear]
  linarith
theorem linear_bound_im_upper (t u y : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hlinear : u*y ≤ t/8) :
    y ≤ t/4 := by
  rcases le_total y 0 with hy | hy
  · linarith
  · have hm := mul_le_mul_of_nonneg_right hu hy
    nlinarith

theorem suppressed_weight_norm_lower (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200)
    (hlinear : u*z.im ≤ t/8) (hsmall : (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1)
    (hregion : ‖z‖^2 ≤ t*(t*u^3+1)) :
    weighted 0 t 0 u*Real.exp (-t/4-1) ≤ ‖saddleWeight t z (branch t u ht hu hs z)‖ := by
  obtain ⟨P,hP0,hP⟩ := exists_normalized_phase t u ht hu hs
  let q := Complex.I*(u : ℂ)*z+z^2/(2*deriv (complexSlope t) (u : ℂ))
  have hrem : ‖P z-q‖ ≤ (25600/(t*u^3+1)^2)*‖z‖^3 := by
    have h := phase_quadratic_remainder t u ht hu hs P hP0 hP z hz
    convert h using 1 <;> congr 1 <;> dsimp [q] <;> ring
  have hquad := quadratic_phase_real_lower_signed t u ht hu hs z
  have hab := Complex.abs_re_le_norm (P z-q)
  have hneg := neg_le_abs (P z-q).re
  simp only [Complex.sub_re] at hab hneg
  have hQ : 0 < t*u^3+1 := by positivity
  have hr : ‖z‖^2/(8*(t*u^3+1)) ≤ t/8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8*(t*u^3+1))).mpr
    nlinarith
  have hphase : -t/4-1 ≤ (P z).re := by
    change -u*z.im-(‖z‖^2/(8*(t*u^3+1))) ≤ q.re at hquad
    linarith
  rw [saddleWeight_eq_exp_phase t u ht hu hs P hP0 hP z hz,norm_mul,Complex.norm_exp,
    zero_weight_norm t u (by linarith)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase) (weighted_pos t u (by linarith)).le
theorem compact_relative_suppressed_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) (hlinear : u*z.im ≤ t/8) (hzt : ‖z‖ ≤ t)
    (hsmall : (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1) (hregion : ‖z‖^2 ≤ t*(t*u^3+1))
    (h : ℝ) (hh : |h| ≤ 1/16) :
    ‖∫ x : ℝ in 0..1, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖/
      ‖saddleWeight t z (branch t u ht hu hs z)‖ ≤
      (5676/kernel 3)*Real.exp (10-251*t/4) := by
  have hpeak := hm (by norm_num : (3 : ℝ) ∈ Ici 0)
  change weighted 0 t 0 3 ≤ weighted 0 t 0 u at hpeak
  have hpeak' : Real.exp (81*t)*kernel 3 ≤ weighted 0 t 0 u := by
    have hthree : weighted 0 t 0 3=Real.exp (81*t)*kernel 3 := by
      simp only [weighted,pow_zero,one_mul,zero_mul,add_zero,show (3 : ℝ)^4=81 by norm_num]
      rw [mul_comm t 81]
    rw [hthree] at hpeak
    exact hpeak
  have hA := suppressed_weight_norm_lower t u ht hu hs z hz hlinear hsmall hregion
  have hA' : (Real.exp (81*t)*kernel 3)*Real.exp (-t/4-1) ≤
      ‖saddleWeight t z (branch t u ht hu hs z)‖ :=
    (mul_le_mul_of_nonneg_right hpeak' (Real.exp_pos _).le).trans hA
  have hK := kernel_pos 3 (by norm_num)
  have hden : 0 < (Real.exp (81*t)*kernel 3)*Real.exp (-t/4-1) := by positivity
  have hnum := compact_signed_integral_bound t z h hh
  rw [abs_of_nonneg ht] at hnum
  have hnum' : ‖∫ x : ℝ in 0..1, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      5676*Real.exp (18*t+9) :=
    hnum.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  calc
    _ ≤ (5676*Real.exp (18*t+9))/‖saddleWeight t z (branch t u ht hu hs z)‖ :=
      div_le_div_of_nonneg_right hnum' (lt_of_lt_of_le hden hA').le
    _ ≤ (5676*Real.exp (18*t+9))/((Real.exp (81*t)*kernel 3)*Real.exp (-t/4-1)) :=
      div_le_div_of_nonneg_left (by positivity) hden hA'
    _ = _ := by
      apply (div_eq_iff hden.ne').mpr
      have he : Real.exp (10-251*t/4)*Real.exp (81*t)*Real.exp (-t/4-1)=Real.exp (18*t+9) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      rw [← he]
      have hc : (5676/kernel 3)*kernel 3=5676 := div_mul_cancel₀ _ hK.ne'
      calc
        _ = ((5676/kernel 3)*kernel 3)*
            (Real.exp (10-251*t/4)*Real.exp (81*t)*Real.exp (-t/4-1)) := by rw [hc]
        _ = _ := by ring

theorem left_segment_relative_suppressed_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) (hlinear : u*z.im ≤ t/8)
    (hsmall : (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1) (hregion : ‖z‖^2 ≤ t*(t*u^3+1))
    (h : ℝ) (hh : |h| ≤ 1/16) (hprod : 0 ≤ z.re*h) :
    ‖∫ y : ℝ in 0..h, saddleWeight t z ((y : ℂ)*Complex.I)‖/
      ‖saddleWeight t z (branch t u ht hu hs z)‖ ≤
      (5676/(16*kernel 1))*Real.exp (1-t/4) := by
  have hpeakpos := weighted_pos t u (by linarith)
  have hA := suppressed_weight_norm_lower t u ht hu hs z hz hlinear hsmall hregion
  have hApos : 0 < weighted 0 t 0 u*Real.exp (-t/4-1) := by positivity
  have hnormpos := lt_of_lt_of_le hApos hA
  have hleft := left_segment_relative_peak_signed t u ht (by linarith) hm z h hh hprod
  have hnum := (div_le_iff₀ hpeakpos).mp hleft
  have hK : 0 ≤ 5676/(16*kernel 1) := by positivity [kernel_pos 1 (by norm_num)]
  calc
    _ ≤ ((5676/(16*kernel 1))*Real.exp (-t/2)*weighted 0 t 0 u)/
        ‖saddleWeight t z (branch t u ht hu hs z)‖ :=
      div_le_div_of_nonneg_right hnum hnormpos.le
    _ ≤ ((5676/(16*kernel 1))*Real.exp (-t/2)*weighted 0 t 0 u)/
        (weighted 0 t 0 u*Real.exp (-t/4-1)) :=
      div_le_div_of_nonneg_left (by positivity) hApos hA
    _ = _ := by
      apply (div_eq_iff (ne_of_gt hApos)).mpr
      have he : Real.exp (1-t/4)*Real.exp (-t/4-1)=Real.exp (-t/2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← he]
      ring

theorem suppressed_branch_halfline_relative_error (t u : ℝ) (ht : 0 < t) (hu : 2 ≤ u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) (hlinear : u*z.im ≤ t/8) (hzt : ‖z‖ ≤ t)
    (hphase : (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1) (hregion : ‖z‖^2 ≤ t*(t*u^3+1))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/819200)
    (hsmall : 204800*(t*u^3+1)*r^3 ≤ 1) :
    let w := branch t u ht.le (le_trans (by norm_num : (1 : ℝ)≤2) hu) hs z
    ‖(∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I))/
      (saddleWeight t z w*((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ))-1‖ ≤
      40*Real.sqrt (t*u^3+1)*((5676/kernel 3)*Real.exp (10-251*t/4)+
        horizontalBudget (t*u^3+1) w.re r R) := by
  let hu1 : 1 ≤ u := le_trans (by norm_num : (1 : ℝ)≤2) hu
  let w := branch t u ht.le hu1 hs z
  have hspec := branch_spec t u ht.le hu1 hs z hz.le
  have him := Complex.abs_im_le_norm (w-(u : ℂ))
  have hdist : ‖w-(u : ℂ)‖ ≤ (1/102400 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hspec.1
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at him
  have hh : |w.im| ≤ 1/16 := (him.trans hdist).trans (by norm_num)
  have hcompact := compact_relative_suppressed_bound t u ht.le hu1 hm hs z hz hlinear hzt hphase hregion w.im hh
  have hApos : 0 < ‖saddleWeight t z w‖ := norm_pos_iff.mpr (saddleWeight_ne_zero t u ht.le hu1 hs z hz.le)
  have hc := (div_le_iff₀ hApos).mp hcompact
  have hc' : ‖∫ x : ℝ in 0..1, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)‖ ≤
      ‖saddleWeight t z w‖*((5676/kernel 3)*Real.exp (10-251*t/4)) := by simpa only [mul_comm] using hc
  exact halfline_relative_error_of_compact_bound_yupper t u ht hu hs z w (linear_bound_im_upper t u z.im ht.le hu1 hlinear) hspec.1 hspec.2 r R
    ((5676/kernel 3)*Real.exp (10-251*t/4)) hr hrR hR hsmall hc'

theorem suppressed_unshifted_relative_error (t u : ℝ) (ht : 0 < t) (hu : 2 ≤ u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) (hlinear : u*z.im ≤ t/8) (hzt : ‖z‖ ≤ t)
    (hphase : (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1) (hregion : ‖z‖^2 ≤ t*(t*u^3+1))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/819200)
    (hsmall : 204800*(t*u^3+1)*r^3 ≤ 1) :
    let w := branch t u ht.le (le_trans (by norm_num : (1 : ℝ)≤2) hu) hs z
    ‖(∫ x : ℝ in Ioi 0, saddleWeight t z (x : ℂ))/
      (saddleWeight t z w*((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ))-1‖ ≤
      40*Real.sqrt (t*u^3+1)*((5676/kernel 3)*Real.exp (10-251*t/4)+
        horizontalBudget (t*u^3+1) w.re r R+(5676/(16*kernel 1))*Real.exp (1-t/4)) := by
  let hu1 : 1 ≤ u := le_trans (by norm_num : (1 : ℝ)≤2) hu
  let w := branch t u ht.le hu1 hs z
  let A := saddleWeight t z w
  let G := ((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)
  let J := ∫ x : ℝ in Ioi 0, saddleWeight t z (x : ℂ)
  let Jh := ∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)
  let V := ∫ y : ℝ in 0..w.im, saddleWeight t z ((y : ℂ)*Complex.I)
  let c := 40*Real.sqrt (t*u^3+1)
  let Ce := (5676/(16*kernel 1))*Real.exp (1-t/4)
  have hspec := branch_spec t u ht.le hu1 hs z hz.le
  have hprod := stationary_saddle_height_product t u ht.le hu1 hs z w hspec.1 hspec.2
  have him := (Complex.abs_im_le_norm (w-(u : ℂ))).trans
    (show ‖w-(u : ℂ)‖ ≤ (1/102400 : ℝ) by simpa only [mem_closedBall,dist_eq_norm] using hspec.1)
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at him
  have hhabs : |w.im| ≤ 1/16 := him.trans (by norm_num)
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr (saddleWeight_ne_zero t u ht.le hu1 hs z hz.le)
  have hG := gaussian_norm_lower t u ht.le hu1 hs w hspec.1
  change 1 ≤ c*‖G‖ at hG
  have hc : 0 < c := by dsimp [c]; positivity
  have hGpos : 0 < ‖G‖ := by nlinarith [norm_nonneg G]
  have hCe : 0 ≤ Ce := by dsimp [Ce]; positivity [kernel_pos 1 (by norm_num)]
  have he := left_segment_relative_suppressed_bound t u ht.le hu1 hm hs z hz hlinear hphase hregion
    w.im hhabs hprod
  change ‖V‖/‖A‖ ≤ Ce at he
  have hv := (div_le_iff₀ hApos).mp he
  have hmG := mul_le_mul_of_nonneg_left hG (mul_nonneg hApos.le hCe)
  have hvscaled : ‖V‖ ≤ (c*Ce)*(‖A‖*‖G‖) := by nlinarith
  have hvrelative : ‖Complex.I*V/(A*G)‖ ≤ c*Ce := by
    simp only [norm_div,norm_mul,Complex.norm_I,one_mul]
    exact (div_le_iff₀ (mul_pos hApos hGpos)).mpr hvscaled
  have hshift := halfline_contour_shift_signed t z w.im hhabs
  change J=Jh+Complex.I*V at hshift
  have hid : J/(A*G)-1=(Jh/(A*G)-1)+Complex.I*V/(A*G) := by rw [hshift]; ring
  have hh := suppressed_branch_halfline_relative_error t u ht hu hm hs z hz hlinear hzt hphase hregion r R hr hrR hR hsmall
  change ‖Jh/(A*G)-1‖ ≤ c*((5676/kernel 3)*Real.exp (10-251*t/4)+horizontalBudget (t*u^3+1) w.re r R) at hh
  change ‖J/(A*G)-1‖ ≤ c*((5676/kernel 3)*Real.exp (10-251*t/4)+horizontalBudget (t*u^3+1) w.re r R+Ce)
  rw [hid]
  calc
    _ ≤ ‖Jh/(A*G)-1‖+‖Complex.I*V/(A*G)‖ := norm_add_le _ _
    _ ≤ c*((5676/kernel 3)*Real.exp (10-251*t/4)+horizontalBudget (t*u^3+1) w.re r R)+c*Ce :=
      add_le_add hh hvrelative
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticSuppressedSaddle
