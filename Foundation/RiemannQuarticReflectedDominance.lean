import Foundation.RiemannQuarticComplexContour
import Foundation.RiemannQuarticFarSimpleZeros
import Foundation.RiemannQuarticNormalizedAnalytic
/-! Reflected-channel bounds retain the main saddle normalization and exact
opposite-height geometry. No nonzero contribution is identified with a nonzero
full transform without bounding both signed channels. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticReflectedDominance
open RiemannQuarticFrequencyBranch RiemannQuarticSaddleBranch RiemannQuarticSaddleTheta
open RiemannQuarticComplexCompactTail RiemannQuarticComplexGaussian
open RiemannQuarticComplexContour RiemannQuarticFarRightTail
open RiemannQuarticFarLeftCompact RiemannThetaComplexKernel RiemannQuarticNaturalContour

theorem reflected_left_compact_bound (t : ℝ) (ht : 1 ≤ t) (z : ℂ) (a h : ℝ)
    (ha : 64 ≤ a) (hh : |h| ≤ 1) (hz : z.im ≤ 0)
    (hE : 1 ≤ (Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re)
    (hupper : Real.pi*(Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re ≤ t*a^3+3-z.im/4) :
    ‖∫ s : ℝ in 0..a-1, saddleWeight t (-z) ((s : ℂ)-(h : ℂ)*Complex.I)‖ ≤
      528*(a-1)*‖saddleWeight t z ((a : ℂ)+(h : ℂ)*Complex.I)‖*
        Real.exp (5*a+3-2*t*a^3+3*z.im/4) := by
  let v := (a : ℂ)+(h : ℂ)*Complex.I
  have ha1 : 0 ≤ a-1 := by linarith
  have hvr : v.re=a := by simp [v]
  have hExp : (Complex.exp (4*v)).re=Real.exp (4*a)*Real.cos (4*h) := by
    simp [v,Complex.exp_re,Complex.mul_re,Complex.mul_im]
  have hhpos : 0 < Real.cos (4*h) := by
    have hp : 0 < Real.exp (4*a)*Real.cos (4*h) := by rw [← hExp]; linarith
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hp
  have hdelta : 1/Real.cos (4*h) ≤ Real.exp (4*a) := by
    apply (div_le_iff₀ hhpos).mpr
    rw [← hExp]
    exact hE
  have hdelta3 := pow_le_pow_left₀ (by positivity : 0 ≤ 1/Real.cos (4*h)) hdelta 3
  have hexp3 : Real.exp (4*a)^3=Real.exp (12*a) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [div_pow,one_pow,hexp3] at hdelta3
  let B := t*((a-1)^4+h^4)-z.re*h+|z.im| *(a-1)
  let P := ((t : ℂ)*v^4+Complex.I*z*v).re+9*a-Real.pi*(Complex.exp (4*v)).re
  let S := 5*a+3-2*t*a^3+3*z.im/4
  have hbound : ‖∫ s : ℝ in 0..a-1, saddleWeight t (-z) ((s : ℂ)-(h : ℂ)*Complex.I)‖ ≤
      (528*(a-1)/Real.cos (4*h)^3)*Real.exp B := by
    have hcos : 0 < Real.cos (4*(-h)) := by simpa only [mul_neg,Real.cos_neg] using hhpos
    have hb := (compact_signed_bound t (by linarith) (-z) (-h) (a-1) hcos (by linarith)).2
    simpa [B,Complex.ofReal_neg,mul_neg,Real.cos_neg,sub_eq_add_neg,show (-h)^4=h^4 by ring] using hb
  have hbd : ‖∫ s : ℝ in 0..a-1, saddleWeight t (-z) ((s : ℂ)-(h : ℂ)*Complex.I)‖ ≤
      528*(a-1)*Real.exp (B+12*a) := by
    apply hbound.trans
    have hm := mul_le_mul_of_nonneg_left hdelta3 (by positivity : 0 ≤ 528*(a-1)*Real.exp B)
    calc
      _ = (528*(a-1)*Real.exp B)*(1/Real.cos (4*h)^3) := by dsimp only [B]; ring
      _ ≤ (528*(a-1)*Real.exp B)*Real.exp (12*a) := hm
      _ = _ := by rw [Real.exp_add B (12*a)]; ring
  have hphase : ((t : ℂ)*v^4+Complex.I*z*v).re=t*(a^4-6*a^2*h^2+h^4)-z.re*h-z.im*a := by
    dsimp [v]
    simp [pow_succ,Complex.mul_re,Complex.mul_im]
    ring
  have hh2 : h^2 ≤ 1 := by nlinarith [(abs_le.mp hh).1,(abs_le.mp hh).2]
  have hmhsq := mul_le_mul_of_nonneg_left hh2 (sq_nonneg a)
  have hcub : 12*a^2+1 ≤ a^3 := by
    have ha2 : 1 ≤ a^2 := by nlinarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ a-64) (sq_nonneg a)]
  have hpoly : (a-1)^4-a^4+6*a^2*h^2 ≤ -3*a^3 := by nlinarith
  have hpolyT := mul_le_mul_of_nonneg_left hpoly (by linarith : 0 ≤ t)
  have hzabs : |z.im| = -z.im := abs_of_nonpos hz
  have hPS : B+12*a ≤ P+S := by
    dsimp only [B,P,S]
    rw [hphase]
    change Real.pi*(Complex.exp (4*v)).re ≤ t*a^3+3-z.im/4 at hupper
    rw [hzabs]
    nlinarith
  have hlower := center_weight_lower t z v (by rw [hvr]; linarith) hE
  rw [hvr] at hlower
  change Real.exp P ≤ ‖saddleWeight t z v‖ at hlower
  apply hbd.trans
  have hExpPS := Real.exp_le_exp.mpr hPS
  rw [Real.exp_add P S] at hExpPS
  have hm := mul_le_mul_of_nonneg_right hlower (Real.exp_pos S).le
  have hm' := mul_le_mul_of_nonneg_left (hExpPS.trans hm) (by positivity : 0 ≤ 528*(a-1))
  exact hm'.trans_eq (by dsimp [S,v]; ring)



theorem actual_gaussian_mass_envelope (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0)
    (ht : 1 ≤ t) (hx : 8 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w = -(Complex.I*c₀))
    (hp : 4*t*‖w‖^3+9 ≤ ‖c₀‖) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v = -(Complex.I*z))
    (heps : 30005*Real.exp (-4*w.re+4) ≤ 1) (s : ℝ) (hsl : -1 ≤ s) :
    ‖saddleWeight t z (v+(s : ℂ))‖ ≤
      3000*‖saddleWeight t z v‖*Real.exp (-(t*w.re^3/4096)*s^2) := by
  let C := t*w.re^3/4096
  have hcub : (4096 : ℝ) ≤ w.re^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) (by linarith : 16 ≤ w.re) 3
    norm_num at h
    exact h
  have htcu : w.re^3 ≤ t*w.re^3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 3]
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hdom0 := horizontal_neighbor_domain t c₀ hcenter ht hx w v (by linarith) hi hs hp hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hdom0
  have hphase : (RiemannQuarticFarSignedIntegral.leadingPhase t z v (s : ℂ)).re ≤
      (30005*Real.exp (-4*w.re+4))*|s|-2*C*s^2 := by
    rcases le_total s 0 with hleft | hright
    · have h := left_phase_quadratic_bound t c₀ hcenter ht hx w v hr hi hs hp hv z hz s hsl hleft
      dsimp [C]
      linarith
    · have h := right_phase_quadratic_bound t c₀ hcenter ht hx w v (by linarith) hi hs hp hv z hz s hright
      rw [abs_of_nonneg hright]
      dsimp [C]
      nlinarith [mul_nonneg (by positivity : 0 ≤ t*w.re^3) (sq_nonneg s)]
  have hdom : 0 ≤ (v+(s : ℂ)).re ∧ 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re := by
    rcases le_total s 0 with hleft | hright
    · have h := left_unit_domain_curvature t c₀ hcenter ht hx w v hr hi hs hp hv s hsl hleft
      exact ⟨h.1,h.2.1⟩
    · have heq : Complex.exp (4*(v+(s : ℂ)))=(Real.exp (4*s) : ℂ)*Complex.exp (4*v) := by
        rw [Complex.ofReal_exp,← Complex.exp_add]
        congr 1
        push_cast
        ring
      have hE : 1 ≤ Real.exp (4*s) := Real.one_le_exp (by positivity)
      constructor
      · simp only [Complex.add_re,Complex.ofReal_re]; linarith [hdom0.1]
      · rw [heq,Complex.mul_re]
        simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
        nlinarith [hdom0.2.1]
  have henv := actual_weight_model_envelope t z v (s : ℂ) hdom0.1 hdom0.2.1 hdom.1 (by linarith [hdom.2])
  have habs : |s| ≤ s^2+1 := by nlinarith [sq_nonneg (|s|-1),sq_abs s]
  have hmul := mul_le_mul_of_nonneg_right hC (sq_nonneg s)
  have he := mul_le_mul_of_nonneg_right heps (abs_nonneg s)
  have hpbound : (RiemannQuarticFarSignedIntegral.leadingPhase t z v (s : ℂ)).re ≤ 1-C*s^2 := by nlinarith
  apply henv.trans
  change 1000*‖saddleWeight t z v‖*Real.exp (RiemannQuarticFarSignedIntegral.leadingPhase t z v (s : ℂ)).re ≤ _
  calc
    _ ≤ 1000*‖saddleWeight t z v‖*Real.exp (1-C*s^2) := by gcongr
    _ = (1000*‖saddleWeight t z v‖)*(Real.exp 1*Real.exp (-C*s^2)) := by rw [sub_eq_add_neg,Real.exp_add]; ring
    _ ≤ (1000*‖saddleWeight t z v‖)*(3*Real.exp (-C*s^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos _).le) (by positivity)
    _ = _ := by dsimp [C]; ring

private theorem gaussian_tail_majorant (F : ℝ → ℂ) (hF : Continuous F)
    (A b : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (hbound : ∀ s : ℝ, -1 ≤ s → ‖F s‖ ≤ A*Real.exp (-b*s^2)) :
    IntegrableOn F (Ioi (-1)) ∧
      ‖∫ s : ℝ in Ioi (-1), F s‖ ≤ A*Real.sqrt (Real.pi/b) := by
  have hg : Integrable (fun s : ℝ => A*Real.exp (-b*s^2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul A
  have hpoint : ∀ᵐ s : ℝ ∂volume.restrict (Ioi (-1)), ‖F s‖ ≤ A*Real.exp (-b*s^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hbound s (le_of_lt hs)
  refine ⟨hg.integrableOn.mono' hF.aestronglyMeasurable hpoint,?_⟩
  have h := norm_integral_le_of_norm_le hg.integrableOn hpoint
  apply h.trans
  have hle := setIntegral_le_integral (s := Ioi (-1)) hg
    (Eventually.of_forall (fun s : ℝ => (show 0 ≤ A*Real.exp (-b*s^2) from by positivity)))
  apply hle.trans_eq
  rw [integral_const_mul,integral_gaussian]

theorem reflected_outer_mass_bound (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0)
    (ht : 1 ≤ t) (hx : 10000 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖)
    (hs : modelDerivative t w = -(Complex.I*c₀)) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v = -(Complex.I*z)) (hy : z.im ≤ -1) :
    IntegrableOn (fun s : ℝ => saddleWeight t (-z) (conj v+(s : ℂ))) (Ioi (-1)) ∧
      ‖∫ s : ℝ in Ioi (-1), saddleWeight t (-z) (conj v+(s : ℂ))‖ ≤
        3000*‖saddleWeight t z v‖*Real.exp (-2*(v.re-1))*
          Real.sqrt (Real.pi/(t*w.re^3/4096)) := by
  have ht0 : 0 < t := by linarith
  have hw0 : 0 < w.re := by linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hpol : 4*t*‖w‖^3+9 ≤ ‖c₀‖ := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0.le
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 3]
  have hg := RiemannQuarticComplexCorrection.corrected_saddle_geometry t c₀ hcenter ht hx w v hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have heps : 30005*Real.exp (-4*w.re+4) ≤ 1 := by
    have hsmall := RiemannQuarticFarCorrection.small_error_at_large_real_part w.re hr
    have he := Real.exp_le_exp.mpr (by linarith : -4*w.re+4 ≤ -w.re)
    nlinarith
  have hcont : Continuous (fun s : ℝ => saddleWeight t (-z) (conj v+(s : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have hq : |(conj v+(s : ℂ)).im| < Real.pi/8 := by simpa using hg.2.1
    exact ContinuousAt.comp (g := saddleWeight t (-z)) (f := fun s : ℝ => conj v+(s : ℂ))
      (weight_analyticAt t (-z) (conj v+(s : ℂ)) hq).continuousAt (by fun_prop)
  apply gaussian_tail_majorant _ hcont
    (3000*‖saddleWeight t z v‖*Real.exp (-2*(v.re-1))) (t*w.re^3/4096)
    (by positivity) (by positivity)
  intro s hsl
  have hmain := actual_gaussian_mass_envelope t c₀ hcenter ht (by linarith) w v hr hi hs hpol hv z hz heps s hsl
  have hu : 0 ≤ v.re+s := by linarith [hg.1]
  have hm := mul_le_mul_of_nonneg_right hy hu
  have hexp : 2*z.im*(v.re+s) ≤ -2*(v.re-1) := by nlinarith
  have hconj : conj (v+(s : ℂ)) = conj v+(s : ℂ) := by simp
  rw [← hconj,reflected_weight_norm]
  simp only [Complex.add_re,Complex.ofReal_re]
  have hb := mul_le_mul hmain (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
  exact hb.trans_eq (by ring)

theorem relative_reflected_left_compact_bound (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hzim : z.im ≤ 0) :
    ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      1056*Real.sqrt ‖c‖*(v.re-1)*Real.exp (5*v.re+3-2*t*v.re^3+3*z.im/4) := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < ‖c‖ := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ ‖c‖ := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have hd := horizontal_neighbor_domain t c hcenter ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hnear : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hreal := (Complex.abs_re_le_norm (v-w)).trans hnear
  have him := (Complex.abs_im_le_norm (v-w)).trans
    (hv.trans ((div_le_iff₀ hx0).mpr (by linarith : (1 : ℝ) ≤ (1/8)*‖c‖)))
  simp only [Complex.sub_re] at hreal
  simp only [Complex.sub_im] at him
  have hvre : 64 ≤ v.re := by linarith [(abs_le.mp hreal).1]
  have hvrem : 0 ≤ v.re-1 := by linarith
  have hvim : |v.im| ≤ 1 := by
    have h := abs_add_le (v.im-w.im) w.im
    rw [sub_add_cancel] at h
    linarith
  have herr := horizontal_neighbor_error t c hcenter ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at herr
  have heps : 30005*Real.exp (-4*w.re+4) ≤ 1 := by
    have h := RiemannQuarticFarCorrection.small_error_at_large_real_part w.re hr
    have he := Real.exp_le_exp.mpr (by linarith : -4*w.re+4 ≤ -w.re)
    nlinarith
  have hupper := RiemannQuarticComplexCompactTail.actual_center_theta_upper t ht0 z v hd.1 hz (herr.trans heps)
  have hvid : (v.re : ℂ)+(v.im : ℂ)*Complex.I=v := by apply Complex.ext <;> simp
  have hbound := reflected_left_compact_bound t ht z v.re v.im hvre hvim hzim
    (by rw [hvid]; exact hd.2.1) (by rw [hvid]; exact hupper)
  rw [hvid] at hbound
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let B := 528*(v.re-1)*Real.exp (5*v.re+3-2*t*v.re^3+3*z.im/4)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnormal := gaussian_normalization_lower t c hcenter ht hx w v (by linarith) hi hp hs hv
  change 1 ≤ 2*Real.sqrt ‖c‖*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (kernel_ne_zero v hd.1 hd.2.1)
  have hnum : ‖∫ s : ℝ in 0..v.re-1, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)‖ ≤ ‖W‖*B :=
    hbound.trans_eq (by dsimp [W,B]; ring)
  have htarget : 1056*Real.sqrt ‖c‖*(v.re-1)*Real.exp (5*v.re+3-2*t*v.re^3+3*z.im/4)=2*Real.sqrt ‖c‖*B := by
    dsimp [B]
    ring
  rw [htarget]
  change ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I))/(W*G)‖ ≤ _
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  nlinarith




theorem relative_reflected_compact_budget (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hzim : z.im ≤ 0) :
    ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      compactBudget v.re := by
  have h := relative_reflected_left_compact_bound t c hcenter ht hx w v hr hi hs hp hv z hz hzim
  have hx0 : 0 < ‖c‖ := by linarith
  have hfreq := RiemannQuarticComplexCompactTail.frequency_exp_bound t c hcenter ht hx w hp hs
  have hnear : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hreal := (Complex.abs_re_le_norm (v-w)).trans hnear
  simp only [Complex.sub_re] at hreal
  have ha : 64 ≤ v.re := by linarith [(abs_le.mp hreal).1]
  have hw : w.re ≤ v.re+1 := by linarith [(abs_le.mp hreal).1]
  have hsqrt : Real.sqrt ‖c‖ ≤ 10000*Real.exp (2*w.re) := by
    have hsq := Real.sq_sqrt hx0.le
    have hE : Real.exp (2*w.re)^2=Real.exp (4*w.re) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    nlinarith [Real.sqrt_nonneg ‖c‖,Real.exp_pos (2*w.re),Real.exp_pos (4*w.re)]
  have hsqrt' : Real.sqrt ‖c‖ ≤ 10000*Real.exp (2*v.re+2) :=
    hsqrt.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  have haexp : v.re-1 ≤ Real.exp v.re := by linarith [Real.add_one_le_exp v.re]
  have hta : v.re^3 ≤ t*v.re^3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ v.re) 3]
  apply h.trans
  calc
    _ ≤ 1056*Real.sqrt ‖c‖*(v.re-1)*Real.exp (5*v.re+3-2*t*v.re^3) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
        (mul_nonneg (by positivity) (by linarith))
    _ ≤ 1056*(10000*Real.exp (2*v.re+2))*Real.exp v.re*Real.exp (5*v.re+3-2*v.re^3) := by
      gcongr <;> linarith
    _ = 10560000*(Real.exp (2*v.re+2)*Real.exp v.re*Real.exp (5*v.re+3-2*v.re^3)) := by ring
    _ = compactBudget v.re := by
      rw [← Real.exp_add,← Real.exp_add]
      dsimp [compactBudget]
      congr 2
      ring


theorem uniform_reflected_compact (η : ℝ) (hη : 0 < η) :
    ∃ N : ℝ, ∀ c : ℂ, c.im ≤ 0 → N ≤ ‖c‖ → ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      120020 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖ →
      modelDerivative t w = -(Complex.I*c) → ‖v-w‖ ≤ 1/‖c‖ →
      ∀ z : ℂ, complexSlope t v = -(Complex.I*z) → z.im ≤ 0 →
      ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (compactBudget_tendsto_zero.eventually (gt_mem_nhds hη))
  refine ⟨max 10000 (100000000*Real.exp (4*(A+1))),?_⟩
  intro c hc hlarge t ht w v hr hi hp hs hv z hz hzim
  have hx : 10000 ≤ ‖c‖ := (le_max_left _ _).trans hlarge
  have hxA : 100000000*Real.exp (4*(A+1)) ≤ ‖c‖ := (le_max_right _ _).trans hlarge
  have hfreq := RiemannQuarticComplexCompactTail.frequency_exp_bound t c hc ht hx w hp hs
  have hw : A+1 ≤ w.re := by
    have he : Real.exp (4*(A+1)) ≤ Real.exp (4*w.re) := by linarith
    have he' := Real.exp_le_exp.mp he
    linarith
  have hx0 : 0 < ‖c‖ := by linarith
  have hnear : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hreal := (Complex.abs_re_le_norm (v-w)).trans hnear
  simp only [Complex.sub_re] at hreal
  have hvre : A ≤ v.re := by linarith [(abs_le.mp hreal).1]
  exact (relative_reflected_compact_budget t c hc ht hx w v hr hi hs hp hv z hz hzim).trans (hA v.re hvre).le

theorem relative_reflected_outer_bound (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0)
    (ht : 1 ≤ t) (hx : 10000 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖)
    (hs : modelDerivative t w = -(Complex.I*c₀)) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v = -(Complex.I*z)) (hy : z.im ≤ -1) :
    ‖(∫ s : ℝ in Ioi (-1), saddleWeight t (-z) (conj v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      6000*Real.sqrt ‖c₀‖*Real.exp (-2*(v.re-1))*Real.sqrt (Real.pi/(t*w.re^3/4096)) := by
  have ht0 : 0 ≤ t := by linarith
  have hpw := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hpol : 4*t*‖w‖^3+9 ≤ ‖c₀‖ := by
    have hm := mul_le_mul_of_nonneg_left hpw ht0
    nlinarith [pow_nonneg (by positivity : 0 ≤ ‖w‖+1) 3]
  have hmass := (reflected_outer_mass_bound t c₀ hcenter ht hx w v hr hi hp hs hv z hz hy).2
  have hd := horizontal_neighbor_domain t c₀ hcenter ht (by linarith) w v (by linarith) hi hs hpol hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let B := 3000*Real.exp (-2*(v.re-1))*Real.sqrt (Real.pi/(t*w.re^3/4096))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnormal := gaussian_normalization_lower t c₀ hcenter ht hx w v (by linarith) hi hp hs hv
  change 1 ≤ 2*Real.sqrt ‖c₀‖*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (RiemannThetaComplexKernel.kernel_ne_zero v hd.1 hd.2.1)
  have hnum : ‖∫ s : ℝ in Ioi (-1), saddleWeight t (-z) (conj v+(s : ℂ))‖ ≤ ‖W‖*B := by
    apply hmass.trans_eq
    dsimp [W,B]
    ring
  have htarget : 6000*Real.sqrt ‖c₀‖*Real.exp (-2*(v.re-1))*Real.sqrt (Real.pi/(t*w.re^3/4096)) =
      2*Real.sqrt ‖c₀‖*B := by dsimp [B]; ring
  rw [htarget]
  change ‖(∫ s : ℝ in Ioi (-1), saddleWeight t (-z) (conj v+(s : ℂ)))/(W*G)‖ ≤ _
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  nlinarith

def reflectionBudget (a : ℝ) : ℝ := 60000000*Real.exp 4*Real.sqrt (Real.pi/a)

theorem reflectionBudget_tendsto_zero : Tendsto reflectionBudget atTop (𝓝 0) := by
  have hdiv : Tendsto (fun a : ℝ => Real.pi/a) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hdiv
  change Tendsto (fun a : ℝ => (60000000*Real.exp 4)*Real.sqrt (Real.pi/a)) atTop (𝓝 0)
  simpa only [Function.comp_def,Real.sqrt_zero,mul_zero] using hs.const_mul (60000000*Real.exp 4)

theorem relative_reflected_outer_budget (t : ℝ) (c₀ : ℂ) (hcenter : c₀.im ≤ 0)
    (ht : 1 ≤ t) (hx : 10000 ≤ ‖c₀‖) (w v : ℂ)
    (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖)
    (hs : modelDerivative t w = -(Complex.I*c₀)) (hv : ‖v-w‖ ≤ 1/‖c₀‖)
    (z : ℂ) (hz : complexSlope t v = -(Complex.I*z)) (hy : z.im ≤ -1) :
    ‖(∫ s : ℝ in Ioi (-1), saddleWeight t (-z) (conj v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      reflectionBudget w.re := by
  have h := relative_reflected_outer_bound t c₀ hcenter ht hx w v hr hi hp hs hv z hz hy
  have hx0 : 0 < ‖c₀‖ := by linarith
  have hw0 : 0 < w.re := by linarith
  have hfreq := RiemannQuarticComplexCompactTail.frequency_exp_bound t c₀ hcenter ht hx w hp hs
  have hnear : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hreal := (Complex.abs_re_le_norm (v-w)).trans hnear
  simp only [Complex.sub_re] at hreal
  have hw : w.re ≤ v.re+1 := by linarith [(abs_le.mp hreal).1]
  have hsqrt : Real.sqrt ‖c₀‖ ≤ 10000*Real.exp (2*w.re) := by
    have hsq := Real.sq_sqrt hx0.le
    have hE : Real.exp (2*w.re)^2 = Real.exp (4*w.re) := by rw [← Real.exp_nat_mul]; congr 1; ring
    nlinarith [Real.sqrt_nonneg ‖c₀‖,Real.exp_pos (2*w.re),Real.exp_pos (4*w.re)]
  have hprod : Real.sqrt ‖c₀‖*Real.exp (-2*(v.re-1)) ≤ 10000*Real.exp 4 := by
    calc
      _ ≤ (10000*Real.exp (2*w.re))*Real.exp (-2*(v.re-1)) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.exp_pos _).le
      _ = 10000*Real.exp (2*w.re-2*v.re+2) := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  have hcube : 4096*w.re ≤ w.re^3 := by
    have hsq : 4096 ≤ w.re^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hsq hw0.le
    nlinarith
  have htc : w.re^3 ≤ t*w.re^3 := by nlinarith [pow_nonneg hw0.le 3]
  have hC : w.re ≤ t*w.re^3/4096 := by linarith
  have hroot : Real.sqrt (Real.pi/(t*w.re^3/4096)) ≤ Real.sqrt (Real.pi/w.re) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left Real.pi_pos.le hw0 hC)
  apply h.trans
  calc
    _ = 6000*(Real.sqrt ‖c₀‖*Real.exp (-2*(v.re-1)))*Real.sqrt (Real.pi/(t*w.re^3/4096)) := by ring
    _ ≤ (6000*(10000*Real.exp 4))*Real.sqrt (Real.pi/w.re) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprod (by norm_num)) hroot (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by dsimp [reflectionBudget]; ring

theorem uniform_reflected_horizontal_bound (η : ℝ) (hη : 0 < η) :
    ∃ N : ℝ, ∀ c₀ : ℂ, c₀.im ≤ 0 → N ≤ ‖c₀‖ → ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      120020 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖ →
      modelDerivative t w = -(Complex.I*c₀) → ‖v-w‖ ≤ 1/‖c₀‖ →
      ∀ z : ℂ, complexSlope t v = -(Complex.I*z) → z.im ≤ -1 →
      ‖(∫ s : ℝ in Ioi 0, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  obtain ⟨N₁,hN₁⟩ := uniform_reflected_compact (η/4) (by positivity)
  obtain ⟨A,hA⟩ := eventually_atTop.mp (reflectionBudget_tendsto_zero.eventually (gt_mem_nhds (by positivity : 0 < η/4)))
  refine ⟨max (max N₁ 10000) (100000000*Real.exp (4*A)),?_⟩
  intro c₀ hc hlarge t ht w v hr hi hp hs hv z hz hy
  have hbase : max N₁ 10000 ≤ ‖c₀‖ := (le_max_left _ _).trans hlarge
  have hN₁c : N₁ ≤ ‖c₀‖ := (le_max_left _ _).trans hbase
  have hx : 10000 ≤ ‖c₀‖ := (le_max_right _ _).trans hbase
  have hxA : 100000000*Real.exp (4*A) ≤ ‖c₀‖ := (le_max_right _ _).trans hlarge
  have hfreq := RiemannQuarticComplexCompactTail.frequency_exp_bound t c₀ hc ht hx w hp hs
  have hw : A ≤ w.re := by
    have he : Real.exp (4*A) ≤ Real.exp (4*w.re) := by linarith
    have hh := Real.exp_le_exp.mp he
    linarith
  have hgeom := RiemannQuarticComplexCorrection.corrected_saddle_geometry t c₀ hc ht hx w v hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have hmass := reflected_outer_mass_bound t c₀ hc ht hx w v hr hi hp hs hv z hz hy
  have hsplit := RiemannQuarticFarHalfline.horizontal_decomposition t (-z) (conj v)
    (by simpa using hgeom.2.1) (-1) hmass.1
  let F := fun s : ℝ => saddleWeight t (-z) (conj v+(s : ℂ))
  have hinv : (∫ s : ℝ in (1 : ℝ)..(-1), F s) = -(∫ s : ℝ in (-1 : ℝ)..1, F s) :=
    intervalIntegral.integral_symm (-1) 1
  let H := ∫ s : ℝ in Ioi 0, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)
  let C := ∫ s : ℝ in 0..v.re-1, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)
  let T := ∫ s : ℝ in Ioi (-1), F s
  have heq : H = C+T := by
    simp only [Complex.conj_re,Complex.conj_im,Complex.ofReal_neg,neg_mul,neg_neg,← sub_eq_add_neg] at hsplit
    change H = C+(∫ s : ℝ in (-1 : ℝ)..1, F s)+(∫ s : ℝ in (1 : ℝ)..(-1), F s)+T at hsplit
    rw [hinv] at hsplit
    linear_combination hsplit
  let D := saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))
  have hC := hN₁ c₀ hc hN₁c t ht w v hr hi hp hs hv z hz (by linarith)
  have hT := (relative_reflected_outer_budget t c₀ hc ht hx w v hr hi hp hs hv z hz hy).trans (hA w.re hw).le
  change ‖C/D‖ ≤ η/4 at hC
  change ‖T/D‖ ≤ η/4 at hT
  change ‖H/D‖ ≤ η
  rw [heq,add_div]
  exact (norm_add_le _ _).trans (by linarith)

theorem uniform_nonzero_below_unit_strip :
    ∃ N : ℝ, ∀ c₀ : ℂ, c₀.im ≤ 0 → N ≤ ‖c₀‖ → ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      120020 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ ‖c₀‖ →
      modelDerivative t w = -(Complex.I*c₀) → ‖v-w‖ ≤ 1/‖c₀‖ →
      ∀ z : ℂ, complexSlope t v = -(Complex.I*z) → z.im ≤ -1 → RiemannQuarticFlow.flow t z ≠ 0 := by
  obtain ⟨N₁,hmain⟩ := uniform_horizontal_gaussian_error (1/4) (by norm_num)
  obtain ⟨N₂,hother⟩ := uniform_reflected_horizontal_bound (1/4) (by norm_num)
  refine ⟨max (max N₁ N₂) 10000,?_⟩
  intro c₀ hc hlarge t ht w v hr hi hp hs hv z hz hy hzero
  have h12 : max N₁ N₂ ≤ ‖c₀‖ := (le_max_left _ _).trans hlarge
  have hx : 10000 ≤ ‖c₀‖ := (le_max_right _ _).trans hlarge
  have hM := (hmain c₀ hc ((le_max_left _ _).trans h12) t ht w v hr hi hp hs hv z hz (by linarith)).2
  have hO := hother c₀ hc ((le_max_right _ _).trans h12) t ht w v hr hi hp hs hv z hz hy
  have hgeom := RiemannQuarticComplexCorrection.corrected_saddle_geometry t c₀ hc ht hx w v hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have hf := flow_eq_paired_horizontal t z v.im hgeom.2.1
  rw [hzero] at hf
  let M := ∫ s : ℝ in Ioi 0, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  let O := ∫ s : ℝ in Ioi 0, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)
  let D := saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))
  change ‖M/D-1‖ ≤ (1/4 : ℝ) at hM
  change ‖O/D‖ ≤ (1/4 : ℝ) at hO
  change 0 = (M+O)/2 at hf
  have hsum : M+O = 0 := by linear_combination -2*hf
  have heq : (M/D-1)+O/D = -1 := by
    calc
      _ = (M+O)/D-1 := by ring
      _ = -1 := by rw [hsum,zero_div,zero_sub]
  have htri := norm_add_le (M/D-1) (O/D)
  rw [heq,norm_neg,norm_one] at htri
  linarith

theorem eventually_nonzero_below_unit_strip (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ a : ℝ in atTop, ∀ c : ℂ, c.im ≤ -1 → ‖c‖ = 4*Real.pi*Real.exp (4*a) →
      RiemannQuarticFlow.flow t c ≠ 0 := by
  obtain ⟨N,hN⟩ := uniform_nonzero_below_unit_strip
  filter_upwards [RiemannQuarticComplexCorrection.eventually_actual_half_circles t ht,
    RiemannQuarticDomain.quartic_exponent_dominated (80000*(t+1)) 0,
    eventually_ge_atTop (max N (240040 : ℝ))] with a hex hdom ha
  intro c hy hn
  have hc : c.im ≤ 0 := by linarith
  have haN : N ≤ a := (le_max_left N _).trans ha
  have ha : 240040 ≤ a := (le_max_right N _).trans ha
  have ha0 : 0 ≤ a := by linarith
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨w,v,hw,hs,hv,hroot,hrv,hiv,hkn,hE,hd⟩ := hex c hc hn
  have hp3 := pow_le_pow_left₀ (by linarith : 0 ≤ a+3) (by linarith : a+3 ≤ 2*a) 3
  have hp34 : a^3 ≤ a^4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ a-1) (pow_nonneg ha0 3)]
  have hM : (a+3)^3 ≤ 8*a^4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 10000*(t+1))
  simp only [zero_mul,add_zero] at hdom
  have hscale : 10000*(t+1)*(a+3)^3 ≤ ‖c‖ := by
    rw [hn]
    nlinarith [Real.pi_gt_three,Real.exp_pos (4*a)]
  have hdist : ‖w-RiemannQuarticComplexModelSaddle.complexAnchor c‖ ≤ (1/1024 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hw
  have hreal := (Complex.abs_re_le_norm (w-RiemannQuarticComplexModelSaddle.complexAnchor c)).trans hdist
  have hg := RiemannQuarticComplexModelSaddle.complexAnchor_geometry a ha0 c hc hn
  simp only [Complex.sub_re,hg.1] at hreal
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hreal).1]
  have hnorm : ‖w‖+1 ≤ a+3 := by
    have hb := norm_add_le (w-RiemannQuarticComplexModelSaddle.complexAnchor c)
      (RiemannQuarticComplexModelSaddle.complexAnchor c)
    rw [sub_add_cancel] at hb
    linarith [hg.2.2]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖+1) hnorm 3
  have hps : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖ := by
    have hmul := mul_le_mul_of_nonneg_left hpow ht0
    nlinarith [pow_nonneg (by linarith : 0 ≤ a+3) 3]
  have hi : |w.im| ≤ 1/2 := by
    have hh := abs_add_le (w.im-(RiemannQuarticComplexModelSaddle.complexAnchor c).im)
      (RiemannQuarticComplexModelSaddle.complexAnchor c).im
    simp only [sub_add_cancel] at hh
    have hdiff := (Complex.abs_im_le_norm (w-RiemannQuarticComplexModelSaddle.complexAnchor c)).trans hdist
    simp only [Complex.sub_im] at hdiff
    linarith [hg.2.1,Real.pi_lt_d2]
  have hNc : N ≤ ‖c‖ := by
    have he := Real.add_one_le_exp (4*a)
    rw [hn]
    nlinarith [Real.pi_gt_three,Real.exp_pos (4*a)]
  have hclose : ‖v-w‖ ≤ 1/‖c‖ := by simpa only [mem_closedBall,dist_eq_norm] using hv
  exact hN c hc hNc t ht w v hr hi hps hs hclose c hroot hy

theorem far_nonzero_below_unit_strip (t : ℝ) (ht : 1 ≤ t) :
    ∃ X : ℝ, 0 < X ∧ ∀ c : ℂ, X ≤ ‖c‖ → c.im ≤ -1 → RiemannQuarticFlow.flow t c ≠ 0 := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (eventually_nonzero_below_unit_strip t ht)
  let X := 4*Real.pi*Real.exp (4*A)
  have hX : 0 < X := by dsimp [X]; positivity
  refine ⟨X,hX,?_⟩
  intro c hc him
  have hn0 : 0 < ‖c‖ := hX.trans_le hc
  let a := Real.log (‖c‖/(4*Real.pi))/4
  have hq : 0 < ‖c‖/(4*Real.pi) := by positivity
  have hn : ‖c‖ = 4*Real.pi*Real.exp (4*a) := by
    rw [show 4*a = Real.log (‖c‖/(4*Real.pi)) by dsimp [a]; ring,Real.exp_log hq]
    field_simp
  have hAa : A ≤ a := by
    have he : Real.exp (4*A) ≤ Real.exp (4*a) := by
      rw [hn] at hc
      change 4*Real.pi*Real.exp (4*A) ≤ 4*Real.pi*Real.exp (4*a) at hc
      exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4*Real.pi)).mp hc
    have hh := Real.exp_le_exp.mp he
    linarith
  exact hA a hAa c him hn

theorem far_right_half_plane_real_simple (t : ℝ) (ht : 1 ≤ t) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ z : ℂ, X ≤ z.re → RiemannQuarticFlow.flow t z = 0 →
      z.im = 0 ∧ deriv (RiemannQuarticFlow.flow t) z ≠ 0 := by
  have hstrip : ∀ᶠ x : ℝ in atTop, ∀ z : ℂ, z.re = x → |z.im| < 1 →
      RiemannQuarticFlow.flow t z = 0 → z.im = 0 ∧ deriv (RiemannQuarticFlow.flow t) z ≠ 0 := by
    filter_upwards [RiemannQuarticFarGaussianLimit.eventually_controlled_far_saddles t ht,
      RiemannQuarticFarCosinePhase.eventually_uniform_zero_strip (1/4) (by norm_num) (by norm_num),
      RiemannQuarticFarSimpleZeros.eventually_uniform_real_simple_zeros] with x hdata hthin hsimple
    intro z hre him hzero
    obtain ⟨hx,w,v₀,hr,hi,hp,hs,hv₀,hz₀,hvre,hvim,hkn⟩ := hdata
    obtain ⟨P,hP0,hP⟩ := RiemannQuarticFarGaussianPhase.exists_normalized_amplitude_phase t x ht hx w hr hi hp hs
    have hnorm : ‖z-(x : ℂ)‖ = |z.im| := by
      have he : z-(x : ℂ) = (z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hre]
      rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    have hzunit : ‖z-(x : ℂ)‖ < 1 := by rw [hnorm]; exact him
    have hbound : |z.im| ≤ 1/w.re := by
      simpa using (hthin t ht hx w hr hi hp hs P hP0 hP z hzunit hzero).2
    have hhalf : |z.im| < 1/2 := hbound.trans_lt ((div_lt_iff₀ (by linarith : 0 < w.re)).mpr (by linarith))
    exact hsimple t ht hx w hr hi hp hs z (by rw [hnorm]; exact hhalf) hzero
  obtain ⟨A,hA⟩ := eventually_atTop.mp hstrip
  obtain ⟨B,hBpos,hB⟩ := far_nonzero_below_unit_strip t ht
  refine ⟨max A (max B 1),(le_max_right B 1).trans (le_max_right A _),?_⟩
  intro z hlarge hzero
  have hAz : A ≤ z.re := (le_max_left _ _).trans hlarge
  have hBz : B ≤ z.re := (le_max_left B 1).trans ((le_max_right A _).trans hlarge)
  have hBn : B ≤ ‖z‖ := hBz.trans (Complex.re_le_norm z)
  by_cases him : |z.im| < 1
  · exact hA z.re hAz z rfl him hzero
  · have hab : 1 ≤ |z.im| := le_of_not_gt him
    exfalso
    rcases le_total z.im 0 with hlo | hhi
    · have hy : z.im ≤ -1 := by rw [abs_of_nonpos hlo] at hab; linarith
      exact hB z hBn hy hzero
    · have hy : (conj z).im ≤ -1 := by
        rw [abs_of_nonneg hhi] at hab
        simp only [Complex.conj_im]
        linarith
      have hzero' : RiemannQuarticFlow.flow t (conj z) = 0 := by
        rw [RiemannQuarticNormalizedAnalytic.flow_conj,hzero]
        simp
      exact hB (conj z) (by simpa using hBn) hy hzero'

theorem far_all_zeros_real (t : ℝ) (ht : 1 ≤ t) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → RiemannQuarticFlow.flow t z = 0 → z.im = 0 := by
  obtain ⟨X,hXpos,hX⟩ := far_right_half_plane_real_simple t ht
  obtain ⟨B,hBpos,hB⟩ := far_nonzero_below_unit_strip t ht
  refine ⟨max B (X+2),lt_of_lt_of_le (by linarith : 0 < X+2) (le_max_right _ _),?_⟩
  intro z hlarge hzero
  have hBn : B ≤ ‖z‖ := (le_max_left _ _).trans hlarge
  by_cases him : |z.im| < 1
  · have hnorm := Complex.norm_le_abs_re_add_abs_im z
    have hXn : X+2 ≤ ‖z‖ := (le_max_right _ _).trans hlarge
    have hreal : X ≤ |z.re| := by linarith
    rcases le_total 0 z.re with hpos | hneg
    · rw [abs_of_nonneg hpos] at hreal
      exact (hX z hreal hzero).1
    · rw [abs_of_nonpos hneg] at hreal
      have hzneg : RiemannQuarticFlow.flow t (-z) = 0 := by rw [RiemannQuarticEvolution.flow_even,hzero]
      have hh := (hX (-z) (by simpa using hreal) hzneg).1
      simpa using hh
  · have hab : 1 ≤ |z.im| := le_of_not_gt him
    exfalso
    rcases le_total z.im 0 with hlo | hhi
    · have hy : z.im ≤ -1 := by rw [abs_of_nonpos hlo] at hab; linarith
      exact hB z hBn hy hzero
    · have hy : (conj z).im ≤ -1 := by
        rw [abs_of_nonneg hhi] at hab
        simp only [Complex.conj_im]
        linarith
      have hzero' : RiemannQuarticFlow.flow t (conj z) = 0 := by
        rw [RiemannQuarticNormalizedAnalytic.flow_conj,hzero]
        simp
      exact hB (conj z) (by simpa using hBn) hy hzero'

end OperatorDerivativeRewrite.Foundation.RiemannQuarticReflectedDominance
