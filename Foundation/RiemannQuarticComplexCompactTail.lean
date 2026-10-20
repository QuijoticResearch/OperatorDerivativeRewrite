import Foundation.RiemannQuarticComplexAnnulus
import Foundation.RiemannQuarticFarLeftCompact
/-! Compact actual contour control at lower-half-plane complex frequencies.
The frequency-dependent theta upper bound is retained; dropping it has an
explicit actual stationary counterexample. Full contour dominance is separate. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticComplexCompactTail
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch
open RiemannThetaComplexKernel RiemannThetaDerivativeBounds
open RiemannQuarticFarLeftCompact RiemannQuarticComplexGaussian
open RiemannQuarticFarCorrection

theorem actual_center_theta_upper (t : ℝ) (ht : 0 ≤ t) (z v : ℂ)
    (hv : 0 ≤ v.re) (hstat : complexSlope t v= -(Complex.I*z))
    (herr : ‖complexSlope t v-modelDerivative t v‖ ≤ 1) :
    Real.pi*(Complex.exp (4*v)).re ≤ t*v.re^3+3-z.im/4 := by
  have he := (Complex.abs_re_le_norm (complexSlope t v-modelDerivative t v)).trans herr
  have hG : (complexSlope t v).re=z.im := by rw [hstat]; simp [Complex.mul_re,Complex.mul_im]
  simp only [Complex.sub_re,hG] at he
  have hD : (modelDerivative t v).re=
      4*t*(v.re^3-3*v.re*v.im^2)+9-4*Real.pi*(Complex.exp (4*v)).re := by
    simp [modelDerivative,Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.mul_im,cube_re]
  rw [hD] at he
  have helow := (abs_le.mp he).2
  nlinarith [mul_nonneg ht (mul_nonneg hv (sq_nonneg v.im))]


theorem missing_frequency_term_counterexample :
    ∃ z : ℂ, z.im ≤ 0 ∧ complexSlope 1 (1 : ℂ) = -(Complex.I*z) ∧
      ‖complexSlope 1 (1 : ℂ)-modelDerivative 1 (1 : ℂ)‖ ≤ 1 ∧
      kernelComplex (1 : ℂ) ≠ 0 ∧
      (1 : ℝ)*(1 : ℝ)^3+3 < Real.pi*(Complex.exp (4*(1 : ℂ))).re := by
  have he := RiemannQuarticSaddleNeighborhood.slope_model_error_on_neighborhood
    1 1 (by norm_num) (1 : ℂ) (by norm_num)
  have hreal := complexSlope_real 1 1
  simp only [Complex.ofReal_one] at hreal
  have hd : (modelDerivative 1 (1 : ℂ)).re = 13-4*Real.pi*Real.exp 4 := by
    norm_num [modelDerivative,Complex.exp_re]
  have herr := (Complex.abs_re_le_norm (complexSlope 1 (1 : ℂ)-modelDerivative 1 (1 : ℂ))).trans he
  simp only [Complex.sub_re,hreal,Complex.ofReal_re,hd] at herr
  have hE : 5 ≤ Real.exp (4 : ℝ) := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hprod : 15 < Real.pi*Real.exp 4 := by nlinarith [Real.pi_gt_three]
  have hg : RiemannQuarticSaddleTimes.phaseSlope 1 1 ≤ 0 := by
    linarith [(abs_le.mp herr).2]
  let z : ℂ := Complex.I*(RiemannQuarticSaddleTimes.phaseSlope 1 1 : ℂ)
  have hz : z.im ≤ 0 := by simpa [z,Complex.mul_im] using hg
  have hs : complexSlope 1 (1 : ℂ) = -(Complex.I*z) := by
    rw [hreal]
    dsimp [z]
    ring_nf
    simp
  have hkn : kernelComplex (1 : ℂ) ≠ 0 := by
    apply RiemannThetaComplexKernel.kernel_ne_zero (1 : ℂ) (by norm_num)
    norm_num [Complex.exp_re]
  refine ⟨z,hz,hs,he,hkn,?_⟩
  norm_num [Complex.exp_re]
  linarith

private theorem center_weight_lower (t : ℝ) (z v : ℂ) (hv : 0 ≤ v.re)
    (hE : 1 ≤ (Complex.exp (4*v)).re) :
    Real.exp (((t : ℂ)*v^4+Complex.I*z*v).re+9*v.re-Real.pi*(Complex.exp (4*v)).re) ≤
      ‖saddleWeight t z v‖ := by
  have hk := kernel_norm_lower v hv hE
  have hcoef : 1 ≤ (21/8 : ℝ)*Real.pi := by linarith [Real.pi_gt_three]
  have he := Real.exp_pos (((t : ℂ)*v^4+Complex.I*z*v).re)
  have hm := mul_le_mul_of_nonneg_left hk he.le
  have hnorm : ‖saddleWeight t z v‖=
      Real.exp (((t : ℂ)*v^4+Complex.I*z*v).re)*‖kernelComplex v‖ := by
    rw [saddleWeight,norm_mul,Complex.norm_exp]
  rw [← hnorm] at hm
  have hexp : Real.exp (((t : ℂ)*v^4+Complex.I*z*v).re+9*v.re-Real.pi*(Complex.exp (4*v)).re)=
      Real.exp (((t : ℂ)*v^4+Complex.I*z*v).re)*Real.exp (9*v.re)*
        Real.exp (-Real.pi*(Complex.exp (4*v)).re) := by
    rw [sub_eq_add_neg,Real.exp_add,Real.exp_add]
    simp only [neg_mul]
  rw [hexp]
  have hc := mul_le_mul_of_nonneg_right hcoef
    (by positivity : 0 ≤ Real.exp (((t : ℂ)*v^4+Complex.I*z*v).re)*Real.exp (9*v.re)*
      Real.exp (-Real.pi*(Complex.exp (4*v)).re))
  nlinarith

theorem actual_left_compact_bound (t : ℝ) (ht : 1 ≤ t) (z : ℂ) (a h : ℝ)
    (ha : 64 ≤ a) (hh : |h| ≤ 1) (hz : z.im ≤ 0)
    (hE : 1 ≤ (Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re)
    (hupper : Real.pi*(Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re ≤ t*a^3+3-z.im/4) :
    ‖∫ s : ℝ in 0..a-1, saddleWeight t z ((s : ℂ)+(h : ℂ)*Complex.I)‖ ≤
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
  have hbound := (compact_signed_bound t (by linarith) z h (a-1) hhpos (by linarith)).2
  have hbd : ‖∫ s : ℝ in 0..a-1, saddleWeight t z ((s : ℂ)+(h : ℂ)*Complex.I)‖ ≤
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



theorem relative_actual_left_compact_bound (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hzim : z.im ≤ 0) :
    ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
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
    have h := small_error_at_large_real_part w.re hr
    have he := Real.exp_le_exp.mpr (by linarith : -4*w.re+4 ≤ -w.re)
    nlinarith
  have hupper := actual_center_theta_upper t ht0 z v hd.1 hz (herr.trans heps)
  have hvid : (v.re : ℂ)+(v.im : ℂ)*Complex.I=v := by apply Complex.ext <;> simp
  have hbound := actual_left_compact_bound t ht z v.re v.im hvre hvim hzim
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
  have hnum : ‖∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)‖ ≤ ‖W‖*B :=
    hbound.trans_eq (by dsimp [W,B]; ring)
  have htarget : 1056*Real.sqrt ‖c‖*(v.re-1)*Real.exp (5*v.re+3-2*t*v.re^3+3*z.im/4)=2*Real.sqrt ‖c‖*B := by
    dsimp [B]
    ring
  rw [htarget]
  change ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/(W*G)‖ ≤ _
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  nlinarith




theorem frequency_exp_bound (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖)
    (w : ℂ) (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖)
    (hs : modelDerivative t w= -(Complex.I*c)) :
    ‖c‖ ≤ 100000000*Real.exp (4*w.re) := by
  have hx0 : 0 < ‖c‖ := by linarith
  have he := arithmetic_error_frequency_bound t c hcenter ht hx w hp hs
  have hprod := (le_div_iff₀ hx0).mp he
  have hm := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (4*w.re)).le
  have hid : Real.exp (-4*w.re+4)*Real.exp (4*w.re)=Real.exp 4 := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heq : (30005*Real.exp (-4*w.re+4)*‖c‖)*Real.exp (4*w.re)=30005*Real.exp 4*‖c‖ := by
    calc
      _ = 30005*‖c‖*(Real.exp (-4*w.re+4)*Real.exp (4*w.re)) := by ring
      _ = _ := by rw [hid]; ring
  rw [heq] at hm
  have hcoef : 1 ≤ 30005*Real.exp 4 := by linarith [Real.one_le_exp (by norm_num : (0 : ℝ)≤4)]
  have hxlow := mul_le_mul_of_nonneg_right hcoef hx0.le
  nlinarith



theorem relative_left_compact_budget (t : ℝ) (c : ℂ) (hcenter : c.im ≤ 0) (ht : 1 ≤ t) (hx : 10000 ≤ ‖c‖)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*c))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖) (hv : ‖v-w‖ ≤ 1/‖c‖)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hzim : z.im ≤ 0) :
    ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      compactBudget v.re := by
  have h := relative_actual_left_compact_bound t c hcenter ht hx w v hr hi hs hp hv z hz hzim
  have hx0 : 0 < ‖c‖ := by linarith
  have hfreq := frequency_exp_bound t c hcenter ht hx w hp hs
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


theorem uniform_relative_left_compact (η : ℝ) (hη : 0 < η) :
    ∃ N : ℝ, ∀ c : ℂ, c.im ≤ 0 → N ≤ ‖c‖ → ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      120020 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ ‖c‖ →
      modelDerivative t w = -(Complex.I*c) → ‖v-w‖ ≤ 1/‖c‖ →
      ∀ z : ℂ, complexSlope t v = -(Complex.I*z) → z.im ≤ 0 →
      ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (compactBudget_tendsto_zero.eventually (gt_mem_nhds hη))
  refine ⟨max 10000 (100000000*Real.exp (4*(A+1))),?_⟩
  intro c hc hlarge t ht w v hr hi hp hs hv z hz hzim
  have hx : 10000 ≤ ‖c‖ := (le_max_left _ _).trans hlarge
  have hxA : 100000000*Real.exp (4*(A+1)) ≤ ‖c‖ := (le_max_right _ _).trans hlarge
  have hfreq := frequency_exp_bound t c hc ht hx w hp hs
  have hw : A+1 ≤ w.re := by
    have he : Real.exp (4*(A+1)) ≤ Real.exp (4*w.re) := by linarith
    have he' := Real.exp_le_exp.mp he
    linarith
  have hx0 : 0 < ‖c‖ := by linarith
  have hnear : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hreal := (Complex.abs_re_le_norm (v-w)).trans hnear
  simp only [Complex.sub_re] at hreal
  have hvre : A ≤ v.re := by linarith [(abs_le.mp hreal).1]
  exact (relative_left_compact_budget t c hc ht hx w v hr hi hs hp hv z hz hzim).trans (hA v.re hvre).le

theorem eventually_actual_left_compact (t : ℝ) (ht : 1 ≤ t) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ a : ℝ in atTop, ∀ c : ℂ, c.im ≤ 0 → ‖c‖ = 4*Real.pi*Real.exp (4*a) →
      ∃ v : ℂ, complexSlope t v = -(Complex.I*c) ∧
        1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 ∧
        ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t c ((s : ℂ)+(v.im : ℂ)*Complex.I))/
          (saddleWeight t c v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  obtain ⟨N,hN⟩ := uniform_relative_left_compact η hη
  filter_upwards [RiemannQuarticComplexCorrection.eventually_actual_half_circles t ht,
    RiemannQuarticDomain.quartic_exponent_dominated (80000*(t+1)) 0,
    eventually_ge_atTop (max N (240040 : ℝ))] with a hex hdom ha
  intro c hc hn
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
  exact ⟨v,hroot,hrv,hiv,hkn,hN c hc hNc t ht w v hr hi hps hs hclose c hroot hc⟩

theorem far_actual_left_compact (t : ℝ) (ht : 1 ≤ t) (η : ℝ) (hη : 0 < η) :
    ∃ X : ℝ, 0 < X ∧ ∀ c : ℂ, X ≤ ‖c‖ → c.im ≤ 0 → ∃ v : ℂ,
      complexSlope t v = -(Complex.I*c) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 ∧
      ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t c ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (saddleWeight t c v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (eventually_actual_left_compact t ht η hη)
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
  obtain ⟨v,hroot,hr,hi,hkn,hrel⟩ := hA a hAa c him hn
  exact ⟨v,hroot,hr,hi,hkn,hrel⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticComplexCompactTail
