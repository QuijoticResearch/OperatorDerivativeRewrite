import Foundation.RiemannThetaSmallParameter
import Foundation.RiemannQuarticFarRightTail
/-! Actual compact left-contour bounds valid up to the natural strip boundary.
The cosine margin is retained explicitly and then absorbed using the actual
saddle's positive theta parameter. This does not control the intervening annulus. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarLeftCompact
open RiemannThetaSmallParameter RiemannThetaComplexKernel RiemannThetaDerivativeBounds
open RiemannQuarticFarGaussianLimit RiemannQuarticFarGaussianLocal RiemannQuarticFarRemainder
open RiemannQuarticFarCorrection RiemannQuarticFarSignedIntegral
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch

theorem compact_weight_bound (t : ℝ) (ht : 0 ≤ t) (z : ℂ) (h L s : ℝ)
    (hh : 0 < Real.cos (4*h)) (hs0 : 0 ≤ s) (hsL : s ≤ L) :
    ‖saddleWeight t z ((s : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      (528/Real.cos (4*h)^3)*Real.exp (t*(L^4+h^4)-z.re*h+|z.im| *L) := by
  let q := (s : ℂ)+(h : ℂ)*Complex.I
  have hker := kernel_horizontal_margin_bound s h hs0 hh
  have hconst : 0 ≤ 528/Real.cos (4*h)^3 := by positivity
  have hk : ‖kernelComplex q‖ ≤ 528/Real.cos (4*h)^3 := by
    have he : Real.exp (-3*s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact hker.trans (by nlinarith)
  have hphase : ((t : ℂ)*q^4+Complex.I*z*q).re=
      t*(s^4-6*s^2*h^2+h^4)-z.re*h-z.im*s := by
    dsimp [q]
    simp [pow_succ,Complex.mul_re,Complex.mul_im]
    ring
  have hL4 := pow_le_pow_left₀ hs0 hsL 4
  have hm := mul_le_mul_of_nonneg_left hL4 ht
  have hlin1 := mul_le_mul_of_nonneg_right (neg_le_abs z.im) hs0
  have hlin2 := mul_le_mul_of_nonneg_left hsL (abs_nonneg z.im)
  have hle : ((t : ℂ)*q^4+Complex.I*z*q).re ≤ t*(L^4+h^4)-z.re*h+|z.im| *L := by
    rw [hphase]
    nlinarith [mul_nonneg ht (mul_nonneg (sq_nonneg s) (sq_nonneg h))]
  rw [saddleWeight,norm_mul,Complex.norm_exp]
  have hprod := mul_le_mul (Real.exp_le_exp.mpr hle) hk (norm_nonneg _) (Real.exp_pos _).le
  exact hprod.trans_eq (by ring)

theorem compact_signed_bound (t : ℝ) (ht : 0 ≤ t) (z : ℂ) (h L : ℝ)
    (hh : 0 < Real.cos (4*h)) (hL : 0 ≤ L) :
    IntervalIntegrable (fun s : ℝ => saddleWeight t z ((s : ℂ)+(h : ℂ)*Complex.I)) volume 0 L ∧
    ‖∫ s : ℝ in 0..L, saddleWeight t z ((s : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      (528*L/Real.cos (4*h)^3)*Real.exp (t*(L^4+h^4)-z.re*h+|z.im| *L) := by
  have hc : Continuous (fun s : ℝ => saddleWeight t z ((s : ℂ)+(h : ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    let q := (s : ℂ)+(h : ℂ)*Complex.I
    have hE : (Complex.exp (4*q)).re=Real.exp (4*s)*Real.cos (4*h) := by
      simp [q,Complex.exp_re,Complex.mul_re,Complex.mul_im]
    have hk := kernelComplex_analyticAt q (by rw [hE]; positivity)
    have hw : AnalyticAt ℂ (saddleWeight t z) q := by
      unfold saddleWeight
      apply AnalyticAt.mul
      · fun_prop
      · exact hk
    exact ContinuousAt.comp (g := saddleWeight t z)
      (f := fun s : ℝ => (s : ℂ)+(h : ℂ)*Complex.I) hw.continuousAt (by fun_prop)
  refine ⟨hc.intervalIntegrable 0 L,?_⟩
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := L) (f := fun s : ℝ => saddleWeight t z ((s : ℂ)+(h : ℂ)*Complex.I))
    (C := (528/Real.cos (4*h)^3)*Real.exp (t*(L^4+h^4)-z.re*h+|z.im| *L)) ?_
  · rw [sub_zero,abs_of_nonneg hL] at hbound
    exact hbound.trans_eq (by ring)
  · intro s hs
    rw [uIoc_of_le hL] at hs
    exact compact_weight_bound t ht z h L s hh hs.1.le hs.2

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
    (ha : 64 ≤ a) (hh : |h| ≤ 1) (hz : |z.im| ≤ 1)
    (hE : 1 ≤ (Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re)
    (hupper : Real.pi*(Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re ≤ t*a^3+3) :
    ‖∫ s : ℝ in 0..a-1, saddleWeight t z ((s : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      528*(a-1)*‖saddleWeight t z ((a : ℂ)+(h : ℂ)*Complex.I)‖*
        Real.exp (5*a+3-2*t*a^3) := by
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
  let S := 5*a+3-2*t*a^3
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
  have hz1 := mul_le_mul_of_nonneg_right hz (by linarith : 0 ≤ a-1)
  have hz2 := mul_le_mul_of_nonneg_right ((le_abs_self z.im).trans hz) (by linarith : 0 ≤ a)
  have hPS : B+12*a ≤ P+S := by
    dsimp only [B,P,S]
    rw [hphase]
    change Real.pi*(Complex.exp (4*v)).re ≤ t*a^3+3 at hupper
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


theorem actual_center_theta_upper (t : ℝ) (ht : 0 ≤ t) (z v : ℂ)
    (hv : 0 ≤ v.re) (hz : |z.im| ≤ 1) (hstat : complexSlope t v= -(Complex.I*z))
    (herr : ‖complexSlope t v-modelDerivative t v‖ ≤ 1) :
    Real.pi*(Complex.exp (4*v)).re ≤ t*v.re^3+3 := by
  have he := (Complex.abs_re_le_norm (complexSlope t v-modelDerivative t v)).trans herr
  have hG : (complexSlope t v).re=z.im := by rw [hstat]; simp [Complex.mul_re,Complex.mul_im]
  simp only [Complex.sub_re,hG] at he
  have hD : (modelDerivative t v).re=
      4*t*(v.re^3-3*v.re*v.im^2)+9-4*Real.pi*(Complex.exp (4*v)).re := by
    simp [modelDerivative,Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.mul_im,cube_re]
  rw [hD] at he
  have hzlow := (abs_le.mp hz).1
  have helow := (abs_le.mp he).2
  nlinarith [mul_nonneg ht (mul_nonneg hv (sq_nonneg v.im))]

theorem relative_actual_left_compact_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hzim : |z.im| ≤ 1) :
    ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      1056*Real.sqrt x*(v.re-1)*Real.exp (5*v.re+3-2*t*v.re^3) := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 4*t*‖w‖^3+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 3]
  have hd := horizontal_neighbor_domain t x ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at hd
  have hnear : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hreal := (Complex.abs_re_le_norm (v-w)).trans hnear
  have him := (Complex.abs_im_le_norm (v-w)).trans
    (hv.trans ((div_le_iff₀ hx0).mpr (by linarith : (1 : ℝ) ≤ (1/8)*x)))
  simp only [Complex.sub_re] at hreal
  simp only [Complex.sub_im] at him
  have hvre : 64 ≤ v.re := by linarith [(abs_le.mp hreal).1]
  have hvrem : 0 ≤ v.re-1 := by linarith
  have hvim : |v.im| ≤ 1 := by
    have h := abs_add_le (v.im-w.im) w.im
    rw [sub_add_cancel] at h
    linarith
  have herr := horizontal_neighbor_error t x ht (by linarith) w v (by linarith) hi hs hp0 hv 0 (by norm_num)
  simp only [Complex.ofReal_zero,add_zero] at herr
  have heps : 30005*Real.exp (-4*w.re+4) ≤ 1 := by
    have h := small_error_at_large_real_part w.re hr
    have he := Real.exp_le_exp.mpr (by linarith : -4*w.re+4 ≤ -w.re)
    nlinarith
  have hupper := actual_center_theta_upper t ht0 z v hd.1 hzim hz (herr.trans heps)
  have hvid : (v.re : ℂ)+(v.im : ℂ)*Complex.I=v := by apply Complex.ext <;> simp
  have hbound := actual_left_compact_bound t ht z v.re v.im hvre hvim hzim
    (by rw [hvid]; exact hd.2.1) (by rw [hvid]; exact hupper)
  rw [hvid] at hbound
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let B := 528*(v.re-1)*Real.exp (5*v.re+3-2*t*v.re^3)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnormal := gaussian_normalization_lower t x ht hx w v (by linarith) hi hp hs hv
  change 1 ≤ 2*Real.sqrt x*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (kernel_ne_zero v hd.1 hd.2.1)
  have hnum : ‖∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)‖ ≤ ‖W‖*B :=
    hbound.trans_eq (by dsimp [W,B]; ring)
  have htarget : 1056*Real.sqrt x*(v.re-1)*Real.exp (5*v.re+3-2*t*v.re^3)=2*Real.sqrt x*B := by
    dsimp [B]
    ring
  rw [htarget]
  change ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/(W*G)‖ ≤ _
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  nlinarith


theorem frequency_exp_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w : ℂ) (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) :
    x ≤ 100000000*Real.exp (4*w.re) := by
  have hx0 : 0 < x := by linarith
  have he := arithmetic_error_frequency_bound t x ht hx w hp hs
  have hprod := (le_div_iff₀ hx0).mp he
  have hm := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (4*w.re)).le
  have hid : Real.exp (-4*w.re+4)*Real.exp (4*w.re)=Real.exp 4 := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heq : (30005*Real.exp (-4*w.re+4)*x)*Real.exp (4*w.re)=30005*Real.exp 4*x := by
    calc
      _ = 30005*x*(Real.exp (-4*w.re+4)*Real.exp (4*w.re)) := by ring
      _ = _ := by rw [hid]; ring
  rw [heq] at hm
  have hcoef : 1 ≤ 30005*Real.exp 4 := by linarith [Real.one_le_exp (by norm_num : (0 : ℝ)≤4)]
  have hxlow := mul_le_mul_of_nonneg_right hcoef hx0.le
  nlinarith

def compactBudget (a : ℝ) : ℝ := 10560000*Real.exp (8*a+5-2*a^3)

theorem compactBudget_tendsto_zero : Tendsto compactBudget atTop (nhds 0) := by
  have hu : Tendsto (fun a : ℝ => 10560000*Real.exp (-a)) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (10560000 : ℝ)
  change Tendsto (fun a : ℝ => 10560000*Real.exp (8*a+5-2*a^3)) atTop (nhds 0)
  apply squeeze_zero' (Eventually.of_forall (fun a => by positivity)) _ hu
  filter_upwards [eventually_ge_atTop (64 : ℝ)] with a ha
  have ha2 : a ≤ a^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ a-1) (by linarith : 0 ≤ a)]
  have ha3 : 64*a^2 ≤ a^3 := by nlinarith [mul_nonneg (by linarith : 0 ≤ a-64) (sq_nonneg a)]
  have hexp : 8*a+5-2*a^3 ≤ -a := by nlinarith
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)

theorem relative_left_compact_budget (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hzim : |z.im| ≤ 1) :
    ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      compactBudget v.re := by
  have h := relative_actual_left_compact_bound t x ht hx w v hr hi hs hp hv z hz hzim
  have hx0 : 0 < x := by linarith
  have hfreq := frequency_exp_bound t x ht hx w hp hs
  have hnear : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hreal := (Complex.abs_re_le_norm (v-w)).trans hnear
  simp only [Complex.sub_re] at hreal
  have ha : 64 ≤ v.re := by linarith [(abs_le.mp hreal).1]
  have hw : w.re ≤ v.re+1 := by linarith [(abs_le.mp hreal).1]
  have hsqrt : Real.sqrt x ≤ 10000*Real.exp (2*w.re) := by
    have hsq := Real.sq_sqrt hx0.le
    have hE : Real.exp (2*w.re)^2=Real.exp (4*w.re) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    nlinarith [Real.sqrt_nonneg x,Real.exp_pos (2*w.re),Real.exp_pos (4*w.re)]
  have hsqrt' : Real.sqrt x ≤ 10000*Real.exp (2*v.re+2) :=
    hsqrt.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  have haexp : v.re-1 ≤ Real.exp v.re := by linarith [Real.add_one_le_exp v.re]
  have hta : v.re^3 ≤ t*v.re^3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ v.re) 3]
  apply h.trans
  calc
    _ ≤ 1056*(10000*Real.exp (2*v.re+2))*Real.exp v.re*Real.exp (5*v.re+3-2*v.re^3) := by
      gcongr <;> linarith
    _ = 10560000*(Real.exp (2*v.re+2)*Real.exp v.re*Real.exp (5*v.re+3-2*v.re^3)) := by ring
    _ = compactBudget v.re := by
      rw [← Real.exp_add,← Real.exp_add]
      dsimp [compactBudget]
      congr 2
      ring

theorem eventually_uniform_relative_left_compact (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      120020 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ x →
      modelDerivative t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ z : ℂ, complexSlope t v= -(Complex.I*z) → |z.im| ≤ 1 →
      ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (compactBudget_tendsto_zero.eventually (gt_mem_nhds hη))
  filter_upwards [eventually_ge_atTop (10000 : ℝ),
    eventually_ge_atTop (100000000*Real.exp (4*(A+1)))] with x hx hxA
  intro t ht w v hr hi hp hs hv z hz hzim
  have hfreq := frequency_exp_bound t x ht hx w hp hs
  have hw : A+1 ≤ w.re := by
    have he : Real.exp (4*(A+1)) ≤ Real.exp (4*w.re) := by linarith
    have he' := Real.exp_le_exp.mp he
    linarith
  have hx0 : 0 < x := by linarith
  have hnear : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hreal := (Complex.abs_re_le_norm (v-w)).trans hnear
  simp only [Complex.sub_re] at hreal
  have hvre : A ≤ v.re := by linarith [(abs_le.mp hreal).1]
  exact (relative_left_compact_budget t x ht hx w v hr hi hs hp hv z hz hzim).trans (hA v.re hvre).le

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarLeftCompact
