import Foundation.RiemannEvenCompactWeight
import Foundation.RiemannSixthFarRightTail
import Foundation.RiemannQuarticFarLeftCompact
/-! Actual compact left-contour bounds for the sixth-order growing flow.
The full mixed sixth-order phase is controlled before normalization. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarLeftCompact
open RiemannEvenComplexWeight RiemannEvenModelPhase RiemannEvenSaddleBranch
open RiemannSixthFarGaussianLimit RiemannSixthFarRemainder RiemannSixthFarCorrection
open RiemannThetaComplexKernel RiemannEvenCompactWeight

theorem sixth_compact_phase_gap (a h : ℝ) (ha : 64 ≤ a) (hh : |h| ≤ 1) :
    ((a-1)^2+h^2)^3 - (a^6-15*a^4*h^2+15*a^2*h^4-h^6) ≤ -4*a^5 := by
  have ha0 : 0 ≤ a := by linarith
  have hh2 : h^2 ≤ 1 := by nlinarith [(abs_le.mp hh).1,(abs_le.mp hh).2]
  have hh6 : h^6 ≤ 1 := by
    have h := pow_le_pow_left₀ (sq_nonneg h) hh2 3
    simpa only [← pow_mul,Nat.reduceMul,one_pow] using h
  have hcube := pow_le_pow_left₀ (by positivity : 0 ≤ (a-1)^2+h^2)
    (by linarith : (a-1)^2+h^2 ≤ a^2-2*a+2) 3
  have hm := mul_le_mul_of_nonneg_left hh2 (by positivity : 0 ≤ 15*a^4)
  have h4 : 64*a^2 ≤ a^4 := by
    nlinarith [mul_nonneg (by nlinarith : 0 ≤ a^2-64) (sq_nonneg a)]
  have h2 : 1 ≤ a^2 := by nlinarith
  have h45 : 34*a^4 ≤ a^5 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ a-34) (pow_nonneg ha0 4)]
  have hnonneg : 0 ≤ 15*a^2*h^4 := by positivity
  nlinarith [pow_nonneg ha0 3,pow_nonneg ha0 5]

theorem actual_center_theta_upper (t : ℝ) (ht : 0 ≤ t) (z v : ℂ)
    (hv : 64 ≤ v.re) (hi : |v.im| ≤ 1) (hz : |z.im| ≤ 1)
    (hstat : complexSlope 3 t v= -(Complex.I*z))
    (herr : ‖complexSlope 3 t v-modelDerivative 3 t v‖ ≤ 1) :
    Real.pi*(Complex.exp (4*v)).re ≤ 2*t*v.re^5+3 := by
  have he := (Complex.abs_re_le_norm (complexSlope 3 t v-modelDerivative 3 t v)).trans herr
  have hG : (complexSlope 3 t v).re=z.im := by rw [hstat]; simp [Complex.mul_re,Complex.mul_im]
  simp only [Complex.sub_re,hG] at he
  have hD : (modelDerivative 3 t v).re=
      6*t*(v.re^5-10*v.re^3*v.im^2+5*v.re*v.im^4)+9-
        4*Real.pi*(Complex.exp (4*v)).re := by
    simp [modelDerivative,pow_succ,Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.mul_im]
    <;> ring_nf <;> simp
  rw [hD] at he
  have hi2 : v.im^2 ≤ 1 := by nlinarith [(abs_le.mp hi).1,(abs_le.mp hi).2]
  have hi4 : v.im^4 ≤ 1 := by
    have h := pow_le_pow_left₀ (sq_nonneg v.im) hi2 2
    simpa only [← pow_mul,Nat.reduceMul,one_pow] using h
  have h4 : 16 ≤ v.re^4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 2 ≤ v.re) 4
    norm_num at h
    exact h
  have h5 : 15*v.re ≤ v.re^5 := by
    nlinarith [mul_le_mul_of_nonneg_right h4 (by linarith : 0 ≤ v.re)]
  have hmix := mul_le_mul_of_nonneg_left hi4 (by positivity : 0 ≤ 30*t*v.re)
  have hscale := mul_le_mul_of_nonneg_left h5 ht
  have hneg : 0 ≤ 60*t*v.re^3*v.im^2 := by positivity
  have hzlow := (abs_le.mp hz).1
  have helow := (abs_le.mp he).2
  nlinarith

theorem actual_left_compact_bound (t : ℝ) (ht : 1 ≤ t) (z : ℂ) (a h : ℝ)
    (ha : 64 ≤ a) (hh : |h| ≤ 1) (hz : |z.im| ≤ 1)
    (hE : 1 ≤ (Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re)
    (hupper : Real.pi*(Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re ≤ 2*t*a^5+3) :
    ‖∫ s : ℝ in 0..a-1, weight 3 t z ((s : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      528*(a-1)*‖weight 3 t z ((a : ℂ)+(h : ℂ)*Complex.I)‖*
        Real.exp (5*a+3-2*t*a^5) := by
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
  let B := t*((a-1)^2+h^2)^3-z.re*h+|z.im| *(a-1)
  let P := ((t : ℂ)*v^6+Complex.I*z*v).re+9*a-Real.pi*(Complex.exp (4*v)).re
  let S := 5*a+3-2*t*a^5
  have hbound := (compact_signed_bound 3 t (by linarith) z h (a-1) hhpos (by linarith)).2
  have hbd : ‖∫ s : ℝ in 0..a-1, weight 3 t z ((s : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      528*(a-1)*Real.exp (B+12*a) := by
    apply hbound.trans
    have hm := mul_le_mul_of_nonneg_left hdelta3 (by positivity : 0 ≤ 528*(a-1)*Real.exp B)
    calc
      _ = (528*(a-1)*Real.exp B)*(1/Real.cos (4*h)^3) := by dsimp only [B]; ring
      _ ≤ (528*(a-1)*Real.exp B)*Real.exp (12*a) := hm
      _ = _ := by rw [Real.exp_add B (12*a)]; ring
  have hphase : ((t : ℂ)*v^6+Complex.I*z*v).re=
      t*(a^6-15*a^4*h^2+15*a^2*h^4-h^6)-z.re*h-z.im*a := by
    dsimp [v]
    simp [pow_succ,Complex.mul_re,Complex.mul_im]
    <;> ring_nf <;> simp
  have hpolyT := mul_le_mul_of_nonneg_left (sixth_compact_phase_gap a h ha hh)
    (by linarith : 0 ≤ t)
  have hz1 := mul_le_mul_of_nonneg_right hz (by linarith : 0 ≤ a-1)
  have hz2 := mul_le_mul_of_nonneg_right ((le_abs_self z.im).trans hz) (by linarith : 0 ≤ a)
  have hPS : B+12*a ≤ P+S := by
    dsimp only [B,P,S]
    rw [hphase]
    change Real.pi*(Complex.exp (4*v)).re ≤ 2*t*a^5+3 at hupper
    nlinarith
  have hlower := center_weight_lower 3 t z v (by rw [hvr]; linarith) hE
  rw [hvr] at hlower
  change Real.exp P ≤ ‖weight 3 t z v‖ at hlower
  apply hbd.trans
  have hExpPS := Real.exp_le_exp.mpr hPS
  rw [Real.exp_add P S] at hExpPS
  have hm := mul_le_mul_of_nonneg_right hlower (Real.exp_pos S).le
  have hm' := mul_le_mul_of_nonneg_left (hExpPS.trans hm) (by positivity : 0 ≤ 528*(a-1))
  exact hm'.trans_eq (by dsimp [S,v]; ring)

theorem relative_actual_left_compact_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) (hzim : |z.im| ≤ 1) :
    ‖(∫ s : ℝ in 0..v.re-1, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤
      1056*Real.sqrt x*(v.re-1)*Real.exp (5*v.re+3-2*t*v.re^5) := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hmul := mul_le_mul_of_nonneg_left hpow ht0
  have hp0 : 6*t*‖w‖^5+9 ≤ x := by nlinarith [pow_nonneg (norm_nonneg w) 5]
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
    have hsmall := RiemannQuarticFarCorrection.small_error_at_large_real_part w.re hr
    have he2 := Real.exp_le_exp.mpr (by linarith : -4*w.re+4 ≤ -w.re)
    nlinarith
  have hupper := actual_center_theta_upper t ht0 z v hvre hvim hzim hz (herr.trans heps)
  have hvid : (v.re : ℂ)+(v.im : ℂ)*Complex.I=v := by apply Complex.ext <;> simp
  have hbound := actual_left_compact_bound t ht z v.re v.im hvre hvim hzim
    (by rw [hvid]; exact hd.2.1) (by rw [hvid]; exact hupper)
  rw [hvid] at hbound
  let W := weight 3 t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)
  let B := 528*(v.re-1)*Real.exp (5*v.re+3-2*t*v.re^5)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hnormal := gaussian_normalization_lower t x ht hx w v (by linarith) hi hp hs hv
  change 1 ≤ 2*Real.sqrt x*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (kernel_ne_zero v hd.1 hd.2.1)
  have hnum : ‖∫ s : ℝ in 0..v.re-1, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I)‖ ≤ ‖W‖*B :=
    hbound.trans_eq (by dsimp [W,B]; ring)
  have htarget : 1056*Real.sqrt x*(v.re-1)*Real.exp (5*v.re+3-2*t*v.re^5)=2*Real.sqrt x*B := by
    dsimp [B]
    ring
  rw [htarget]
  change ‖(∫ s : ℝ in 0..v.re-1, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I)) / (W*G)‖ ≤ _
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  nlinarith

open RiemannQuarticFarLeftCompact (compactBudget compactBudget_tendsto_zero)

theorem frequency_exp_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w : ℂ) (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ))) :
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

theorem relative_left_compact_budget (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) (hv : ‖v-w‖ ≤ 1/x)
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) (hzim : |z.im| ≤ 1) :
    ‖(∫ s : ℝ in 0..v.re-1, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤
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
  have h35 : v.re^3 ≤ v.re^5 := pow_le_pow_right₀ (by linarith : 1 ≤ v.re) (by norm_num)
  have ht5 : v.re^5 ≤ t*v.re^5 := by nlinarith [pow_nonneg (by linarith : 0 ≤ v.re) 5]
  have hta : v.re^3 ≤ t*v.re^5 := h35.trans ht5
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
      120020 ≤ w.re → |w.im| ≤ 1/2 → 10000*(t*(‖w‖+1)^5+1) ≤ x →
      modelDerivative 3 t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ z : ℂ, complexSlope 3 t v= -(Complex.I*z) → |z.im| ≤ 1 →
      ‖(∫ s : ℝ in 0..v.re-1, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤ η := by
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

theorem exists_uniform_actual_central_right_compact (R : ℝ)
    (hR0 : 0 < R) (hR : R ≤ 1/8192) :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ t u x : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x →
      ∃ w : ℂ, 10000 ≤ x ∧ 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
        10000*(t*(‖w‖+1)^5+1) ≤ x ∧ modelDerivative 3 t w = -(Complex.I*(x : ℂ)) ∧
        ∀ z : ℂ, ‖z-(x : ℂ)‖ ≤ 1 → ∃ v : ℂ,
          v ∈ closedBall w (1/x) ∧ complexSlope 3 t v = -(Complex.I*z) ∧
          1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ weight 3 t z v ≠ 0 ∧
          weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)) ≠ 0 ∧
          ‖(∫ s : ℝ in -R..R, weight 3 t z (v+(s : ℂ)))/
            (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ ≤ η ∧
          IntegrableOn (fun s : ℝ => weight 3 t z (v+(s : ℂ))) (Ioi R) ∧
          ‖(∫ s : ℝ in Ioi R, weight 3 t z (v+(s : ℂ)))/
            (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤ η ∧
          ‖(∫ s : ℝ in 0..v.re-1, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
            (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤ η := by
  obtain ⟨K,hK,hC⟩ := RiemannSixthFarRightTail.exists_uniform_actual_fixed_gaussian_right_tail R hR0 hR
  refine ⟨K,hK,?_⟩
  intro η hη
  obtain ⟨XC,hXC⟩ := hC η hη
  obtain ⟨XT,hXT⟩ := eventually_atTop.mp (eventually_uniform_relative_left_compact η hη)
  refine ⟨max XC XT,?_⟩
  intro t u x ht hu hstat hx
  have hxC : max XC (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x := by
    exact max_le ((le_max_left XC XT).trans ((le_max_left _ _).trans hx))
      ((le_max_right _ _).trans hx)
  have hxT : XT ≤ x := (le_max_right XC XT).trans ((le_max_left _ _).trans hx)
  obtain ⟨w,hxlarge,hr,hi,hp,hs,hroots⟩ := hXC t u x ht hu hstat hxC
  refine ⟨w,hxlarge,hr,hi,hp,hs,?_⟩
  intro z hz
  obtain ⟨v,hv,hvstat,hvre,hvim,hW,hD,hcentral,htauI,htau⟩ := hroots z hz
  have hvdist : ‖v-w‖ ≤ 1/x := by simpa only [mem_closedBall,dist_eq_norm] using hv
  have hzim : |z.im| ≤ 1 := by
    have hi := (Complex.abs_im_le_norm (z-(x : ℂ))).trans hz
    simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using hi
  have hleft := hXT x hxT t ht w v hr hi hp hs hvdist z hvstat hzim
  exact ⟨v,hv,hvstat,hvre,hvim,hW,hD,hcentral,htauI,htau,hleft⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarLeftCompact
