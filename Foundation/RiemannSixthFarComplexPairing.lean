import Foundation.RiemannSixthFarPairing
import Foundation.RiemannSixthFarLeftCompact
/-! Actual A6 complex-frequency pairing, including the signed vertical
endpoint correction. Both Gaussian channels are retained. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarComplexPairing
open RiemannEvenHorizontalPairing RiemannSixthFarPairing
open RiemannSixthFarAnalyticBranch RiemannSixthFarCorrection RiemannSixthFarGaussianLimit
open RiemannSixthFarLeftCompact RiemannEvenCompactWeight
open RiemannEvenComplexWeight RiemannEvenModelPhase RiemannEvenSaddleBranch
open RiemannQuarticFarLeftCompact (compactBudget compactBudget_tendsto_zero)

private theorem center_margin (a h : ℝ)
    (hE : 1 ≤ (Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re) :
    Real.exp (-4*a) ≤ Real.cos (4*h) := by
  have hEq : (Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re=
      Real.exp (4*a)*Real.cos (4*h) := by
    simp [Complex.exp_re,Complex.mul_re,Complex.mul_im]
  rw [hEq] at hE
  rw [show -4*a=-(4*a) by ring,Real.exp_neg,inv_eq_one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr (by nlinarith)

theorem vertical_center_bound (t : ℝ) (ht : 1 ≤ t) (z : ℂ) (a h k : ℝ)
    (ha : 64 ≤ a) (hh : |h| < Real.pi/8) (hk : |k| < Real.pi/8)
    (hz : |z.im| ≤ 1) (hgap : |h-k| ≤ 1) (hfreq : |z.re| *|h-k| ≤ 2)
    (hE : 1 ≤ (Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re)
    (hupper : Real.pi*(Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re ≤ 2*t*a^5+3)
    (hmargin : Real.exp (-4*(a+2)) ≤ Real.cos (4*k)) :
    ‖∫ y : ℝ in k..h, weight 3 t z ((y : ℂ)*Complex.I)‖ ≤
      528*‖weight 3 t z ((a : ℂ)+(h : ℂ)*Complex.I)‖*Real.exp (5*a+3-2*t*a^5) := by
  let v := (a : ℂ)+(h : ℂ)*Complex.I
  let c := Real.exp (-4*(a+2))
  have ht0 : 0 ≤ t := by linarith
  have hc : 0 < c := Real.exp_pos _
  have hch : c ≤ Real.cos (4*h) :=
    (Real.exp_le_exp.mpr (by linarith : -4*(a+2) ≤ -4*a)).trans (center_margin a h hE)
  have hb := vertical_segment_bound 3 t ht0 z h k c hh hk hc hch hmargin
  have hbd : ‖∫ y : ℝ in k..h, weight 3 t z ((y : ℂ)*Complex.I)‖ ≤
      (528/c^3)*Real.exp (t+2-z.re*h) := by
    apply hb.trans
    have hcoef : 528*|h-k|/c^3 ≤ 528/c^3 :=
      div_le_div_of_nonneg_right (by nlinarith) (pow_pos hc 3).le
    exact mul_le_mul hcoef (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
  have hc3 : c^3=Real.exp (-12*(a+2)) := by
    dsimp [c]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hbd' : ‖∫ y : ℝ in k..h, weight 3 t z ((y : ℂ)*Complex.I)‖ ≤
      528*Real.exp (t+2-z.re*h+12*(a+2)) := by
    apply hbd.trans_eq
    rw [hc3]
    calc
      _ = 528*(Real.exp (t+2-z.re*h)/Real.exp (-12*(a+2))) := by ring
      _ = _ := by rw [← Real.exp_sub]; congr 1 <;> ring
  let P := ((t : ℂ)*v^6+Complex.I*z*v).re+9*a-Real.pi*(Complex.exp (4*v)).re
  let S := 5*a+3-2*t*a^5
  have hphase : ((t : ℂ)*v^6+Complex.I*z*v).re=
      t*(a^6-15*a^4*h^2+15*a^2*h^4-h^6)-z.re*h-z.im*a := by
    dsimp [v]
    simp [pow_succ,Complex.mul_re,Complex.mul_im]
    <;> ring_nf <;> simp
  have hh1 : |h| ≤ 1 := by linarith [Real.pi_lt_four]
  have hh2 : h^2 ≤ 1 := by nlinarith [(abs_le.mp hh1).1,(abs_le.mp hh1).2]
  have hh6 : h^6 ≤ 1 := by
    have hp := pow_le_pow_left₀ (sq_nonneg h) hh2 3
    simpa only [← pow_mul,Nat.reduceMul,one_pow] using hp
  have hmhsq := mul_le_mul_of_nonneg_left hh2 (by positivity : 0 ≤ 15*a^4)
  have hzim := mul_le_mul_of_nonneg_right ((le_abs_self z.im).trans hz) (by linarith : 0 ≤ a)
  have ha4 : 1 ≤ a^4 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 1 ≤ a) 4
    simpa using hp
  have h45 : 17*a^4 ≤ a^5 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ a-17) (pow_nonneg (by linarith : 0 ≤ a) 4)]
  have h56 : 6*a^5 ≤ a^6 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ a-6) (pow_nonneg (by linarith : 0 ≤ a) 5)]
  have hpoly : 1 ≤ a^6-4*a^5-15*a^4-1 := by nlinarith
  have hreal6 : 1+4*a^5 ≤ a^6-15*a^4*h^2+15*a^2*h^4-h^6 := by
    nlinarith [show 0 ≤ 15*a^2*h^4 by positivity]
  have hpolyT := mul_le_mul_of_nonneg_left hreal6 ht0
  have hPS : t+2-z.re*h+12*(a+2) ≤ P+S := by
    dsimp only [P,S]
    rw [hphase]
    change Real.pi*(Complex.exp (4*v)).re ≤ 2*t*a^5+3 at hupper
    nlinarith
  have hlower := center_weight_lower 3 t z v (by simp [v]; linarith) hE
  have hvr : v.re=a := by simp [v]
  rw [hvr] at hlower
  change Real.exp P ≤ ‖weight 3 t z v‖ at hlower
  apply hbd'.trans
  have he := Real.exp_le_exp.mpr hPS
  rw [Real.exp_add P S] at he
  have hm := mul_le_mul_of_nonneg_right hlower (Real.exp_pos S).le
  have hm' := mul_le_mul_of_nonneg_left (he.trans hm) (by norm_num : (0 : ℝ) ≤ 528)
  exact hm'.trans_eq (by dsimp [S,v]; ring)

private theorem conjugate_disk (x : ℝ) (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    ‖conj z-(x : ℂ)‖ ≤ 1 := by
  have he : conj z-(x : ℂ)=conj (z-(x : ℂ)) := by simp
  rw [he,norm_conj]
  exact hz

private theorem polynomial_bound (t x : ℝ) (ht : 1 ≤ t) (w : ℂ)
    (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) : 6*t*‖w‖^5+9 ≤ x := by
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 5
  have hm := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ t)
  nlinarith [pow_nonneg (norm_nonneg w) 5]

section FarData
variable (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
  (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
  (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
include ht hx hr hi hp hs
local notation "B" => RiemannSixthFarAnalyticBranch.branch t x ht hx w hr hi hp hs

theorem branch_height_gap (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    |(B z).im-(B (conj z)).im| ≤ |z.im|/x := by
  have h := branch_distance t x ht hx w hr hi hp hs z (conj z) hz (conjugate_disk x z hz)
  have he : z-conj z=(2*(z.im : ℂ))*Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
  have hn : ‖z-conj z‖=2*|z.im| := by
    rw [he,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  have him := Complex.abs_im_le_norm (B z-B (conj z))
  simp only [Complex.sub_im] at him
  apply him.trans
  rw [hn] at h
  exact h.trans_eq (by field_simp)

theorem flow_actual_branch_pair (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    RiemannEvenFlow.flow 3 t z=(horizontalIntegral 3 t z (B z).im+
      conj (horizontalIntegral 3 t (conj z) (B (conj z)).im)+
      Complex.I*(∫ y : ℝ in (B (conj z)).im..(B z).im, weight 3 t z ((y : ℂ)*Complex.I)))/2 :=
  flow_unequal_heights 3 t z (B z).im (B (conj z)).im
    (branch_domain t x ht hx w hr hi hp hs z hz).2.1
    (branch_domain t x ht hx w hr hi hp hs (conj z) (conjugate_disk x z hz)).2.1

theorem actual_branch_endpoint_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    ‖∫ y : ℝ in (B (conj z)).im..(B z).im, weight 3 t z ((y : ℂ)*Complex.I)‖ ≤
      528*‖weight 3 t z (B z)‖*Real.exp (5*(B z).re+3-2*t*(B z).re^5) := by
  let v := B z
  let q := B (conj z)
  have hx0 : 0 < x := by linarith
  have hv : ‖v-w‖ ≤ 1/x := by
    simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t x ht hx w hr hi hp hs z hz).1
  have hq : ‖q-w‖ ≤ 1/x := by
    simpa only [mem_closedBall,dist_eq_norm] using
      (branch_spec t x ht hx w hr hi hp hs (conj z) (conjugate_disk x z hz)).1
  have h12 : 1/x ≤ 2/x := (div_le_div_iff_of_pos_right hx0).mpr (by norm_num)
  have hpol := polynomial_bound t x ht w hp
  have hdv := neighbor_domain t x ht (by linarith) w v (by linarith) hi hs hpol (hv.trans h12)
  have hdq := neighbor_domain t x ht (by linarith) w q (by linarith) hi hs hpol (hq.trans h12)
  have hzim : |z.im| ≤ 1 := by
    simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using (Complex.abs_im_le_norm (z-(x : ℂ))).trans hz
  have hg := (branch_height_gap t x ht hx w hr hi hp hs z hz).trans
    (div_le_div_of_nonneg_right hzim hx0.le)
  change |v.im-q.im| ≤ 1/x at hg
  have hgap : |v.im-q.im| ≤ 1 := hg.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hrez := (Complex.abs_re_le_norm (z-(x : ℂ))).trans hz
  simp only [Complex.sub_re,Complex.ofReal_re] at hrez
  have hzre : |z.re| ≤ x+1 := by
    rw [abs_of_nonneg (by linarith [(abs_le.mp hrez).1] : 0 ≤ z.re)]
    linarith [(abs_le.mp hrez).2]
  have hfreq : |z.re| *|v.im-q.im| ≤ 2 := by
    have hm := mul_le_mul hzre hg (abs_nonneg _) (by linarith : 0 ≤ x+1)
    have hc : (x+1)*(1/x) ≤ 2 := by
      rw [show (x+1)*(1/x)=(x+1)/x by ring]
      exact (div_le_iff₀ hx0).mpr (by linarith)
    exact hm.trans hc
  have hn := hv.trans ((div_le_iff₀ hx0).mpr (by linarith) : 1/x ≤ 1)
  have hreal := (Complex.abs_re_le_norm (v-w)).trans hn
  simp only [Complex.sub_re] at hreal
  have ha : 64 ≤ v.re := by linarith [(abs_le.mp hreal).1]
  have hqreal := (Complex.abs_re_le_norm (q-w)).trans
    (hq.trans ((div_le_iff₀ hx0).mpr (by linarith) : 1/x ≤ 1))
  simp only [Complex.sub_re] at hqreal
  have hqa : q.re ≤ v.re+2 := by linarith [(abs_le.mp hreal).1,(abs_le.mp hqreal).2]
  have hvsplit : (v.re : ℂ)+(v.im : ℂ)*Complex.I=v := by apply Complex.ext <;> simp
  have hqsplit : (q.re : ℂ)+(q.im : ℂ)*Complex.I=q := by apply Complex.ext <;> simp
  have hmargin : Real.exp (-4*(v.re+2)) ≤ Real.cos (4*q.im) :=
    (Real.exp_le_exp.mpr (by linarith : -4*(v.re+2) ≤ -4*q.re)).trans
      (center_margin q.re q.im (by simpa only [hqsplit] using hdq.2.1))
  have herr := neighbor_error_bound t x ht (by linarith) w v (by linarith) hi hs hpol (hv.trans h12)
  have herr1 : ‖complexSlope 3 t v-modelDerivative 3 t v‖ ≤ 1 :=
    herr.trans ((RiemannQuarticFarCorrection.small_error_at_large_real_part w.re hr).trans (by norm_num))
  have hupper := actual_center_theta_upper t (by linarith) z v ha
    (by have hh := (branch_domain t x ht hx w hr hi hp hs z hz).2.1
        linarith [Real.pi_lt_four]) hzim
    (branch_spec t x ht hx w hr hi hp hs z hz).2 herr1
  have hb := vertical_center_bound t ht z v.re v.im q.im ha
    (branch_domain t x ht hx w hr hi hp hs z hz).2.1
    (branch_domain t x ht hx w hr hi hp hs (conj z) (conjugate_disk x z hz)).2.1
    hzim hgap hfreq (by simpa only [hvsplit] using hdv.2.1)
    (by simpa only [hvsplit] using hupper) hmargin
  simpa only [hvsplit] using hb

theorem relative_actual_branch_endpoint_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    ‖(∫ y : ℝ in (B (conj z)).im..(B z).im, weight 3 t z ((y : ℂ)*Complex.I))/
      modelGaussianAmplitude t z (B z)‖ ≤
      1056*Real.sqrt x*Real.exp (5*(B z).re+3-2*t*(B z).re^5) := by
  have hv : ‖B z-w‖ ≤ 1/x := by
    simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t x ht hx w hr hi hp hs z hz).1
  have he := actual_branch_endpoint_bound t x ht hx w hr hi hp hs z hz
  let W := weight 3 t z (B z)
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) (B z)*(s : ℂ)^2/2)
  let F := 528*Real.exp (5*(B z).re+3-2*t*(B z).re^5)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hn := gaussian_normalization_lower t x ht hx w (B z) (by linarith) hi hp hs hv
  change 1 ≤ 2*Real.sqrt x*‖G‖ at hn
  have hA := modelGaussianAmplitude_ne_zero t x ht hx w (B z) hr hi hp hs hv z
  change W*G ≠ 0 at hA
  have hW : W ≠ 0 := (mul_ne_zero_iff.mp hA).1
  have hG : G ≠ 0 := (mul_ne_zero_iff.mp hA).2
  have hnum : ‖∫ y : ℝ in (B (conj z)).im..(B z).im, weight 3 t z ((y : ℂ)*Complex.I)‖ ≤ ‖W‖*F := by
    exact he.trans_eq (by dsimp [W,F]; ring)
  change ‖(∫ y : ℝ in (B (conj z)).im..(B z).im, weight 3 t z ((y : ℂ)*Complex.I))/(W*G)‖ ≤ _
  rw [norm_div,norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hn (mul_nonneg (norm_nonneg W) hF)
  dsimp [F] at hm
  nlinarith

theorem relative_endpoint_budget (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    ‖(∫ y : ℝ in (B (conj z)).im..(B z).im, weight 3 t z ((y : ℂ)*Complex.I))/
      modelGaussianAmplitude t z (B z)‖ ≤ compactBudget (B z).re := by
  have he := relative_actual_branch_endpoint_bound t x ht hx w hr hi hp hs z hz
  have hx0 : 0 < x := by linarith
  have hv : ‖B z-w‖ ≤ 1 := by
    have h := (show ‖B z-w‖ ≤ 1/x by
      simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t x ht hx w hr hi hp hs z hz).1)
    exact h.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hreal := (Complex.abs_re_le_norm (B z-w)).trans hv
  simp only [Complex.sub_re] at hreal
  have ha : 0 ≤ (B z).re := by linarith [(abs_le.mp hreal).1]
  have hw : w.re ≤ (B z).re+1 := by linarith [(abs_le.mp hreal).1]
  have hfreq := frequency_exp_bound t x ht hx w hp hs
  have hsqrt : Real.sqrt x ≤ 10000*Real.exp (2*w.re) := by
    have hsq := Real.sq_sqrt hx0.le
    have hE : Real.exp (2*w.re)^2=Real.exp (4*w.re) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    nlinarith [Real.sqrt_nonneg x,Real.exp_pos (2*w.re),Real.exp_pos (4*w.re)]
  have hsqrt' : Real.sqrt x ≤ 10000*Real.exp (2*(B z).re+2) :=
    hsqrt.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  have ha1 : 1 ≤ (B z).re := by linarith [(abs_le.mp hreal).1]
  have h35 : (B z).re^3 ≤ (B z).re^5 := pow_le_pow_right₀ ha1 (by norm_num)
  have ht5 : (B z).re^5 ≤ t*(B z).re^5 := by nlinarith [pow_nonneg ha 5]
  have hta : (B z).re^3 ≤ t*(B z).re^5 := h35.trans ht5
  apply he.trans
  calc
    _ ≤ 1056*(10000*Real.exp (2*(B z).re+2))*Real.exp (5*(B z).re+3-2*(B z).re^3) := by
      gcongr <;> linarith
    _ = 10560000*Real.exp (7*(B z).re+5-2*(B z).re^3) := by
      calc
        _ = 10560000*(Real.exp (2*(B z).re+2)*Real.exp (5*(B z).re+3-2*(B z).re^3)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring
    _ ≤ compactBudget (B z).re := by
      dsimp [compactBudget]
      gcongr
      linarith

end FarData
theorem eventually_uniform_relative_endpoint (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ (t : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
      (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
      (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
      (z : ℂ), ‖z-(x : ℂ)‖ ≤ 1 →
      ‖(∫ y : ℝ in (branch t x ht hx w hr hi hp hs (conj z)).im..(branch t x ht hx w hr hi hp hs z).im,
        weight 3 t z ((y : ℂ)*Complex.I))/
        modelGaussianAmplitude t z (branch t x ht hx w hr hi hp hs z)‖ ≤ η := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp (compactBudget_tendsto_zero.eventually (gt_mem_nhds hη))
  filter_upwards [eventually_ge_atTop (100000000*Real.exp (4*(A+1)))] with x hxA
  intro t ht hx w hr hi hp hs z hz
  have hf := frequency_exp_bound t x ht hx w hp hs
  have hw : A+1 ≤ w.re := by
    have he : Real.exp (4*(A+1)) ≤ Real.exp (4*w.re) := by linarith
    have he' := Real.exp_le_exp.mp he
    linarith
  have hv : ‖branch t x ht hx w hr hi hp hs z-w‖ ≤ 1 := by
    have h := (show ‖branch t x ht hx w hr hi hp hs z-w‖ ≤ 1/x by
      simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t x ht hx w hr hi hp hs z hz).1)
    exact h.trans ((div_le_iff₀ (by linarith : 0 < x)).mpr (by linarith))
  have hre := (Complex.abs_re_le_norm (branch t x ht hx w hr hi hp hs z-w)).trans hv
  simp only [Complex.sub_re] at hre
  have ha : A ≤ (branch t x ht hx w hr hi hp hs z).re := by linarith [(abs_le.mp hre).1]
  exact (relative_endpoint_budget t x ht hx w hr hi hp hs z hz).trans (hA _ ha).le

private theorem absolute_from_relative (H A : ℂ) (hA : A ≠ 0) (η : ℝ) (he : ‖H/A-1‖ ≤ η) :
    ‖H-A‖ ≤ η*‖A‖ := by
  have hid : H/A-1=(H-A)/A := by field_simp
  rw [hid,norm_div] at he
  exact (div_le_iff₀ (norm_pos_iff.mpr hA)).mp he

theorem eventually_uniform_complex_pair_error (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ (t : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
      (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
      (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x) (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
      (z : ℂ), ‖z-(x : ℂ)‖ ≤ 1 →
      ‖RiemannEvenFlow.flow 3 t z-
        (modelGaussianAmplitude t z (branch t x ht hx w hr hi hp hs z)+
          conj (modelGaussianAmplitude t (conj z) (branch t x ht hx w hr hi hp hs (conj z))))/2‖ ≤
        η*(‖modelGaussianAmplitude t z (branch t x ht hx w hr hi hp hs z)‖+
          ‖modelGaussianAmplitude t (conj z) (branch t x ht hx w hr hi hp hs (conj z))‖) := by
  filter_upwards [eventually_uniform_relative_endpoint (η/4) (by positivity),
    RiemannSixthFarHalfline.eventually_uniform_horizontal_gaussian_error (η/4) (by positivity)]
    with x heV heH
  intro t ht hx w hr hi hp hs z hz
  let B := branch t x ht hx w hr hi hp hs
  let H := horizontalIntegral 3 t z (B z).im
  let J := horizontalIntegral 3 t (conj z) (B (conj z)).im
  let A := modelGaussianAmplitude t z (B z)
  let C := modelGaussianAmplitude t (conj z) (B (conj z))
  let V := ∫ y : ℝ in (B (conj z)).im..(B z).im, weight 3 t z ((y : ℂ)*Complex.I)
  have hzc := conjugate_disk x z hz
  have hstat := branch_spec t x ht hx w hr hi hp hs z hz
  have hstatc := branch_spec t x ht hx w hr hi hp hs (conj z) hzc
  have hv : ‖B z-w‖ ≤ 1/x := by simpa only [mem_closedBall,dist_eq_norm] using hstat.1
  have hvc : ‖B (conj z)-w‖ ≤ 1/x := by simpa only [mem_closedBall,dist_eq_norm] using hstatc.1
  have him : |z.im| ≤ 1 := by
    simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using (Complex.abs_im_le_norm (z-(x : ℂ))).trans hz
  have himc : |(conj z).im| ≤ 1 := by simpa only [Complex.conj_im,abs_neg] using him
  have hAn : A ≠ 0 := modelGaussianAmplitude_ne_zero t x ht hx w (B z) hr hi hp hs hv z
  have hCn : C ≠ 0 := modelGaussianAmplitude_ne_zero t x ht hx w (B (conj z)) hr hi hp hs hvc (conj z)
  have hH := (heH t ht w (B z) hr hi hp hs hv z hstat.2 him).2
  have hJ := (heH t ht w (B (conj z)) hr hi hp hs hvc (conj z) hstatc.2 himc).2
  have hV := heV t ht hx w hr hi hp hs z hz
  change ‖H/A-1‖ ≤ η/4 at hH
  change ‖J/C-1‖ ≤ η/4 at hJ
  change ‖V/A‖ ≤ η/4 at hV
  have hHa := absolute_from_relative H A hAn (η/4) hH
  have hJa := absolute_from_relative J C hCn (η/4) hJ
  rw [norm_div] at hV
  have hVa := (div_le_iff₀ (norm_pos_iff.mpr hAn)).mp hV
  have hpair := flow_actual_branch_pair t x ht hx w hr hi hp hs z hz
  change RiemannEvenFlow.flow 3 t z=(H+conj J+Complex.I*V)/2 at hpair
  have hid : RiemannEvenFlow.flow 3 t z-(A+conj C)/2=((H-A)+conj (J-C)+Complex.I*V)/2 := by
    rw [hpair,map_sub]
    ring
  change ‖RiemannEvenFlow.flow 3 t z-(A+conj C)/2‖ ≤ η*(‖A‖+‖C‖)
  rw [hid,norm_div,Complex.norm_ofNat]
  have h1 := norm_add_le (H-A) (conj (J-C))
  have h2 := norm_add_le ((H-A)+conj (J-C)) (Complex.I*V)
  simp only [norm_conj,norm_mul,Complex.norm_I,one_mul] at h1 h2
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith [norm_nonneg A,norm_nonneg C]

theorem exists_uniform_actual_complex_pair :
    ∃ K : ℝ, 0 < K ∧ ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ t u x : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x →
      ∃ w : ℂ, ∃ (hx : 10000 ≤ x) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
        (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
        (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ))),
        ∃ B : ℂ → ℂ, (∀ z : ℂ, ‖z-(x : ℂ)‖ < 1 → AnalyticAt ℂ B z) ∧
        ∀ z : ℂ, ‖z-(x : ℂ)‖ ≤ 1 →
          B z ∈ closedBall w (1/x) ∧ complexSlope 3 t (B z) = -(Complex.I*z) ∧
          |(B z).im| < Real.pi/8 ∧ modelGaussianAmplitude t z (B z) ≠ 0 ∧
          modelGaussianAmplitude t (conj z) (B (conj z)) ≠ 0 ∧
          IntervalIntegrable (fun y : ℝ => weight 3 t z ((y : ℂ)*Complex.I))
            volume (B (conj z)).im (B z).im ∧
          RiemannEvenFlow.flow 3 t z =
            (horizontalIntegral 3 t z (B z).im+
              conj (horizontalIntegral 3 t (conj z) (B (conj z)).im)+
              Complex.I*(∫ y : ℝ in (B (conj z)).im..(B z).im,
                weight 3 t z ((y : ℂ)*Complex.I)))/2 ∧
          ‖(∫ y : ℝ in (B (conj z)).im..(B z).im, weight 3 t z ((y : ℂ)*Complex.I))/
            modelGaussianAmplitude t z (B z)‖ ≤ η ∧
          ‖RiemannEvenFlow.flow 3 t z-
            (modelGaussianAmplitude t z (B z)+conj (modelGaussianAmplitude t (conj z) (B (conj z))))/2‖ ≤
            η*(‖modelGaussianAmplitude t z (B z)‖+‖modelGaussianAmplitude t (conj z) (B (conj z))‖) := by
  obtain ⟨K,hK,hC⟩ := RiemannSixthFarHalfline.exists_uniform_actual_horizontal_gaussian
  obtain ⟨X₀,hX₀⟩ := hC 1 (by norm_num)
  refine ⟨K,hK,?_⟩
  intro η hη
  obtain ⟨X₁,hX₁⟩ := eventually_atTop.mp (eventually_uniform_complex_pair_error η hη)
  obtain ⟨X₂,hX₂⟩ := eventually_atTop.mp (eventually_uniform_relative_endpoint η hη)
  refine ⟨max X₀ (max X₁ X₂),?_⟩
  intro t u x ht hu hstat hx
  have hx₀ : X₀ ≤ x := le_trans (le_max_left _ _) ((le_max_left _ _).trans hx)
  have hx₁ : X₁ ≤ x := le_trans (le_max_left _ _) ((le_max_right _ _).trans ((le_max_left _ _).trans hx))
  have hx₂ : X₂ ≤ x := le_trans (le_max_right _ _) ((le_max_right _ _).trans ((le_max_left _ _).trans hx))
  have hxold : max X₀ (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x :=
    max_le hx₀ ((le_max_right _ _).trans hx)
  obtain ⟨w,hxl,hr,hi,hp,hs,hroots⟩ := hX₀ t u x ht hu hstat hxold
  let B := branch t x ht hxl w hr hi hp hs
  refine ⟨w,hxl,hr,hi,hp,hs,B,?_,?_⟩
  · intro z hz
    exact branch_analyticAt t x ht hxl w hr hi hp hs z hz
  · intro z hz
    have hzc := conjugate_disk x z hz
    have hv := branch_spec t x ht hxl w hr hi hp hs z hz
    have hq := branch_spec t x ht hxl w hr hi hp hs (conj z) hzc
    have hd := branch_domain t x ht hxl w hr hi hp hs z hz
    have hdq := branch_domain t x ht hxl w hr hi hp hs (conj z) hzc
    have hvd : ‖B z-w‖ ≤ 1/x := by simpa only [mem_closedBall,dist_eq_norm] using hv.1
    have hqd : ‖B (conj z)-w‖ ≤ 1/x := by simpa only [mem_closedBall,dist_eq_norm] using hq.1
    exact ⟨hv.1,hv.2,hd.2.1,
      modelGaussianAmplitude_ne_zero t x ht hxl w (B z) hr hi hp hs hvd z,
      modelGaussianAmplitude_ne_zero t x ht hxl w (B (conj z)) hr hi hp hs hqd (conj z),
      vertical_interval_integrable 3 t z (B z).im (B (conj z)).im hd.2.1 hdq.2.1,
      flow_actual_branch_pair t x ht hxl w hr hi hp hs z hz,
      hX₂ x hx₂ t ht hxl w hr hi hp hs z hz,
      hX₁ x hx₁ t ht hxl w hr hi hp hs z hz⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarComplexPairing
