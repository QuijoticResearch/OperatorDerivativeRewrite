import Foundation.RiemannSixthTransitionGaussianPhase
import Foundation.RiemannSixthTransitionCompact
import Foundation.RiemannSixthFarComplexPairing
import Mathlib.Analysis.Calculus.Deriv.Star
/-! Actual signed paired contours on transition disks, retaining the
vertical residual between independently selected conjugate-frequency heights. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionComplexPairing
open RiemannSixthTransitionAnalyticBranch RiemannSixthTransitionGaussianPhase
open RiemannSixthTransitionCorrection RiemannSixthTransitionGaussian
open RiemannSixthTransitionCompact RiemannSixthFarPairing
open RiemannEvenComplexWeight RiemannEvenModelPhase RiemannEvenSaddleBranch
open RiemannEvenHorizontalPairing (horizontalIntegral)
open RiemannThetaComplexKernel

private theorem conjugate_disk (x r : ℝ) (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    ‖conj z-(x : ℂ)‖ ≤ r := by
  have he : conj z-(x : ℂ)=conj (z-(x : ℂ)) := by simp
  rw [he,norm_conj]
  exact hz

private theorem center_margin (a h : ℝ)
    (hE : 1 ≤ (Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re) :
    Real.exp (-4*a) ≤ Real.cos (4*h) := by
  have hEq : (Complex.exp (4*((a : ℂ)+(h : ℂ)*Complex.I))).re=
      Real.exp (4*a)*Real.cos (4*h) := by simp [Complex.exp_re,Complex.mul_re,Complex.mul_im]
  rw [hEq] at hE
  rw [show -4*a=-(4*a) by ring,Real.exp_neg,inv_eq_one_div]
  exact (div_le_iff₀ (Real.exp_pos _)).mpr (by nlinarith)

section Scaled
variable (t K x r : ℝ) (w : ℂ)
  (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 120020 ≤ w.re)
  (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
  (hnorm : ‖w‖ ≤ 2*w.re) (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
  (hE : ‖Complex.exp (4*w)‖ ≤ K)
  (hsmall : (30005*Real.exp (-w.re))*K ≤ t*w.re^5/4)
  (hrpos : 0 < r) (hradius : r ≤ t*w.re^5/K)
include ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius
local notation "B" => RiemannSixthTransitionAnalyticBranch.branch t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius

theorem branch_height_gap (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    |(B z).im-(B (conj z)).im| ≤ |z.im|/(t*w.re^5) := by
  have h := branch_distance t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z (conj z) hz (conjugate_disk x r z hz)
  have he : z-conj z=(2*(z.im : ℂ))*Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
  have hn : ‖z-conj z‖=2*|z.im| := by
    rw [he,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  have him := Complex.abs_im_le_norm (B z-B (conj z))
  simp only [Complex.sub_im] at him
  apply him.trans
  rw [hn] at h
  exact h.trans_eq (by field_simp)

theorem flow_actual_branch_pair (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    RiemannEvenFlow.flow 3 t z=(horizontalIntegral 3 t z (B z).im+
      conj (horizontalIntegral 3 t (conj z) (B (conj z)).im)+
      Complex.I*(∫ y : ℝ in (B (conj z)).im..(B z).im, weight 3 t z ((y : ℂ)*Complex.I)))/2 :=
  RiemannEvenHorizontalPairing.flow_unequal_heights 3 t z (B z).im (B (conj z)).im
    (branch_domain t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).2.1
    (branch_domain t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius (conj z) (conjugate_disk x r z hz)).2.1

theorem actual_branch_endpoint_bound (hr1 : r ≤ 1)
    (hfreq : (|x|+r)*r ≤ 2*(t*w.re^5))
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    ‖∫ y : ℝ in (B (conj z)).im..(B z).im, weight 3 t z ((y : ℂ)*Complex.I)‖ ≤
      528*‖weight 3 t z (B z)‖*Real.exp (5*(B z).re+3-2*t*(B z).re^5) := by
  let v := B z
  let q := B (conj z)
  have hK0 : 0 < K := by linarith
  have hQ : 0 < t*w.re^5 := by positivity
  have hQ1 : 1 ≤ t*w.re^5 := by
    have hp := one_le_pow₀ (by linarith : 1 ≤ w.re) (n := 5)
    nlinarith
  have hv : ‖v-w‖ ≤ 1/K := by
    simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).1
  have hq : ‖q-w‖ ≤ 1/K := by
    simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius (conj z) (conjugate_disk x r z hz)).1
  have h12 : 1/K ≤ 2/K := by apply (div_le_div_iff_of_pos_right hK0).mpr; norm_num
  have hdv := scaled_neighbor_domain t K (x : ℂ) w v ht hK (by linarith) hmargin hi (by simp) hs hE (hv.trans h12)
  have hdq := scaled_neighbor_domain t K (x : ℂ) w q ht hK (by linarith) hmargin hi (by simp) hs hE (hq.trans h12)
  have hzimr : |z.im| ≤ r := by
    simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using (Complex.abs_im_le_norm (z-(x : ℂ))).trans hz
  have hzim : |z.im| ≤ 1 := hzimr.trans hr1
  have hg := (branch_height_gap t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).trans (div_le_div_of_nonneg_right hzimr hQ.le)
  change |v.im-q.im| ≤ r/(t*w.re^5) at hg
  have hgap : |v.im-q.im| ≤ 1 := hg.trans ((div_le_iff₀ hQ).mpr (by linarith))
  have hzre : |z.re| ≤ |x|+r := by
    have h := abs_add_le (z.re-x) x
    rw [sub_add_cancel] at h
    have hh := (Complex.abs_re_le_norm (z-(x : ℂ))).trans hz
    simp only [Complex.sub_re,Complex.ofReal_re] at hh
    linarith
  have hfreq' : |z.re| *|v.im-q.im| ≤ 2 := by
    have hm := mul_le_mul hzre hg (abs_nonneg _) (by positivity : 0 ≤ |x|+r)
    apply hm.trans
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hQ).mpr hfreq
  have hn := hv.trans ((div_le_iff₀ hK0).mpr (by linarith) : 1/K ≤ 1)
  have hreal := (Complex.abs_re_le_norm (v-w)).trans hn
  simp only [Complex.sub_re] at hreal
  have ha : 64 ≤ v.re := by linarith [(abs_le.mp hreal).1]
  have hqreal := (Complex.abs_re_le_norm (q-w)).trans (hq.trans ((div_le_iff₀ hK0).mpr (by linarith) : 1/K ≤ 1))
  simp only [Complex.sub_re] at hqreal
  have hqa : q.re ≤ v.re+2 := by linarith [(abs_le.mp hreal).1,(abs_le.mp hqreal).2]
  have hvsplit : (v.re : ℂ)+(v.im : ℂ)*Complex.I=v := Complex.re_add_im v
  have hqsplit : (q.re : ℂ)+(q.im : ℂ)*Complex.I=q := Complex.re_add_im q
  have hcosMargin : Real.exp (-4*(v.re+2)) ≤ Real.cos (4*q.im) :=
    (Real.exp_le_exp.mpr (by linarith : -4*(v.re+2) ≤ -4*q.re)).trans
      (center_margin q.re q.im (by simpa only [hqsplit] using hdq.2.1))
  have herr := scaled_neighbor_error t K (x : ℂ) w v ht hK (by linarith) hmargin hi (by simp) hs hE (hv.trans h12)
  have herr1 : ‖complexSlope 3 t v-modelDerivative 3 t v‖ ≤ 1 :=
    herr.trans ((RiemannQuarticFarCorrection.small_error_at_large_real_part w.re hr).trans (by norm_num))
  have hvi := (branch_domain t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).2.1
  have hupper := RiemannSixthFarLeftCompact.actual_center_theta_upper t (by linarith) z v ha
    (by change |(B z).im| ≤ 1; linarith [Real.pi_lt_four] : |v.im| ≤ 1) hzim
    (branch_spec t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).2 herr1
  have hb := RiemannSixthFarComplexPairing.vertical_center_bound t ht z v.re v.im q.im ha
    (branch_domain t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).2.1 (branch_domain t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius (conj z) (conjugate_disk x r z hz)).2.1
    hzim hgap hfreq' (by simpa only [hvsplit] using hdv.2.1)
    (by simpa only [hvsplit] using hupper) hcosMargin
  simpa only [hvsplit] using hb

theorem relative_actual_branch_endpoint_bound (hr1 : r ≤ 1)
    (hfreq : (|x|+r)*r ≤ 2*(t*w.re^5)) (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    ‖(∫ y : ℝ in (B (conj z)).im..(B z).im, weight 3 t z ((y : ℂ)*Complex.I))/
      modelGaussianAmplitude t z (B z)‖ ≤
      4224*Real.sqrt K*(t*w.re^5)*Real.exp (-(t*w.re^5)/32) := by
  let v := B z
  have hv : ‖v-w‖ ≤ 1/K := by
    simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).1
  have he := actual_branch_endpoint_bound t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius hr1 hfreq z hz
  have hgeom := RiemannSixthTransitionCompact.corrected_geometry t K x w v
    ht hK hr hmargin hi hnorm hs hE hsmall hv
  have h : ‖∫ y : ℝ in (B (conj z)).im..v.im, weight 3 t z ((y : ℂ)*Complex.I)‖ ≤
      528*(v.re-1)*‖weight 3 t z v‖*Real.exp (5*v.re+3-2*t*v.re^5) := by
    apply he.trans
    have hm := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ v.re-1 by linarith [hgeom.1])
      (show 0 ≤ 528*‖weight 3 t z v‖*Real.exp (5*v.re+3-2*t*v.re^5) by positivity)
    nlinarith
  have hg := corrected_geometry t K x w v ht hK hr hmargin hi hnorm hs hE hsmall hv
  have hd : ‖v-w‖ ≤ 1/2 := hv.trans ((div_le_iff₀ (by linarith : 0 < K)).mpr (by linarith))
  have hc := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hc
  have hva : w.re ≤ 2*v.re := by linarith [(abs_le.mp hc).1]
  have hcube := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ w.re) hva 5)
    (show 0 ≤ t by linarith)
  have hpoly : 5*v.re+3 ≤ v.re^5 := by
    have hsq : 4096 ≤ v.re^2 := by nlinarith [hg.1]
    have hcu := mul_le_mul_of_nonneg_right hsq (by linarith [hg.1] : 0 ≤ v.re)
    have h35 : v.re^3 ≤ v.re^5 := pow_le_pow_right₀ (by linarith [hg.1] : 1 ≤ v.re) (by norm_num)
    nlinarith [hg.1]
  have htime : v.re^5 ≤ t*v.re^5 := by nlinarith [pow_nonneg (by linarith [hg.1] : 0 ≤ v.re) 5]
  have hexp : 5*v.re+3-2*t*v.re^5 ≤ -(t*w.re^5)/32 := by nlinarith
  have hQ : v.re-1 ≤ t*w.re^5 := by
    have hh : w.re ≤ w.re^5 := by
      have hsq : 1 ≤ w.re^4 := one_le_pow₀ (by linarith : 1 ≤ w.re)
      nlinarith [mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)]
    have htcu : w.re^5 ≤ t*w.re^5 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5]
    linarith [(abs_le.mp hc).2]
  let W := weight 3 t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)
  let L := ∫ y : ℝ in (B (conj z)).im..v.im, weight 3 t z ((y : ℂ)*Complex.I)
  let F := 528*(t*w.re^5)*Real.exp (-(t*w.re^5)/32)
  have hnum : ‖L‖ ≤ ‖W‖*F := by
    apply h.trans
    have hm := mul_le_mul hQ (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
      (show 0 ≤ t*w.re^5 by positivity)
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 528*‖W‖ by positivity)
    dsimp [L,W,F] at *
    nlinarith
  have hnormal := gaussian_normalization_lower t K x w v ht hK hr hmargin hi hnorm hs hE hsmall hv
  change 1 ≤ 8*Real.sqrt K*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hg.2.2
  have hB : 0 ≤ F := by dsimp [F]; positivity
  change ‖L/(W*G)‖ ≤ _
  rw [norm_div, norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  dsimp [F] at *
  nlinarith

theorem paired_amplitude_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    AnalyticAt ℂ (fun y => (modelGaussianAmplitude t y (B y)+
      conj (modelGaussianAmplitude t (conj y) (B (conj y))))/2) z := by
  have hd : DifferentiableOn ℂ (fun y => (modelGaussianAmplitude t y (B y)+
      conj (modelGaussianAmplitude t (conj y) (B (conj y))))/2) (ball (x : ℂ) r) := by
    intro y hy
    have hy' : ‖y-(x : ℂ)‖ < r := by simpa only [mem_ball,dist_eq_norm] using hy
    have hyc : ‖conj y-(x : ℂ)‖ < r := by
      have hid : conj y-(x : ℂ)=conj (y-(x : ℂ)) := by simp
      rwa [hid,norm_conj]
    have ha := amplitude_hasDerivAt t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius y hy'
    have hc := amplitude_hasDerivAt t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius (conj y) hyc
    have hc' := hc.conj_conj
    simp only [Function.comp_apply,Complex.conj_conj] at hc'
    exact ((ha.add hc').div_const (2 : ℂ)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_eq_norm] using hz))

end Scaled

private theorem absolute_from_relative (H A : ℂ) (hA : A ≠ 0) (η : ℝ) (he : ‖H/A-1‖ ≤ η) :
    ‖H-A‖ ≤ η*‖A‖ := by
  have hid : H/A-1=(H-A)/A := by field_simp
  rw [hid,norm_div] at he
  exact (div_le_iff₀ (norm_pos_iff.mpr hA)).mp he

theorem eventually_uniform_complex_pair_error (C η : ℝ) (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ Q : ℝ in atTop, ∀ (t K x r : ℝ) (w : ℂ)
      (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 120020 ≤ w.re)
  (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
      (hnorm : ‖w‖ ≤ 2*w.re) (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
      (hE : ‖Complex.exp (4*w)‖ ≤ K)
      (hsmall : (30005*Real.exp (-w.re))*K ≤ t*w.re^5/4)
      (hrpos : 0 < r) (hradius : r ≤ t*w.re^5/K),
      r ≤ 1 → (|x|+r)*r ≤ 2*Q → Q=t*w.re^5 → K ≤ C*Q →
      let B := RiemannSixthTransitionAnalyticBranch.branch t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius
      ∀ z : ℂ, ‖z-(x : ℂ)‖ ≤ r →
        ‖RiemannEvenFlow.flow 3 t z-(modelGaussianAmplitude t z (B z)+
          conj (modelGaussianAmplitude t (conj z) (B (conj z))))/2‖ ≤
          η*(‖modelGaussianAmplitude t z (B z)‖+‖modelGaussianAmplitude t (conj z) (B (conj z))‖) := by
  filter_upwards [eventually_uniform_horizontal_error C (η/4) hC (by positivity),
    eventually_ge_atTop (1 : ℝ),
    (compact_budget_tendsto_zero C).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η/4))]
    with Q heH hQ hbudget
  intro t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius hr1 hfreq hQid hscale
  dsimp only
  let B := RiemannSixthTransitionAnalyticBranch.branch t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius
  intro z hz
  let H := horizontalIntegral 3 t z (B z).im
  let J := horizontalIntegral 3 t (conj z) (B (conj z)).im
  let A := modelGaussianAmplitude t z (B z)
  let D := modelGaussianAmplitude t (conj z) (B (conj z))
  let V := ∫ y : ℝ in (B (conj z)).im..(B z).im, weight 3 t z ((y : ℂ)*Complex.I)
  have hzc := conjugate_disk x r z hz
  have hstat := branch_spec t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz
  have hstatc := branch_spec t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius (conj z) hzc
  have hv : ‖B z-w‖ ≤ 1/K := by simpa only [mem_closedBall,dist_eq_norm] using hstat.1
  have hvc : ‖B (conj z)-w‖ ≤ 1/K := by simpa only [mem_closedBall,dist_eq_norm] using hstatc.1
  have him : |z.im| ≤ 1 := by
    have hh := (Complex.abs_im_le_norm (z-(x : ℂ))).trans (hz.trans hr1)
    simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using hh
  have himc : |(conj z).im| ≤ 1 := by simpa only [Complex.conj_im,abs_neg] using him
  have hAn : A ≠ 0 := mul_ne_zero
    (actual_weight_ne_zero t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz)
    (gaussian_ne_zero t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz)
  have hDn : D ≠ 0 := mul_ne_zero
    (actual_weight_ne_zero t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius (conj z) hzc)
    (gaussian_ne_zero t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius (conj z) hzc)
  have hH := heH t K x w (B z) z ht hK hr hmargin hi hnorm hs hE hsmall hv hstat.2
    him hQid hscale
  have hJ := heH t K x w (B (conj z)) (conj z) ht hK hr hmargin hi hnorm hs hE hsmall hvc hstatc.2
    himc hQid hscale
  have hV := relative_actual_branch_endpoint_bound t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius
    hr1 (by simpa only [hQid] using hfreq) z hz
  rw [← hQid] at hV
  have hroot : Real.sqrt K ≤ Real.sqrt C*Q := by
    have hh : Real.sqrt Q ≤ Q := by nlinarith [Real.sq_sqrt (show 0 ≤ Q by linarith),Real.sqrt_nonneg Q]
    have hm := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg C)
    have hk := Real.sqrt_le_sqrt hscale
    rw [Real.sqrt_mul hC.le] at hk
    linarith
  have hmul := mul_le_mul_of_nonneg_right hroot (show 0 ≤ 4224*Q*Real.exp (-Q/32) by positivity)
  change ‖H/A-1‖ < η/4 at hH
  change ‖J/D-1‖ < η/4 at hJ
  have hV' : ‖V/A‖ ≤ η/4 := by
    change ‖V/A‖ ≤ _ at hV
    nlinarith
  have hHa := absolute_from_relative H A hAn (η/4) hH.le
  have hJa := absolute_from_relative J D hDn (η/4) hJ.le
  rw [norm_div] at hV'
  have hVa := (div_le_iff₀ (norm_pos_iff.mpr hAn)).mp hV'
  have hpair := flow_actual_branch_pair t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz
  change RiemannEvenFlow.flow 3 t z=(H+conj J+Complex.I*V)/2 at hpair
  have hid : RiemannEvenFlow.flow 3 t z-(A+conj D)/2=((H-A)+conj (J-D)+Complex.I*V)/2 := by
    rw [hpair,map_sub]
    ring
  change ‖RiemannEvenFlow.flow 3 t z-(A+conj D)/2‖ ≤ η*(‖A‖+‖D‖)
  rw [hid,norm_div,Complex.norm_ofNat]
  have h1 := norm_add_le (H-A) (conj (J-D))
  have h2 := norm_add_le ((H-A)+conj (J-D)) (Complex.I*V)
  simp only [norm_conj,norm_mul,Complex.norm_I,one_mul] at h1 h2
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith [norm_nonneg A,norm_nonneg D]

set_option maxHeartbeats 800000 in
theorem eventually_actual_complex_pair_error (M η : ℝ) (hM : 0 ≤ M) (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, 65536*(M+7) ≤ u ∧ RiemannEvenRealSaddle.phaseSlope 3 t u=0 ∧
      ∀ x : ℝ, |x| ≤ M*RiemannQuarticTransitionSaddle.realScale u →
        ∃ (w : ℂ) (b : ℂ → ℂ), ‖w-(u : ℂ)‖ ≤ M+7 ∧
          ∀ z : ℂ, ‖z-(x : ℂ)‖ ≤ 1/(2048*(M+8)) →
            AnalyticAt ℂ b z ∧ complexSlope 3 t (b z)= -(Complex.I*z) ∧
            AnalyticAt ℂ (fun y => (modelGaussianAmplitude t y (b y)+
              conj (modelGaussianAmplitude t (conj y) (b (conj y))))/2) z ∧
            modelGaussianAmplitude t z (b z) ≠ 0 ∧
            modelGaussianAmplitude t (conj z) (b (conj z)) ≠ 0 ∧
            ‖RiemannEvenFlow.flow 3 t z-(modelGaussianAmplitude t z (b z)+
              conj (modelGaussianAmplitude t (conj z) (b (conj z))))/2‖ ≤
              η*(‖modelGaussianAmplitude t z (b z)‖+‖modelGaussianAmplitude t (conj z) (b (conj z))‖) := by
  let C := 1024*(M+8)
  have hC0 : 0 < C := by dsimp [C]; positivity
  obtain ⟨U,hU⟩ := eventually_atTop.1 (eventually_uniform_complex_pair_error C η hC0 hη)
  filter_upwards [RiemannSixthTransitionCorrection.eventually_exists_actual_transition_family M hM,
    eventually_ge_atTop (max U 1)] with t hfamily htU
  obtain ⟨u,hu,hstationary,_⟩ := hfamily
  have ht : 1 ≤ t := (le_max_right U 1).trans htU
  refine ⟨u,hu,hstationary,?_⟩
  intro x hx
  let K := (M+8)*RiemannQuarticTransitionSaddle.realScale u
  let C := 1024*(M+8)
  let r := 1/C
  have hC : 0 < C := by dsimp [C]; positivity
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hxnorm : ‖(x : ℂ)‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u := by simpa using hx
  obtain ⟨w,hw,_⟩ := RiemannSixthTransitionSaddle.existsUnique_transition_model_saddle
    t u M (x : ℂ) ht hM hu hstationary (by simp) hxnorm
  have hg := RiemannSixthTransitionSaddle.transition_model_geometry t u M (x : ℂ) w
    ht hM hu hstationary (by simp) hxnorm hw.1 hw.2
  have hd := transition_scale_data t u M (x : ℂ) w ht hM hu hstationary (by simp) hxnorm hw.1 hw.2
  have hK : 8 ≤ K := hd.1
  have hnorm := hd.2.2.2.1
  have hE := hd.2.2.2.2.1
  have hsmall := hd.2.2.2.2.2.1
  have hmargin := hd.2.2.2.2.2.2
  have hcoord := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hg.1
  simp only [Complex.sub_re,Complex.ofReal_re] at hcoord
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hcoord).1]
  have hscale : K ≤ C*(t*w.re^5) :=
    RiemannSixthTransitionAnalyticBranch.moving_scale_ratio_bound t u M w ht hM hu hstationary hg.1
  have hradius : r ≤ t*w.re^5/K := by
    apply (le_div_iff₀ (by linarith : 0 < K)).mpr
    dsimp [r]
    have hh : K/C ≤ t*w.re^5 := (div_le_iff₀ hC).mpr (by nlinarith)
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  let b := branch t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hradius
  have hQ1 : 1 ≤ t*w.re^5 := by
    have hp : 1 ≤ w.re^5 := one_le_pow₀ (by linarith : 1 ≤ w.re)
    nlinarith
  have hr1 : r ≤ 1 := (div_le_iff₀ hC).mpr (by dsimp [C]; nlinarith)
  have hXK : |x| ≤ K := by
    dsimp [K]
    have hb := RiemannQuarticTransitionSaddle.realScale_pos u
    nlinarith
  have hKr : K*r ≤ t*w.re^5 := by
    have h := (le_div_iff₀ (by linarith : 0 < K)).mp hradius
    nlinarith
  have hfreq : (|x|+r)*r ≤ 2*(t*w.re^5) := by
    have hm := mul_le_mul_of_nonneg_right hXK hrpos.le
    have hr2 : r*r ≤ 1 := by nlinarith
    nlinarith
  have hQ : U ≤ t*w.re^5 := by
    have hp : 1 ≤ w.re^5 := one_le_pow₀ (by linarith : 1 ≤ w.re)
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ t by linarith)
    linarith [(le_max_left U 1).trans htU]
  have he := hU (t*w.re^5) hQ t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall
    hrpos hradius hr1 hfreq rfl hscale
  refine ⟨w,b,hg.1,?_⟩
  intro z hz
  have hzlt : ‖z-(x : ℂ)‖ < r := by
    have hpos : 0 < M+8 := by positivity
    dsimp [r,C]
    have hhalf : 1/(2048*(M+8)) < 1/(1024*(M+8)) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    exact hz.trans_lt hhalf
  have hzc := conjugate_disk x r z hzlt.le
  have hspec := branch_spec t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hzlt.le
  have hA := mul_ne_zero
    (actual_weight_ne_zero t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hzlt.le)
    (gaussian_ne_zero t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hzlt.le)
  have hD := mul_ne_zero
    (actual_weight_ne_zero t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius (conj z) hzc)
    (gaussian_ne_zero t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius (conj z) hzc)
  exact ⟨branch_analyticAt t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hzlt,
    hspec.2,paired_amplitude_analyticAt t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hzlt,
    hA,hD,he z hzlt.le⟩

end OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionComplexPairing
