import Foundation.RiemannQuarticTransitionContour
/-! Complete positive horizontal saddle asymptotics at bounded transition ratios.
The existing signed compact-contour bounds supplement the actual outer tails.
The opposite-frequency pair and global zero control remain separate. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionCompact
open RiemannQuarticTransitionCorrection RiemannQuarticTransitionGaussian RiemannQuarticTransitionContour
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch
open RiemannQuarticFarModelSaddle RiemannThetaComplexKernel RiemannQuarticErrorLimits
section Scaled
variable (t K : ℝ) (c₀ w v : ℂ)
  (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hn : ‖w‖ ≤ 2*w.re) (hcenter : c₀.im ≤ 1)
  (hs : modelDerivative t w= -(Complex.I*c₀)) (hE : ‖Complex.exp (4*w)‖ ≤ K)
  (hv : ‖v-w‖ ≤ 1/K)
include ht hK hr hi hn hcenter hs hE hv

theorem corrected_geometry : 64 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ kernelComplex v ≠ 0 := by
  have hd := RiemannQuarticTransitionGaussian.horizontal_neighbor_domain t K c₀ w v
    ht hK (by linarith) hi hn hcenter hs hE hv 0 (by norm_num)
  simp only [Complex.ofReal_zero, add_zero] at hd
  have hdist : ‖v-w‖ ≤ 1/2 := hv.trans ((div_le_iff₀ (by linarith : 0 < K)).mpr (by linarith))
  have hre := (Complex.abs_re_le_norm (v-w)).trans hdist
  have him := (Complex.abs_im_le_norm (v-w)).trans hdist
  simp only [Complex.sub_re, Complex.sub_im] at hre him
  have hiv : |v.im| ≤ 1 := by
    rcases abs_le.mp hi with ⟨hi1,hi2⟩
    rcases abs_le.mp him with ⟨hv1,hv2⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hpos : 0 < Real.cos (4*v.im) := by
    have he : (Complex.exp (4*v)).re=Real.exp (4*v.re)*Real.cos (4*v.im) := by
      simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
    have hp : 0 < (Complex.exp (4*v)).re := by linarith [hd.2.1]
    rw [he] at hp
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hp
  have hlt : |4*v.im| < Real.pi/2 := by
    by_contra h
    have hh := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt h)
      (by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; linarith [Real.pi_gt_three] :
        |4*v.im| ≤ Real.pi+Real.pi/2)
    rw [Real.cos_abs] at hh
    linarith
  refine ⟨by linarith [(abs_le.mp hre).1], ?_, kernel_ne_zero v hd.1 hd.2.1⟩
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hlt
  linarith

theorem actual_compact_bound (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hy : z.im ≤ 1) :
    ‖∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)‖ ≤
      528*(v.re-1)*‖saddleWeight t z v‖*Real.exp (5*v.re+3-2*t*v.re^3) := by
  have hg := corrected_geometry t K c₀ w v ht hK hr hi hn hcenter hs hE hv
  have hd := RiemannQuarticTransitionGaussian.horizontal_neighbor_domain t K c₀ w v
    ht hK (by linarith) hi hn hcenter hs hE hv 0 (by norm_num)
  simp only [Complex.ofReal_zero, add_zero] at hd
  have hh : |v.im| ≤ 1 := hg.2.1.le.trans (by linarith [Real.pi_lt_four])
  have herr : ‖complexSlope t v-modelDerivative t v‖ ≤ 1 := by
    have he := RiemannQuarticTransitionGaussian.horizontal_neighbor_error t K c₀ w v
      ht hK (by linarith) hi hn hcenter hs hE hv 0 (by norm_num)
    simp only [Complex.ofReal_zero, add_zero] at he
    have hb := RiemannQuarticFarCorrection.small_error_at_large_real_part w.re hr
    have hExp := Real.exp_le_exp.mpr (show -4*w.re+4 ≤ -w.re by linarith)
    nlinarith
  have hupper := RiemannQuarticComplexCompactTail.actual_center_theta_upper t (by linarith) z v hd.1 hz herr
  have hvext : (v.re : ℂ)+(v.im : ℂ)*Complex.I=v := Complex.re_add_im v
  have ha1 : 0 ≤ v.re-1 := by linarith [hg.1]
  by_cases hlow : z.im ≤ 0
  · have h := RiemannQuarticComplexCompactTail.actual_left_compact_bound t ht z v.re v.im
      hg.1 hh hlow (by simpa only [hvext] using hd.2.1) (by simpa only [hvext] using hupper)
    rw [hvext] at h
    apply h.trans
    have he := Real.exp_le_exp.mpr (show 5*v.re+3-2*t*v.re^3+3*z.im/4 ≤ 5*v.re+3-2*t*v.re^3 by linarith)
    exact mul_le_mul_of_nonneg_left he (by positivity)
  · have habs : |z.im| ≤ 1 := by rw [abs_of_nonneg (by linarith : 0 ≤ z.im)]; exact hy
    have hupp : Real.pi*(Complex.exp (4*v)).re ≤ t*v.re^3+3 := by linarith
    have h := RiemannQuarticFarLeftCompact.actual_left_compact_bound t ht z v.re v.im hg.1 hh habs
      (by simpa only [hvext] using hd.2.1) (by simpa only [hvext] using hupp)
    simpa only [hvext] using h

theorem relative_compact_bound (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hy : z.im ≤ 1) :
    ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      4224*Real.sqrt K*(t*w.re^3)*Real.exp (-(t*w.re^3)/8) := by
  have h := actual_compact_bound t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hz hy
  have hg := corrected_geometry t K c₀ w v ht hK hr hi hn hcenter hs hE hv
  have hd : ‖v-w‖ ≤ 1/2 := hv.trans ((div_le_iff₀ (by linarith : 0 < K)).mpr (by linarith))
  have hc := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hc
  have hva : w.re ≤ 2*v.re := by linarith [(abs_le.mp hc).1]
  have hcube := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ w.re) hva 3)
    (show 0 ≤ t by linarith)
  have hpoly : 5*v.re+3 ≤ v.re^3 := by
    have hsq : 4096 ≤ v.re^2 := by nlinarith [hg.1]
    have hcu := mul_le_mul_of_nonneg_right hsq (by linarith [hg.1] : 0 ≤ v.re)
    nlinarith [hg.1]
  have htime : v.re^3 ≤ t*v.re^3 := by nlinarith [pow_nonneg (by linarith [hg.1] : 0 ≤ v.re) 3]
  have hexp : 5*v.re+3-2*t*v.re^3 ≤ -(t*w.re^3)/8 := by nlinarith
  have hQ : v.re-1 ≤ t*w.re^3 := by
    have hh : w.re ≤ w.re^3 := by
      have hsq : 1 ≤ w.re^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)]
    have htcu : w.re^3 ≤ t*w.re^3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 3]
    linarith [(abs_le.mp hc).2]
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let L := ∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  let B := 528*(t*w.re^3)*Real.exp (-(t*w.re^3)/8)
  have hnum : ‖L‖ ≤ ‖W‖*B := by
    apply h.trans
    have hm := mul_le_mul hQ (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
      (show 0 ≤ t*w.re^3 by positivity)
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 528*‖W‖ by positivity)
    dsimp [L,W,B] at *
    nlinarith
  have hnormal := gaussian_normalization_lower t K c₀ w v ht hK (by linarith) hi hn hcenter hs hE hv
  change 1 ≤ 8*Real.sqrt K*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hg.2.2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  change ‖L/(W*G)‖ ≤ _
  rw [norm_div, norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  dsimp [B] at *
  nlinarith

theorem horizontal_integrable (z : ℂ) :
    IntegrableOn (fun s : ℝ => saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)) (Ioi 0) :=
  RiemannQuarticNaturalContour.shifted_weight_integrable t z v.im
    (corrected_geometry t K c₀ w v ht hK hr hi hn hcenter hs hE hv).2.1

theorem horizontal_compact_outer_identity (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) :
    (∫ s : ℝ in Ioi 0, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))=
      (∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))+
      (∫ s : ℝ in Ioi (-1), saddleWeight t z (v+(s : ℂ))) := by
  have h := RiemannQuarticFarHalfline.horizontal_decomposition t z v
    (corrected_geometry t K c₀ w v ht hK hr hi hn hcenter hs hE hv).2.1 (-1)
    (actual_outer_integrable t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hz)
  simp only [neg_neg] at h
  have hrev : (∫ s : ℝ in (1 : ℝ)..(-1), saddleWeight t z (v+(s : ℂ)))=
      -(∫ s : ℝ in (-1 : ℝ)..1, saddleWeight t z (v+(s : ℂ))) :=
    intervalIntegral.integral_symm (-1) 1
  linear_combination h+hrev

end Scaled

theorem compact_budget_tendsto_zero (C : ℝ) :
    Tendsto (fun Q : ℝ => 4224*Real.sqrt C*Q^2*Real.exp (-Q/8)) atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) (1/8) (by norm_num)).const_mul
    (4224*Real.sqrt C)
  convert h using 1
  · ext Q
    rw [Real.rpow_two, show -(1/8 : ℝ)*Q= -Q/8 by ring]
    ring
  · ring

theorem eventually_uniform_horizontal_error (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in atTop, ∀ (t K : ℝ) (c₀ w v z : ℂ),
      1 ≤ t → 8 ≤ K → 120020 ≤ w.re → |w.im| ≤ 1/2 → ‖w‖ ≤ 2*w.re → c₀.im ≤ 1 →
      modelDerivative t w= -(Complex.I*c₀) → ‖Complex.exp (4*w)‖ ≤ K → ‖v-w‖ ≤ 1/K →
      complexSlope t v= -(Complex.I*z) → z.im ≤ 1 → Q=t*w.re^3 → K ≤ C*Q →
      ‖(∫ s : ℝ in Ioi 0, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ < ε := by
  filter_upwards [eventually_uniform_relative_outer_error C (ε/2) hC (half_pos hε),
    eventually_ge_atTop (1 : ℝ),
    (compact_budget_tendsto_zero C).eventually (gt_mem_nhds (half_pos hε))]
    with Q houter hQ hbudget
  intro t K c₀ w v z ht hK hr hi hn hcenter hs hE hv hstat hy hQid hratio
  have ho := houter t K c₀ w v z ht hK hr hi hn hcenter hs hE hv hstat hQid hratio
  have hc := relative_compact_bound t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hstat hy
  rw [← hQid] at hc
  have hroot : Real.sqrt K ≤ Real.sqrt C*Q := by
    have hh : Real.sqrt Q ≤ Q := by nlinarith [Real.sq_sqrt (show 0 ≤ Q by linarith), Real.sqrt_nonneg Q]
    have hmul := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg C)
    have hrK := Real.sqrt_le_sqrt hratio
    rw [Real.sqrt_mul hC.le] at hrK
    linarith
  have hmul := mul_le_mul_of_nonneg_right hroot (show 0 ≤ 4224*Q*Real.exp (-Q/8) by positivity)
  have hcomp :
      ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ < ε/2 := by
    nlinarith
  have hsplit := horizontal_compact_outer_identity t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hstat
  let D := saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))
  let H := ∫ s : ℝ in Ioi 0, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  let L := ∫ s : ℝ in Ioi (-1), saddleWeight t z (v+(s : ℂ))
  let B := ∫ s : ℝ in 0..v.re-1, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  have hid : H/D-1=(L/D-1)+B/D := by
    change H=B+L at hsplit
    rw [hsplit, add_div]
    ring
  change ‖H/D-1‖ < ε
  rw [hid]
  have htri := norm_add_le (L/D-1) (B/D)
  change ‖L/D-1‖ < ε/2 at ho
  change ‖B/D‖ < ε/2 at hcomp
  linarith

theorem eventually_actual_horizontal_error (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, 65536*(M+7) ≤ u ∧ RiemannQuarticSaddleTimes.phaseSlope t u=0 ∧
      ∀ z : ℂ, z.im ≤ 1 → ‖z‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u →
        ∃ w v : ℂ, w ∈ closedBall (RiemannQuarticTransitionSaddle.movingAnchor u z) (1/1024) ∧
          modelDerivative t w= -(Complex.I*z) ∧
          ‖v-w‖ ≤ 1/((M+8)*RiemannQuarticTransitionSaddle.realScale u) ∧
          complexSlope t v= -(Complex.I*z) ∧ |v.im| < Real.pi/8 ∧
          IntegrableOn (fun s : ℝ => saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)) (Ioi 0) ∧
          ‖(∫ s : ℝ in Ioi 0, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
            (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))-1‖ < ε := by
  let C := 128*(M+8)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨U,hU⟩ := eventually_atTop.1 (eventually_uniform_horizontal_error C ε hC hε)
  filter_upwards [RiemannQuarticTransitionSaddle.eventually_exists_transition_family M hM,
    eventually_ge_atTop (max U 1)] with t hmodels htU
  obtain ⟨u,hu,hs,hmodel⟩ := hmodels
  have ht : 1 ≤ t := (le_max_right U 1).trans htU
  refine ⟨u,hu,hs,?_⟩
  intro z hy hz
  obtain ⟨w,hw,_⟩ := hmodel z hy hz
  have hd := transition_scale_data t u M z w ht hM hu hs hy hz hw.1 hw.2
  let K := (M+8)*RiemannQuarticTransitionSaddle.realScale u
  have hK0 : 0 < K := by
    change 0 < (M+8)*RiemannQuarticTransitionSaddle.realScale u
    positivity [RiemannQuarticTransitionSaddle.realScale_pos u]
  have hwpos : 0 < w.re := by linarith [hd.2.1]
  obtain ⟨v,hv,_⟩ := actual_scaled_frequency_disk t K z w z ht hd.1 hd.2.1 hd.2.2.1
    hd.2.2.2.1 hy hw.2 hd.2.2.2.2.1 hd.2.2.2.2.2 (by simp; positivity)
  have hvdist : ‖v-w‖ ≤ 1/K := by simpa only [mem_closedBall, dist_eq_norm] using hv.1
  have hg := RiemannQuarticTransitionSaddle.transition_model_geometry t u M z w ht hM hu hs hy hz hw.1 hw.2
  have hratio : K ≤ C*(t*w.re^3) := moving_scale_ratio_bound t u M w ht hM hu hs hg.1
  have hcoord := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hg.1
  simp only [Complex.sub_re, Complex.ofReal_re] at hcoord
  have hlarge : 120020 ≤ w.re := by linarith [(abs_le.mp hcoord).1]
  have hQ : U ≤ t*w.re^3 := by
    have hp : 1 ≤ w.re^3 := one_le_pow₀ (by linarith : 1 ≤ w.re)
    have hh := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ t)
    linarith [(le_max_left U 1).trans htU]
  have he := hU (t*w.re^3) hQ t K z w v z ht hd.1 hlarge hd.2.2.1 hd.2.2.2.1
    hy hw.2 hd.2.2.2.2.1 hvdist hv.2 hy rfl hratio
  have hgeo := corrected_geometry t K z w v ht hd.1 hlarge hd.2.2.1 hd.2.2.2.1 hy hw.2 hd.2.2.2.2.1 hvdist
  have hint := horizontal_integrable t K z w v ht hd.1 hlarge hd.2.2.1 hd.2.2.2.1 hy hw.2 hd.2.2.2.2.1 hvdist z
  exact ⟨w,v,hw.1,hw.2,hvdist,hv.2,hgeo.2.1,hint,he⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionCompact
