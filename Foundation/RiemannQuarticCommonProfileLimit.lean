import Foundation.RiemannQuarticCommonProfile
import Foundation.RiemannQuarticFrequencyRegion
/-! Uniform common-center channel comparison on growing complex disks. -/
noncomputable section
open Set Metric Complex Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCommonProfileLimit
open RiemannQuarticCommonProfile RiemannQuarticFrequencyRegion
open RiemannQuarticPairedSaddle RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes
open RiemannQuarticDomain RiemannQuarticSaddleGrowth

theorem power_window_relative_error (γ : ℝ) (hγ : γ < 2/3) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ Q^γ →
      ((51200/Q^2)*‖z‖^3)*(1+51200*‖z‖/Q)+51200*‖z‖/Q ≤ ε := by
  have hA : Tendsto (fun Q : ℝ => 51200*Q^(3*γ-2)) atTop (nhds 0) := by
    have hp : 0 < 2-3*γ := by linarith
    rw [show 3*γ-2= -(2-3*γ) by ring]
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hp).const_mul 51200
  have hB : Tendsto (fun Q : ℝ => 51200*Q^(γ-1)) atTop (nhds 0) := by
    have hp : 0 < 1-γ := by linarith
    rw [show γ-1= -(1-γ) by ring]
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hp).const_mul 51200
  have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hE := (hA.mul (hc.add hB)).add hB
  simp only [zero_mul,add_zero] at hE
  filter_upwards [eventually_gt_atTop (0 : ℝ),hE.eventually (gt_mem_nhds hε)] with Q hQ hbound
  intro z hz
  have ha : (51200/Q^2)*‖z‖^3 ≤ 51200*Q^(3*γ-2) := by
    have hp := pow_le_pow_left₀ (norm_nonneg z) hz 3
    have he : (Q^γ)^3=Q^(3*γ) := by
      rw [← Real.rpow_natCast (Q^γ) 3,← Real.rpow_mul hQ.le]
      congr 1
      ring
    calc
      _ ≤ (51200/Q^2)*(Q^γ)^3 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by rw [he,← Real.rpow_natCast Q 2,Real.rpow_sub hQ]; ring
  have hb : 51200*‖z‖/Q ≤ 51200*Q^(γ-1) := by
    calc
      _ ≤ 51200*Q^γ/Q := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz (by norm_num)) hQ.le
      _ = _ := by rw [Real.rpow_sub hQ,Real.rpow_one]; ring
  have hbpos : 0 ≤ 51200*Q^(γ-1) := by positivity
  have hprod := mul_le_mul ha (show 1+51200*‖z‖/Q ≤ 1+51200*Q^(γ-1) by linarith) (by positivity : 0 ≤ 1+51200*‖z‖/Q) (by positivity : 0 ≤ 51200*Q^(3*γ-2))
  exact (add_le_add hprod hb).trans hbound.le

theorem uniform_channel_comparison (γ : ℝ) (hγ : γ < 2/3) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (ht : 0 < t) (u : ℝ) (hu : 2 ≤ u),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → ∀ (hs : phaseSlope t u=0) (z : ℂ),
      ‖z‖ ≤ (t*u^3+1)^γ →
      let hu1 := le_trans (by norm_num : (1 : ℝ)≤2) hu
      ‖approxContribution t u ht.le hu1 hs z-centerContribution t u z‖ ≤
        ε*‖centerContribution t u z‖ := by
  obtain ⟨U,hU⟩ := eventually_atTop.1 ((power_window_relative_error γ hγ ε hε).and
    (cubic_phase_power_window γ hγ))
  filter_upwards [eventually_cubic_frequency_domains,eventually_ge_atTop U] with t hdomains htU
  intro ht u hu hm hs z hz
  have hu1 : 1 ≤ u := by linarith
  have hu3 : 1 ≤ u^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sq_nonneg u)]
  have hQt : t ≤ t*u^3+1 := by nlinarith
  have hb := hU (t*u^3+1) (le_trans htU hQt)
  have hp := hb.2 z hz
  have hd := (hdomains u (by change 0 ≤ u; linarith) hm).2 z hp
  have h := RiemannQuarticCommonProfile.actual_relative_center t u ht.le hu1 hs z hd.1 hp
  have herr := h.trans (hb.1 z hz)
  have hC := centerContribution_ne_zero t u ht.le hu1 hs z
  have hid : approxContribution t u ht.le hu1 hs z/centerContribution t u z-1=
      (approxContribution t u ht.le hu1 hs z-centerContribution t u z)/centerContribution t u z := by
    field_simp
  rw [hid,norm_div] at herr
  exact (div_le_iff₀ (norm_pos_iff.mpr hC)).mp herr

theorem paired_model_error (F P M C D : ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hF : ‖F-(P+M)/2‖ ≤ δ*(‖P‖+‖M‖)/2)
    (hP : ‖P-C‖ ≤ δ*‖C‖) (hM : ‖M-D‖ ≤ δ*‖D‖) :
    ‖F-(C+D)/2‖ ≤ δ*(2+δ)*(‖C‖+‖D‖)/2 := by
  have hnP : ‖P‖ ≤ (1+δ)*‖C‖ := by
    have h := norm_add_le (P-C) C
    simp only [sub_add_cancel] at h
    nlinarith
  have hnM : ‖M‖ ≤ (1+δ)*‖D‖ := by
    have h := norm_add_le (M-D) D
    simp only [sub_add_cancel] at h
    nlinarith
  have hCD : ‖(P+M)/2-(C+D)/2‖ ≤ δ*(‖C‖+‖D‖)/2 := by
    have he : (P+M)/2-(C+D)/2=((P-C)+(M-D))/2 := by ring
    rw [he,norm_div,Complex.norm_ofNat]
    have h := norm_add_le (P-C) (M-D)
    linarith
  have hsum : ‖P‖+‖M‖ ≤ (1+δ)*(‖C‖+‖D‖) := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsum hδ
  have htri := norm_add_le (F-(P+M)/2) ((P+M)/2-(C+D)/2)
  simp only [sub_add_sub_cancel] at htri
  nlinarith

theorem uniform_center_pair (γ : ℝ) (hγ : γ < 2/3) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (ht : 0 < t) (u : ℝ) (hu : 2 ≤ u),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → ∀ (hs : phaseSlope t u=0) (z : ℂ),
      ‖z‖ ≤ (t*u^3+1)^γ →
      ‖RiemannQuarticFlow.flow t z-(centerContribution t u z+centerContribution t u (-z))/2‖ ≤
        ε*(‖centerContribution t u z‖+‖centerContribution t u (-z)‖)/2 := by
  let δ := min 1 (ε/3)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε/3 := min_le_right _ _
  filter_upwards [uniform_channel_comparison γ hγ δ hδ,uniform_power_window_pair γ hγ δ hδ] with t hchannel hpair
  intro ht u hu hm hs z hz
  let hu1 : 1 ≤ u := by linarith
  have hP := hchannel ht u hu hm hs z hz
  have hM := hchannel ht u hu hm hs (-z) (by simpa using hz)
  have hF := hpair ht u hu hm hs z hz
  have h := paired_model_error _ _ _ _ _ δ hδ.le hF hP hM
  apply h.trans
  have hscalar : δ*(2+δ) ≤ ε := by nlinarith
  have hn : 0 ≤ ‖centerContribution t u z‖+‖centerContribution t u (-z)‖ := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hscalar hn]

theorem uniform_gaussian_cosine (γ : ℝ) (hγ : γ < 2/3) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (ht : 0 < t) (u : ℝ) (hu : 2 ≤ u),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → ∀ (hs : phaseSlope t u=0) (z : ℂ),
      ‖z‖ ≤ (t*u^3+1)^γ →
      ‖RiemannQuarticFlow.flow t z-
        RiemannQuarticFrequencyBranch.saddleWeight t 0 (u : ℂ)*
          RiemannQuarticGaussianPrefactor.gaussianFactor t (u : ℂ)*
          Complex.exp (z^2/(2*deriv (complexSlope t) (u : ℂ)))*Complex.cos ((u : ℂ)*z)‖ ≤
        ε*(‖centerContribution t u z‖+‖centerContribution t u (-z)‖)/2 := by
  filter_upwards [uniform_center_pair γ hγ ε hε] with t hpair
  intro ht u hu hm hs z hz
  simpa only [← center_pair_eq_cosine] using hpair ht u hu hm hs z hz

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCommonProfileLimit
