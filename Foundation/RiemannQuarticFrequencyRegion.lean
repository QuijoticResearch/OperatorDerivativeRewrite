import Foundation.RiemannQuarticPairedSaddle
/-! Automatic frequency-domain inclusion for actual paired saddles.
Actual maxima satisfy u^12<=t eventually. Cubic phase control then forces
norm(z)*u<=t/8, the inverse disk, norm(z)<=t and the remaining region bound.
Thus the actual two-saddle flow estimate needs only its cubic phase condition.
For every gamma<2/3 it holds uniformly on norm(z)<=Q^gamma, Q=t*u^3+1.
This approximates actual saddle contributions, not a common real-center cosine
profile; zero counts and unrestricted frequency far field remain unproved. -/
noncomputable section
open Set Metric Complex Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFrequencyRegion
open RiemannQuarticSaddleGrowth RiemannQuarticRealSaddle RiemannQuarticDomain

theorem scaled_frequency_power (t u s : ℝ) (ht : 1 ≤ t) (hu : 1 ≤ u) (hs : 0 ≤ s)
    (hu12 : u^12 ≤ t) (hs3 : s^3 ≤ (t*u^3+1)^2) : (s*u)^12 ≤ 256*t^11 := by
  have hu3 : 1 ≤ u^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sq_nonneg u)]
  have htu : 1 ≤ t*u^3 := by nlinarith
  have hQ : 0 ≤ t*u^3+1 := by positivity
  have hQupper : t*u^3+1 ≤ 2*t*u^3 := by linarith
  have hspow : s^12 ≤ (t*u^3+1)^8 := by
    have h := pow_le_pow_left₀ (pow_nonneg hs 3) hs3 4
    simpa only [← pow_mul,Nat.reduceMul] using h
  have hQpow := pow_le_pow_left₀ hQ hQupper 8
  have hupow : u^36 ≤ t^3 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ u^12) hu12 3
    simpa only [← pow_mul,Nat.reduceMul] using h
  calc
    _ = s^12*u^12 := mul_pow s u 12
    _ ≤ (t*u^3+1)^8*u^12 := mul_le_mul_of_nonneg_right hspow (by positivity)
    _ ≤ (2*t*u^3)^8*u^12 := mul_le_mul_of_nonneg_right hQpow (by positivity)
    _ = 256*t^8*u^36 := by ring
    _ ≤ 256*t^8*t^3 := mul_le_mul_of_nonneg_left hupow (by positivity)
    _ = _ := by ring

theorem frequency_linear_budget (t u s : ℝ) (ht : (256*8^12 : ℝ) ≤ t) (hu : 1 ≤ u) (hs : 0 ≤ s)
    (hu12 : u^12 ≤ t) (hs3 : s^3 ≤ (t*u^3+1)^2) : s*u ≤ t/8 := by
  have ht1 : 1 ≤ t := by norm_num at ht ⊢; linarith
  have hpow := scaled_frequency_power t u s ht1 hu hs hu12 hs3
  by_contra hn
  have hx : t/8 < s*u := lt_of_not_ge hn
  have hp := pow_lt_pow_left₀ hx (by positivity : (0 : ℝ) ≤ t/8) (by decide : (12 : ℕ) ≠ 0)
  rw [div_pow] at hp
  have hpl : t^12 < (8 : ℝ)^12*(s*u)^12 := by
    have h := (div_lt_iff₀ (by positivity : (0 : ℝ)<8^12)).mp hp
    nlinarith
  have hupper := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 8^12)
  have hmul := mul_le_mul_of_nonneg_right ht (by positivity : (0 : ℝ) ≤ t^11)
  have hind : (8 : ℝ)^12*(256*t^11) ≤ t^12 := by convert hmul using 1 <;> ring
  exact (not_lt_of_ge hind) (hpl.trans_le hupper)

theorem cubic_frequency_domains (t u s : ℝ) (ht : (256*8^12 : ℝ) ≤ t) (hu : 16 ≤ u) (hs : 0 ≤ s)
    (hu12 : u^12 ≤ t) (hs3 : s^3 ≤ (t*u^3+1)^2) :
    s < (t*u^3+1)/51200 ∧ s*u ≤ t/8 ∧ s ≤ t ∧ s^2 ≤ t*(t*u^3+1) := by
  have ht1 : 1 ≤ t := by norm_num at ht ⊢; linarith
  have hu1 : 1 ≤ u := by linarith
  have hlinear := frequency_linear_budget t u s ht hu1 hs hu12 hs3
  have hu3 : 1 ≤ u^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sq_nonneg u)]
  have hQt : t ≤ t*u^3+1 := by nlinarith
  have hst : s ≤ t := by nlinarith [mul_nonneg hs (sub_nonneg.mpr hu1)]
  refine ⟨?_,hlinear,hst,?_⟩
  · by_contra hn
    have hx : (t*u^3+1)/51200 ≤ s := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hx (by linarith : 0 ≤ u)
    have hu4 : (65536 : ℝ) ≤ u^4 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hu 4
      norm_num at h
      exact h
    have hmul := mul_le_mul_of_nonneg_left hu4 (by linarith : 0 ≤ t)
    nlinarith
  · have hsq := (sq_le_sq₀ hs (by linarith : 0 ≤ t)).mpr hst
    have hm := mul_le_mul_of_nonneg_left hQt (by linarith : 0 ≤ t)
    nlinarith

theorem eventually_cubic_frequency_domains :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ), IsMaxOn (weighted 0 t 0) (Ici 0) u →
      16 ≤ u ∧ ∀ z : ℂ, (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1 →
        ‖z‖ < (t*u^3+1)/51200 ∧ u*|z.im| ≤ t/8 ∧ ‖z‖ ≤ t ∧ ‖z‖^2 ≤ t*(t*u^3+1) := by
  filter_upwards [eventually_all_maxima_power_bound 12,maxima_escape 16 (by norm_num),
    eventually_ge_atTop (256*8^12 : ℝ)] with t hpow hEscape ht
  intro u hu hm
  have hu16 : 16 ≤ u := (hEscape u hu hm).le
  refine ⟨hu16,?_⟩
  intro z hphase
  have ht1 : 1 ≤ t := by norm_num at ht ⊢; linarith
  have hQ : 0 < t*u^3+1 := by positivity
  have hs3 : ‖z‖^3 ≤ (t*u^3+1)^2 := by
    have hb : 25600*‖z‖^3 ≤ (t*u^3+1)^2 := by
      have hd : (25600*‖z‖^3)/(t*u^3+1)^2 ≤ 1 := by
        simpa only [div_mul_eq_mul_div] using hphase
      simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos hQ)).mp hd
    nlinarith [pow_nonneg (norm_nonneg z) 3]
  have hd := cubic_frequency_domains t u ‖z‖ ht hu16 (norm_nonneg z) (hpow u hu hm) hs3
  refine ⟨hd.1,?_,hd.2.2.1,hd.2.2.2⟩
  have hi := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) (by linarith : 0 ≤ u)
  nlinarith [hd.2.1]

theorem uniform_cubic_phase_pair (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (ht : 0 < t) (u : ℝ) (hu : 2 ≤ u),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → ∀ (hs : RiemannQuarticSaddleTimes.phaseSlope t u=0) (z : ℂ),
      (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1 →
      let hu1 := le_trans (by norm_num : (1 : ℝ)≤2) hu
      let Pp := RiemannQuarticPairedSaddle.approxContribution t u ht.le hu1 hs z
      let Pm := RiemannQuarticPairedSaddle.approxContribution t u ht.le hu1 hs (-z)
      ‖RiemannQuarticFlow.flow t z-(Pp+Pm)/2‖ ≤ ε*(‖Pp‖+‖Pm‖)/2 := by
  filter_upwards [RiemannQuarticPairedSaddle.uniform_actual_two_saddle ε hε,
    eventually_cubic_frequency_domains] with t hpair hdomains
  intro ht u hu hm hs z hphase
  have hd := (hdomains u (by change 0 ≤ u; linarith) hm).2 z hphase
  exact hpair ht u hu hm hs z hd.1 hd.2.1 hd.2.2.1 hphase hd.2.2.2

theorem cubic_phase_power_window (γ : ℝ) (hγ : γ < 2/3) :
    ∀ᶠ Q : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ Q^γ → (25600/Q^2)*‖z‖^3 ≤ 1 := by
  have hpos : 0 < 2-3*γ := by linarith
  have hlim : Tendsto (fun Q : ℝ => 25600*Q^(3*γ-2)) atTop (nhds 0) := by
    rw [show 3*γ-2= -(2-3*γ) by ring]
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hpos).const_mul 25600
  filter_upwards [eventually_gt_atTop (0 : ℝ),hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))] with Q hQ hbound
  intro z hz
  have hp := pow_le_pow_left₀ (norm_nonneg z) hz 3
  have hpow : (Q^γ)^3=Q^(3*γ) := by
    calc
      _ = Q^(γ*(3 : ℝ)) := by rw [Real.rpow_mul hQ.le,Real.rpow_ofNat]
      _ = _ := by congr 1; ring
  have hden : Q^2=Q^(2 : ℝ) := (Real.rpow_natCast Q 2).symm
  calc
    _ ≤ (25600/Q^2)*(Q^γ)^3 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 25600*Q^(3*γ-2) := by rw [hpow,hden,Real.rpow_sub hQ]; ring
    _ ≤ 1 := hbound.le

theorem uniform_power_window_pair (γ : ℝ) (hγ : γ < 2/3) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (ht : 0 < t) (u : ℝ) (hu : 2 ≤ u),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → ∀ (hs : RiemannQuarticSaddleTimes.phaseSlope t u=0) (z : ℂ),
      ‖z‖ ≤ (t*u^3+1)^γ →
      let hu1 := le_trans (by norm_num : (1 : ℝ)≤2) hu
      let Pp := RiemannQuarticPairedSaddle.approxContribution t u ht.le hu1 hs z
      let Pm := RiemannQuarticPairedSaddle.approxContribution t u ht.le hu1 hs (-z)
      ‖RiemannQuarticFlow.flow t z-(Pp+Pm)/2‖ ≤ ε*(‖Pp‖+‖Pm‖)/2 := by
  obtain ⟨U,hU⟩ := eventually_atTop.1 (cubic_phase_power_window γ hγ)
  filter_upwards [uniform_cubic_phase_pair ε hε,eventually_ge_atTop U] with t hpair htU
  intro ht u hu hm hs z hz
  have hu1 : 1 ≤ u := by linarith
  have hu3 : 1 ≤ u^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sq_nonneg u)]
  have hQt : t ≤ t*u^3+1 := by nlinarith
  have hphase := hU (t*u^3+1) (le_trans htU hQt) z hz
  exact hpair ht u hu hm hs z hphase

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFrequencyRegion
