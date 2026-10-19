import Foundation.RiemannQuarticEvolution
import Foundation.RiemannQuarticSuppressedSaddle
import Foundation.RiemannQuarticErrorLimits
/-! Uniform actual two-channel saddle approximation of the quartic cosine flow.
Signed contours and controlled positive imaginary suppression allow both z
and -z. The actual jet0/half-line bridge handles Ici/Ioi endpoints exactly.
The error is small relative to the sum of the magnitudes of both nonzero
actual Gaussian saddle contributions. Their possibly vanishing sum is never
used as a denominator. Disk, phase, suppression and region conditions remain
explicit; a common real-center cosine profile and zero counts are unproved. -/
noncomputable section
open Set Metric Complex Filter MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticPairedSaddle
open RiemannQuarticErrorLimits RiemannQuarticHalflineApproximation RiemannQuarticSaddleGrowth
open RiemannQuarticSaddleTimes RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch
open RiemannQuarticDomain RiemannQuarticKernel RiemannQuarticRealSaddle
open RiemannQuarticSuppressedSaddle RiemannQuarticSaddleGeometry RiemannThetaComplexKernel

def relativeBudget (t Q a R : ℝ) : ℝ :=
  40*Real.sqrt Q*((5676/kernel 3)*Real.exp (10-251*t/4)+
    horizontalBudget Q a (centralRadius Q) R+(5676/(16*kernel 1))*Real.exp (1-t/4))

theorem time_endpoints_tendsto_zero (C D : ℝ) :
    Tendsto (fun t : ℝ => 80*t*(C*Real.exp (10-251*t/4)+D*Real.exp (1-t/4))) atTop (nhds 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (251/4) (by norm_num)
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (1/4) (by norm_num)
  simp only [Real.rpow_one] at h1 h2
  have hlim := (h1.const_mul (80*C*Real.exp 10)).add (h2.const_mul (80*D*Real.exp 1))
  simp only [mul_zero,add_zero] at hlim
  apply hlim.congr'
  filter_upwards with t
  rw [show 10-251*t/4=10+(-(251/4)*t) by ring,show 1-t/4=1+(-(1/4)*t) by ring,
    Real.exp_add,Real.exp_add]
  ring


theorem eventually_uniform_budget (R : ℝ) (hR : 0 < R) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ), IsMaxOn (weighted 0 t 0) (Ici 0) u →
      2 ≤ u ∧ ∀ w ∈ closedBall (u : ℂ) (1/102400),
        0 < centralRadius (t*u^3+1) ∧ centralRadius (t*u^3+1) ≤ R ∧
        204800*(t*u^3+1)*centralRadius (t*u^3+1)^3 ≤ 1 ∧
        relativeBudget t (t*u^3+1) w.re R < ε := by
  let C := 5676/kernel 3
  let D := 5676/(16*kernel 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity [kernel_pos 3 (by norm_num)]
  have hD : 0 ≤ D := by dsimp [D]; positivity [kernel_pos 1 (by norm_num)]
  have hEnv : Tendsto (fun Q : ℝ => 40*Real.sqrt Q*horizontalBudget Q (Q+1) (centralRadius Q) R) atTop (nhds 0) := by
    simpa only [mul_zero,mul_assoc] using (horizontal_envelope_tendsto_zero R hR).const_mul 40
  obtain ⟨U,hU⟩ := eventually_atTop.1 ((eventual_central_conditions R hR).and
    (hEnv.eventually (gt_mem_nhds (half_pos hε))))
  have hTime := (time_endpoints_tendsto_zero C D).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [eventually_all_maxima_power_bound 1,eventually_all_maxima_scale_power_bound 1,
    maxima_escape 2 (by norm_num),eventually_ge_atTop (max U 1),hTime] with t huPow hQPow hEscape ht hTime
  intro u hu hm
  have hu2 : 2 ≤ u := (hEscape u hu hm).le
  have ht1 : 1 ≤ t := le_trans (le_max_right U 1) ht
  have htu := huPow u hu hm
  simp only [pow_one] at htu
  have hu3 : 1 ≤ u^3 := by nlinarith [mul_nonneg (by linarith : 0 ≤ u-1) (sq_nonneg u)]
  let Q := t*u^3+1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hQt : t ≤ Q := by dsimp [Q]; nlinarith
  have hQupper := hQPow u hu hm
  simp only [pow_one,Nat.reduceAdd] at hQupper
  change Q ≤ 2*t^2 at hQupper
  have hroot : Real.sqrt Q ≤ 2*t := by nlinarith [Real.sq_sqrt hQ.le,Real.sqrt_nonneg Q]
  have hconditions := hU Q (le_trans (le_trans (le_max_left U 1) ht) hQt)
  refine ⟨hu2,?_⟩
  intro w hw
  refine ⟨hconditions.1.1,hconditions.1.2.1,hconditions.1.2.2,?_⟩
  have hdist : ‖w-(u : ℂ)‖ ≤ (1/102400 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hre := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hdist
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  have ha : w.re ≤ Q+1 := by linarith [(abs_le.mp hre).2]
  have hhorizontal := mul_le_mul_of_nonneg_left
    (horizontal_budget_le_envelope Q w.re (centralRadius Q) R ha) (by norm_num : (0 : ℝ) ≤ 40)
  have hBpos : 0 ≤ C*Real.exp (10-251*t/4)+D*Real.exp (1-t/4) := by positivity
  have htimeBound := mul_le_mul_of_nonneg_right hroot hBpos
  change relativeBudget t Q w.re R < ε
  dsimp [relativeBudget]
  change 80*t*(C*Real.exp (10-251*t/4)+D*Real.exp (1-t/4)) < ε/2 at hTime
  have hEnvQ := hconditions.2
  change 40*Real.sqrt Q*horizontalBudget Q (Q+1) (centralRadius Q) R < ε/2 at hEnvQ
  change 40*Real.sqrt Q*(C*Real.exp (10-251*t/4)+horizontalBudget Q w.re (centralRadius Q) R+
    D*Real.exp (1-t/4)) < ε
  nlinarith

theorem uniform_unshifted_relative_error (R : ℝ) (hR : 0 < R) (hRcap : R ≤ 1/819200)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (ht : 0 < t) (u : ℝ) (hu : 2 ≤ u),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → ∀ (hs : phaseSlope t u=0) (z : ℂ),
      ‖z‖ < (t*u^3+1)/51200 → u*z.im ≤ t/8 → ‖z‖ ≤ t →
      (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1 → ‖z‖^2 ≤ t*(t*u^3+1) →
      let w := branch t u ht.le (le_trans (by norm_num : (1 : ℝ)≤2) hu) hs z
      ‖(∫ x : ℝ in Ioi 0, saddleWeight t z (x : ℂ))/
        (saddleWeight t z w*((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ))-1‖ < ε := by
  filter_upwards [eventually_uniform_budget R hR ε hε] with t htBudget
  intro ht u hu hm hs z hz hlinear hzt hphase hregion
  let hu1 : 1 ≤ u := le_trans (by norm_num : (1 : ℝ)≤2) hu
  let w := branch t u ht.le hu1 hs z
  have hspec := branch_spec t u ht.le hu1 hs z hz.le
  have hb := (htBudget u (by change 0 ≤ u; linarith) hm).2 w hspec.1
  have he := suppressed_unshifted_relative_error t u ht hu hm hs z hz hlinear hzt hphase hregion
    (centralRadius (t*u^3+1)) R hb.1 hb.2.1 hRcap hb.2.2.1
  exact he.trans_lt hb.2.2.2

def approxContribution (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0) (z : ℂ) : ℂ :=
  let w := branch t u ht hu hs z
  saddleWeight t z w*((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)

theorem jet_zero_eq_halfline (t : ℝ) (z : ℂ) :
    RiemannQuarticFlow.jet 0 t z=∫ x : ℝ in Ioi 0, saddleWeight t z (x : ℂ) := by
  unfold RiemannQuarticFlow.jet RiemannQuarticFlow.halfLine
  rw [integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [RiemannQuarticFlow.integrand,weighted,pow_zero,one_mul,mul_one,zero_mul,add_zero,
    saddleWeight,kernelComplex_real,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_pow]
  rw [Complex.exp_add]
  have hphase : Complex.I*(x : ℂ)*z=Complex.I*z*(x : ℂ) := by ring
  rw [hphase]
  ring

theorem approxContribution_ne_zero (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ ≤ (t*u^3+1)/51200) : approxContribution t u ht hu hs z ≠ 0 := by
  let w := branch t u ht hu hs z
  have hw := (branch_spec t u ht hu hs z hz).1
  have hG : ((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ) ≠ 0 := by
    rw [← quadratic_gaussian_integral t u ht hu hs w hw]
    exact quadratic_gaussian_integral_ne_zero t u ht hu hs w hw
  exact mul_ne_zero (saddleWeight_ne_zero t u ht hu hs z hz) hG

theorem uniform_actual_two_saddle (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (ht : 0 < t) (u : ℝ) (hu : 2 ≤ u),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → ∀ (hs : phaseSlope t u=0) (z : ℂ),
      ‖z‖ < (t*u^3+1)/51200 → u*|z.im| ≤ t/8 → ‖z‖ ≤ t →
      (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1 → ‖z‖^2 ≤ t*(t*u^3+1) →
      let hu1 := le_trans (by norm_num : (1 : ℝ)≤2) hu
      let Pp := approxContribution t u ht.le hu1 hs z
      let Pm := approxContribution t u ht.le hu1 hs (-z)
      ‖RiemannQuarticFlow.flow t z-(Pp+Pm)/2‖ ≤ ε*(‖Pp‖+‖Pm‖)/2 := by
  filter_upwards [uniform_unshifted_relative_error (1/819200) (by norm_num) (by norm_num) ε hε] with t hbound
  intro ht u hu hm hs z hz hlinear hzt hphase hregion
  let hu1 : 1 ≤ u := le_trans (by norm_num : (1 : ℝ)≤2) hu
  let Pp := approxContribution t u ht.le hu1 hs z
  let Pm := approxContribution t u ht.le hu1 hs (-z)
  let Jp := ∫ x : ℝ in Ioi 0, saddleWeight t z (x : ℂ)
  let Jm := ∫ x : ℝ in Ioi 0, saddleWeight t (-z) (x : ℂ)
  have hu0 : 0 ≤ u := by linarith
  have hlinp : u*z.im ≤ t/8 := (mul_le_mul_of_nonneg_left (le_abs_self z.im) hu0).trans hlinear
  have hlinm : u*(-z).im ≤ t/8 := by
    simpa only [Complex.neg_im] using (mul_le_mul_of_nonneg_left (neg_le_abs z.im) hu0).trans hlinear
  have hp := hbound ht u hu hm hs z hz hlinp hzt hphase hregion
  have hn := hbound ht u hu hm hs (-z) (by simpa only [norm_neg] using hz) hlinm
    (by simpa only [norm_neg] using hzt) (by simpa only [norm_neg] using hphase)
    (by simpa only [norm_neg] using hregion)
  change ‖Jp/Pp-1‖ < ε at hp
  change ‖Jm/Pm-1‖ < ε at hn
  have error_of_relative (J P : ℂ) (hP : P ≠ 0) (h : ‖J/P-1‖ < ε) : ‖J-P‖ ≤ ε*‖P‖ := by
    have hid : (J/P-1)*P=J-P := by field_simp [hP]
    calc
      _ = ‖J/P-1‖*‖P‖ := by rw [← hid,norm_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right h.le (norm_nonneg _)
  have hpe := error_of_relative Jp Pp (approxContribution_ne_zero t u ht.le hu1 hs z hz.le) hp
  have hme := error_of_relative Jm Pm
    (approxContribution_ne_zero t u ht.le hu1 hs (-z) (by simpa only [norm_neg] using hz.le)) hn
  have hflow : RiemannQuarticFlow.flow t z=(Jp+Jm)/2 := by
    rw [RiemannQuarticFlow.flow,jet_zero_eq_halfline,jet_zero_eq_halfline]
  have hid : RiemannQuarticFlow.flow t z-(Pp+Pm)/2=((Jp-Pp)+(Jm-Pm))/2 := by rw [hflow]; ring
  change ‖RiemannQuarticFlow.flow t z-(Pp+Pm)/2‖ ≤ ε*(‖Pp‖+‖Pm‖)/2
  rw [hid,norm_div,Complex.norm_ofNat]
  calc
    _ ≤ (‖Jp-Pp‖+‖Jm-Pm‖)/2 := div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ (ε*‖Pp‖+ε*‖Pm‖)/2 := by gcongr
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticPairedSaddle
