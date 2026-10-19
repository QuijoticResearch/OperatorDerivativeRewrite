import Foundation.RiemannQuarticErrorLimits
/-! Uniform actual positive-half-line saddle asymptotics on an explicit region.
The verified error-limit envelopes and actual saddle growth give a relative
error tending to zero uniformly over all global amplitude maxima and nearby
branch saddles. The unshifted integral includes every endpoint and tail term.
Frequency disk, quadrant, norm(z)<=t and phase-region inequalities stay explicit.
No automatic power-window inclusion, opposite-frequency/cosine pairing,
zero-count theorem or unbounded frequency far-field control is asserted. -/
noncomputable section
open Set Metric Complex Filter MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticUniformSaddle
open RiemannQuarticErrorLimits RiemannQuarticHalflineApproximation RiemannQuarticSaddleGrowth
open RiemannQuarticSaddleTimes RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch
open RiemannQuarticDomain RiemannQuarticKernel RiemannQuarticRealSaddle

def relativeBudget (t Q a R : ℝ) : ℝ :=
  40*Real.sqrt Q*((5676/kernel 3)*Real.exp (10-503*t/8)+
    horizontalBudget Q a (centralRadius Q) R+(5676/(16*kernel 1))*Real.exp (1-3*t/8))

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
  have hBpos : 0 ≤ C*Real.exp (10-503*t/8)+D*Real.exp (1-3*t/8) := by positivity
  have htimeBound := mul_le_mul_of_nonneg_right hroot hBpos
  change relativeBudget t Q w.re R < ε
  dsimp [relativeBudget]
  change 80*t*(C*Real.exp (10-503*t/8)+D*Real.exp (1-3*t/8)) < ε/2 at hTime
  have hEnvQ := hconditions.2
  change 40*Real.sqrt Q*horizontalBudget Q (Q+1) (centralRadius Q) R < ε/2 at hEnvQ
  change 40*Real.sqrt Q*(C*Real.exp (10-503*t/8)+horizontalBudget Q w.re (centralRadius Q) R+
    D*Real.exp (1-3*t/8)) < ε
  nlinarith

theorem uniform_unshifted_relative_error (R : ℝ) (hR : 0 < R) (hRcap : R ≤ 1/819200)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (ht : 0 < t) (u : ℝ) (hu : 2 ≤ u),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → ∀ (hs : phaseSlope t u=0) (z : ℂ),
      ‖z‖ < (t*u^3+1)/51200 → 0 ≤ z.re → z.im ≤ 0 → ‖z‖ ≤ t →
      (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1 → ‖z‖^2 ≤ t*(t*u^3+1) →
      let w := branch t u ht.le (le_trans (by norm_num : (1 : ℝ)≤2) hu) hs z
      ‖(∫ x : ℝ in Ioi 0, saddleWeight t z (x : ℂ))/
        (saddleWeight t z w*((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ))-1‖ < ε := by
  filter_upwards [eventually_uniform_budget R hR ε hε] with t htBudget
  intro ht u hu hm hs z hz hre hy hzt hphase hregion
  let hu1 : 1 ≤ u := le_trans (by norm_num : (1 : ℝ)≤2) hu
  let w := branch t u ht.le hu1 hs z
  have hspec := branch_spec t u ht.le hu1 hs z hz.le
  have hb := (htBudget u (by change 0 ≤ u; linarith) hm).2 w hspec.1
  have he := unshifted_branch_relative_error t u ht hu hm hs z hz hre hy hzt hphase hregion
    (centralRadius (t*u^3+1)) R hb.1 hb.2.1 hRcap hb.2.2.1
  exact he.trans_lt hb.2.2.2

end OperatorDerivativeRewrite.Foundation.RiemannQuarticUniformSaddle
