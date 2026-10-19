import Foundation.RiemannQuarticCurvature
/-! Uniform sub-polynomial growth of actual quartic maximizing saddles.
For each natural n, every sufficiently large positive stationary center has
u^n<=t. Escape of all actual global maxima then makes this uniform over those
maxima at all sufficiently large times. In particular Q^n<=2^n*t^(n+1) for
Q=t*u^3+1. The cutoff may depend on n. These actual-kernel scale estimates
support joint error limits; they assert no zero-control theorem. -/
noncomputable section
open Set Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticSaddleGrowth
open RiemannQuarticCurvature RiemannQuarticSaddleTimes RiemannQuarticRealSaddle
open RiemannQuarticDomain RiemannQuarticKernel

theorem eventually_stationary_power_bound (n : ℕ) :
    ∀ᶠ u : ℝ in atTop, ∀ t : ℝ, phaseSlope t u=0 → u^n ≤ t := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop (n+3) (b := 4) (by norm_num)).bound (by norm_num : (0 : ℝ)<1)
  filter_upwards [hp,eventually_ge_atTop (1 : ℝ)] with u hu hu1
  intro t hs
  have hu0 : 0 < u := by linarith
  simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hu0.le _),abs_of_pos (Real.exp_pos _),one_mul] at hu
  have he := exp_four_ge_sixteen u hu1
  have hscale := (stationary_scale_bounds t u hu1 hs).1
  have hpow : u^(n+3) ≤ t*u^3 := by nlinarith [Real.pi_gt_three]
  rw [pow_add] at hpow
  exact (mul_le_mul_iff_left₀ (pow_pos hu0 3)).mp hpow

theorem eventually_all_maxima_power_bound (n : ℕ) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → u^n ≤ t := by
  obtain ⟨U,hU⟩ := eventually_atTop.1 (eventually_stationary_power_bound n)
  filter_upwards [maxima_escape (max U 1) (by positivity)] with t ht
  intro u hu hm
  have hub := ht u hu hm
  have hu1 : 1 < u := lt_of_le_of_lt (le_max_right U 1) hub
  have hs := max_real_stationary t u (by linarith) hm
  rw [← (kernel_hasDerivAt u).deriv] at hs
  exact hU u (le_trans (le_max_left U 1) hub.le) t hs

theorem eventually_all_maxima_scale_power_bound (n : ℕ) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → (t*u^3+1)^n ≤ (2 : ℝ)^n*t^(n+1) := by
  filter_upwards [eventually_all_maxima_power_bound (3*n),maxima_escape 1 (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with t hpow hescape ht1
  intro u hu hm
  have hu1 : 1 ≤ u := (hescape u hu hm).le
  have hu3 : 1 ≤ u^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sq_nonneg u)]
  have htu : 1 ≤ t*u^3 := by nlinarith
  have hb : t*u^3+1 ≤ 2*t*u^3 := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ t*u^3+1) hb n
  have hpn := hpow u hu hm
  have hm := mul_le_mul_of_nonneg_left hpn (by positivity : 0 ≤ (2 : ℝ)^n*t^n)
  calc
    _ ≤ (2*t*u^3)^n := hp
    _ = (2 : ℝ)^n*t^n*u^(3*n) := by rw [mul_pow,mul_pow,← pow_mul]
    _ ≤ (2 : ℝ)^n*t^n*t := hm
    _ = _ := by rw [pow_succ]; ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticSaddleGrowth
