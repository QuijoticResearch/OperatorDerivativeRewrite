import Foundation.RiemannEvenFourierMoment

/-! Two-sided actual time/center estimates used to control exponentially
weighted moments with growing frequency ranges. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenSaddleGrowth
open RiemannEvenDomain RiemannEvenRealSaddle RiemannEvenSaddleTimes RiemannEvenConcentration

theorem stationary_time_upper (m : ℕ) (hm : 0 < m) (t u : ℝ)
    (hu : ((2*m : ℕ) : ℝ) ≤ u) (hs : phaseSlope m t u = 0) :
    t ≤ 4*Real.pi*Real.exp (4*u) := by
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have ht : 0 < t := by
    rw [← phaseSlope_zero_saddleTime m hm t u hu0 hs]
    exact saddleTime_pos m hm u hu1
  have hp : 1 ≤ u^(2*m-1) := one_le_pow₀ hu1
  have hnp := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (2*m) : (0 : ℝ) ≤ ((2*m : ℕ) : ℝ))
  have hnt := mul_le_mul_of_nonneg_right (hn.trans (by simpa using hnp)) ht.le
  have hb := (stationary_scale_bounds m t u hu1 hs).2
  nlinarith

theorem exists_stationary_time_exponential_lower (m : ℕ) (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ t u : ℝ, ((2*m : ℕ) : ℝ) ≤ u →
      phaseSlope m t u = 0 → c*Real.exp (3*u) ≤ t := by
  let n : ℝ := ((2*m : ℕ) : ℝ)
  have hn : (2 : ℝ) ≤ n := by dsimp [n]; exact_mod_cast (show 2 ≤ 2*m by omega)
  have hT := saddleTime_pos m hm n (by linarith)
  refine ⟨saddleTime m n*Real.exp (-3*n),by positivity,?_⟩
  intro t u hu hs
  have hu0 : 0 < u := by change n ≤ u at hu; linarith
  have hg := saddleTime_exponential_lower m hm n u le_rfl hu
  rw [phaseSlope_zero_saddleTime m hm t u hu0 hs] at hg
  convert hg using 1
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem quadratic_linear_eventually_le_exp (c A B : ℝ) (hc : 0 < c) :
    ∀ᶠ u : ℝ in atTop, u^2+A*u+B ≤ c*Real.exp (2*u) := by
  have h2 := isLittleO_pow_exp_pos_mul_atTop 2 (b := 2) (by norm_num)
  have h1 := (isLittleO_pow_exp_pos_mul_atTop 1 (b := 2) (by norm_num)).const_mul_left A
  have h0 := (isLittleO_pow_exp_pos_mul_atTop 0 (b := 2) (by norm_num)).const_mul_left B
  have h := ((h2.add h1).add h0).bound hc
  filter_upwards [h] with u hu
  simp only [pow_one,pow_zero,mul_one,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hu
  exact (le_abs_self _).trans hu

end OperatorDerivativeRewrite.Foundation.RiemannEvenSaddleGrowth
