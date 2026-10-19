import Foundation.RiemannQuarticHalflineApproximation
import Foundation.RiemannQuarticSaddleGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
/-! Vanishing relative-error budgets for the actual saddle estimates.
The central radius Q^(-7/16) eventually meets the verified local conditions.
After Gaussian normalization its central error is Q^(-1/4); both model tails
and the actual fixed-window tails vanish. The horizontal envelope takes
center coordinate Q+1 and dominates every smaller center. Time-exponential
compact/endpoint envelopes vanish as well. Actual uniform branch convergence
requires connecting these scalar limits with the verified saddle-growth bounds. -/
noncomputable section
open Set Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticErrorLimits

def centralRadius (Q : ℝ) : ℝ := Q^(-7/16 : ℝ)

theorem centralRadius_pow (Q : ℝ) (hQ : 0 < Q) (n : ℕ) :
    centralRadius Q^n=Q^((-7/16 : ℝ)*(n : ℝ)) := by
  dsimp [centralRadius]
  rw [Real.rpow_mul hQ.le,Real.rpow_natCast]

theorem gaussian_argument (Q : ℝ) (hQ : 0 < Q) : Q*centralRadius Q^2=Q^(1/8 : ℝ) := by
  calc
    _ = Q^(1 : ℝ)*Q^((-7/16 : ℝ)*2) := by rw [Real.rpow_one,centralRadius_pow Q hQ 2]; norm_num
    _ = Q^((1 : ℝ)+(-7/16)*2) := (Real.rpow_add hQ _ _).symm
    _ = _ := by norm_num

theorem central_scaled_error (Q : ℝ) (hQ : 0 < Q) :
    Real.sqrt Q*Q*centralRadius Q^4=Q^(-1/4 : ℝ) := by
  calc
    _ = Q^(1/2 : ℝ)*Q^(1 : ℝ)*Q^((-7/16 : ℝ)*4) := by
      rw [Real.sqrt_eq_rpow,Real.rpow_one,centralRadius_pow Q hQ 4]; norm_num
    _ = Q^((1/2 : ℝ)+1+(-7/16)*4) := by rw [Real.rpow_add hQ,Real.rpow_add hQ]
    _ = _ := by norm_num

theorem central_small_error (Q : ℝ) (hQ : 0 < Q) :
    Q*centralRadius Q^3=Q^(-5/16 : ℝ) := by
  calc
    _ = Q^(1 : ℝ)*Q^((-7/16 : ℝ)*3) := by rw [Real.rpow_one,centralRadius_pow Q hQ 3]; norm_num
    _ = Q^((1 : ℝ)+(-7/16)*3) := (Real.rpow_add hQ _ _).symm
    _ = _ := by norm_num

theorem gaussian_scaled_prefactor (Q : ℝ) (hQ : 0 < Q) :
    Real.sqrt Q/(Q*centralRadius Q)=Q^(-1/16 : ℝ) := by
  calc
    _ = Q^(1/2 : ℝ)/(Q^(1 : ℝ)*Q^(-7/16 : ℝ)) := by rw [Real.sqrt_eq_rpow,Real.rpow_one]; rfl
    _ = Q^(1/2 : ℝ)/Q^((1 : ℝ)+(-7/16)) := by rw [Real.rpow_add hQ]
    _ = Q^((1/2 : ℝ)-(1+(-7/16))) := (Real.rpow_sub hQ _ _).symm
    _ = _ := by norm_num

theorem centralRadius_tendsto_zero : Tendsto centralRadius atTop (nhds 0) := by
  change Tendsto (fun Q : ℝ => Q^(-7/16 : ℝ)) atTop (nhds 0)
  simpa only [neg_div] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<7/16))

theorem eventual_central_conditions (R : ℝ) (hR : 0 < R) :
    ∀ᶠ Q : ℝ in atTop, 0 < centralRadius Q ∧ centralRadius Q ≤ R ∧ 204800*Q*centralRadius Q^3 ≤ 1 := by
  have hs : Tendsto (fun Q : ℝ => 204800*Q^(-5/16 : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero,neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<5/16)).const_mul 204800
  filter_upwards [eventually_gt_atTop (0 : ℝ),centralRadius_tendsto_zero.eventually (gt_mem_nhds hR),
    hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))] with Q hQ hr hsQ
  refine ⟨Real.rpow_pos_of_pos hQ _,hr.le,?_⟩
  have hid : 204800*Q*centralRadius Q^3=204800*Q^(-5/16 : ℝ) := by
    rw [mul_assoc,central_small_error Q hQ]
  rw [hid]
  exact hsQ.le

theorem central_relative_tendsto_zero :
    Tendsto (fun Q : ℝ => Real.sqrt Q*Q*centralRadius Q^4) atTop (nhds 0) := by
  apply (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/4)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Q hQ
  simpa only [neg_div] using (central_scaled_error Q hQ).symm

theorem gaussian_scaled_tail_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun Q : ℝ => Real.sqrt Q*Real.exp (-c*Q*centralRadius Q^2)/(c*Q*centralRadius Q))
      atTop (nhds 0) := by
  have hp : Tendsto (fun Q : ℝ => Q^(-1/16 : ℝ)) atTop (nhds 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/16)
  have he : Tendsto (fun Q : ℝ => Real.exp (-c*Q^(1/8 : ℝ))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/8)).const_mul_atTop_of_neg (by linarith : -c<0))
  have hlim : Tendsto (fun Q : ℝ => (1/c)*Q^(-1/16 : ℝ)*Real.exp (-c*Q^(1/8 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero,zero_mul] using (hp.const_mul (1/c)).mul he
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Q hQ
  symm
  calc
    _ = (1/c)*(Real.sqrt Q/(Q*centralRadius Q))*Real.exp (-c*(Q*centralRadius Q^2)) := by simp only [div_eq_mul_inv]; ring
    _ = _ := by rw [gaussian_argument Q hQ,gaussian_scaled_prefactor Q hQ]

theorem fixed_left_scaled_tendsto_zero (R : ℝ) (hR : 0 < R) :
    Tendsto (fun Q : ℝ => Real.sqrt Q*(Q+1-R-1)*Real.exp (-((3/4 : ℝ)*Q)*R^2)) atTop (nhds 0) := by
  have hk : 0 < (3/4 : ℝ)*R^2 := by positivity
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3/2 : ℝ) ((3/4 : ℝ)*R^2) hk
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2 : ℝ) ((3/4 : ℝ)*R^2) hk
  have hlim := h1.sub (h2.const_mul R)
  simp only [mul_zero,sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Q hQ
  have hp : Q^(3/2 : ℝ)=Real.sqrt Q*Q := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = Q^((1/2 : ℝ)+1) := by norm_num
      _ = _ := by rw [Real.rpow_add hQ,Real.rpow_one]
  have he : Real.exp (-((3/4 : ℝ)*R^2)*Q)=Real.exp (-((3/4 : ℝ)*Q)*R^2) := by congr 1; ring
  rw [hp,he,Real.sqrt_eq_rpow]
  ring

theorem fixed_right_scaled_tendsto_zero (R : ℝ) (hR : 0 < R) :
    Tendsto (fun Q : ℝ => Real.sqrt Q*Real.exp (-((3/4 : ℝ)*Q)*R^2)/(Q*R)) atTop (nhds 0) := by
  have hk : 0 < (3/4 : ℝ)*R^2 := by positivity
  have hp : Tendsto (fun Q : ℝ => Q^(-1/2 : ℝ)) atTop (nhds 0) := by
    simpa only [neg_div] using tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/2)
  have he : Tendsto (fun Q : ℝ => Real.exp (-((3/4 : ℝ)*R^2)*Q)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith : -((3/4 : ℝ)*R^2)<0))
  have hlim := (hp.mul he).div_const R
  simp only [zero_mul,zero_div] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Q hQ
  have hpre : Real.sqrt Q/Q=Q^(-1/2 : ℝ) := by
    calc
      _ = Q^(1/2 : ℝ)/Q^(1 : ℝ) := by rw [Real.sqrt_eq_rpow,Real.rpow_one]
      _ = Q^((1/2 : ℝ)-1) := (Real.rpow_sub hQ _ _).symm
      _ = _ := by norm_num
  have hexp : Real.exp (-((3/4 : ℝ)*R^2)*Q)=Real.exp (-((3/4 : ℝ)*Q)*R^2) := by congr 1; ring
  rw [← hpre,hexp]
  ring

theorem horizontal_envelope_tendsto_zero (R : ℝ) (hR : 0 < R) :
    Tendsto (fun Q : ℝ => Real.sqrt Q*RiemannQuarticHalflineApproximation.horizontalBudget Q (Q+1) (centralRadius Q) R)
      atTop (nhds 0) := by
  have hc := central_relative_tendsto_zero.const_mul 819200
  have hg1 := gaussian_scaled_tail_tendsto_zero 1 (by norm_num)
  have hg2 := gaussian_scaled_tail_tendsto_zero (3/4) (by norm_num)
  have hl := fixed_left_scaled_tendsto_zero R hR
  have hr := fixed_right_scaled_tendsto_zero R hR
  have hlim := (((hc.add hg1).add hg2).add hl).add hr
  simp only [mul_zero,zero_add,add_zero,one_mul,neg_one_mul] at hlim
  apply hlim.congr'
  filter_upwards with Q
  simp only [RiemannQuarticHalflineApproximation.horizontalBudget,neg_mul,div_eq_mul_inv]
  ring

theorem horizontal_budget_le_envelope (Q a r R : ℝ) (ha : a ≤ Q+1) :
    Real.sqrt Q*RiemannQuarticHalflineApproximation.horizontalBudget Q a r R ≤
      Real.sqrt Q*RiemannQuarticHalflineApproximation.horizontalBudget Q (Q+1) r R := by
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg Q)
  unfold RiemannQuarticHalflineApproximation.horizontalBudget
  have hm := mul_le_mul_of_nonneg_right (by linarith : a-R-1 ≤ Q+1-R-1) (Real.exp_pos (-((3/4 : ℝ)*Q)*R^2)).le
  linarith

theorem time_endpoints_tendsto_zero (C D : ℝ) :
    Tendsto (fun t : ℝ => 80*t*(C*Real.exp (10-503*t/8)+D*Real.exp (1-3*t/8))) atTop (nhds 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (503/8) (by norm_num)
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (3/8) (by norm_num)
  simp only [Real.rpow_one] at h1 h2
  have hlim := (h1.const_mul (80*C*Real.exp 10)).add (h2.const_mul (80*D*Real.exp 1))
  simp only [mul_zero,add_zero] at hlim
  apply hlim.congr'
  filter_upwards with t
  rw [show 10-503*t/8=10+(-(503/8)*t) by ring,show 1-3*t/8=1+(-(3/8)*t) by ring,
    Real.exp_add,Real.exp_add]
  ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticErrorLimits
