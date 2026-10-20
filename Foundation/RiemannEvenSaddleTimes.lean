import Foundation.RiemannEvenRealSaddle

/-! The exact integer-even saddle-time map. On the order-dependent far
positive axis it is strictly increasing, giving uniqueness of actual
late-time global amplitude maxima without exceptional times. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenSaddleTimes
open RiemannQuarticKernel RiemannEvenDomain RiemannEvenRealSaddle

def saddleTime (m : ℕ) (u : ℝ) : ℝ :=
  -(deriv kernel u/kernel u)/(((2*m : ℕ) : ℝ)*u^(2*m-1))

theorem saddleTime_quartic : saddleTime 2 = RiemannQuarticSaddleTimes.saddleTime := rfl

theorem saddleTime_analyticAt (m : ℕ) (hm : 0 < m) (u : ℝ) (hu : 0 < u) :
    AnalyticAt ℝ (saddleTime m) u := by
  have hn : (0 : ℝ) < ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*m by omega)
  have ha := RiemannQuarticSaddleTimes.kernel_analyticAt u
  exact ((ha.deriv.div ha (ne_of_gt (kernel_pos u hu.le))).neg).div
    (analyticAt_const.mul (analyticAt_id.pow (2*m-1)))
    (ne_of_gt (mul_pos hn (pow_pos hu _)))

theorem phaseSlope_factor (m : ℕ) (hm : 0 < m) (t u : ℝ) (hu : 0 < u) :
    phaseSlope m t u = ((2*m : ℕ) : ℝ)*(t-saddleTime m u)*u^(2*m-1) := by
  have hn : (0 : ℝ) < ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*m by omega)
  have hk := ne_of_gt (kernel_pos u hu.le)
  unfold phaseSlope saddleTime
  field_simp [hn.ne',hu.ne']
  ring

theorem phaseSlope_zero_saddleTime (m : ℕ) (hm : 0 < m) (t u : ℝ) (hu : 0 < u)
    (hs : phaseSlope m t u = 0) : saddleTime m u = t := by
  have hn : (0 : ℝ) < ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*m by omega)
  rw [phaseSlope_factor m hm t u hu] at hs
  have hp := (mul_eq_zero.mp hs).resolve_right (pow_ne_zero _ hu.ne')
  have he := (mul_eq_zero.mp hp).resolve_left hn.ne'
  exact (sub_eq_zero.mp he).symm

theorem max_saddleTime (m : ℕ) (hm : 0 < m) (t u : ℝ) (hu : 0 < u)
    (hmax : IsMaxOn (weighted m 0 t 0) (Ici 0) u) : saddleTime m u = t :=
  phaseSlope_zero_saddleTime m hm t u hu (max_real_stationary m t u hu hmax)

theorem saddleTime_pos (m : ℕ) (hm : 0 < m) (u : ℝ) (hu : 1 ≤ u) :
    0 < saddleTime m u := by
  have hn : (0 : ℝ) < ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*m by omega)
  unfold saddleTime
  exact div_pos (neg_pos.mpr (RiemannQuarticCurvature.realLogSlope_neg u hu))
    (mul_pos hn (pow_pos (by linarith : 0 < u) _))

theorem phaseSlope_factor_hasDerivAt (m : ℕ) (hm : 0 < m) (t u : ℝ) (hu : 0 < u)
    (hs : saddleTime m u = t) :
    HasDerivAt (phaseSlope m t) (-((2*m : ℕ) : ℝ)*u^(2*m-1)*deriv (saddleTime m) u) u := by
  have hT := (saddleTime_analyticAt m hm u hu).differentiableAt.hasDerivAt
  have h := (((hasDerivAt_const u t).sub hT).const_mul ((2*m : ℕ) : ℝ)).mul
    ((hasDerivAt_id u).pow (2*m-1))
  have he : phaseSlope m t =ᶠ[nhds u]
      (fun w => ((2*m : ℕ) : ℝ)*(t-saddleTime m w)*w^(2*m-1)) := by
    filter_upwards [Ioi_mem_nhds hu] with w hw
    exact phaseSlope_factor m hm t w hw
  convert h.congr_of_eventuallyEq he using 1
  simp only [Pi.sub_apply,Pi.pow_apply,id_eq,hs,sub_self,mul_zero,zero_mul]
  ring

theorem saddleTime_deriv_pos (m : ℕ) (hm : 0 < m) (u : ℝ)
    (hu : ((2*m : ℕ) : ℝ) ≤ u) : 0 < deriv (saddleTime m) u := by
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hs : phaseSlope m (saddleTime m u) u = 0 := by
    rw [phaseSlope_factor m hm _ u hu0]
    simp
  have hupper := stationary_phaseSlope_deriv_upper m hm (saddleTime m u) u
    (saddleTime_pos m hm u hu1).le hu hs
  have hneg : deriv (phaseSlope m (saddleTime m u)) u < 0 := by
    nlinarith [mul_pos Real.pi_pos (Real.exp_pos (4*u))]
  rw [(phaseSlope_factor_hasDerivAt m hm (saddleTime m u) u hu0 rfl).deriv] at hneg
  by_contra hnot
  have hd : deriv (saddleTime m) u ≤ 0 := le_of_not_gt hnot
  have hcoef : -((2*m : ℕ) : ℝ)*u^(2*m-1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg hu0.le _)
  have hp := mul_nonneg_of_nonpos_of_nonpos hcoef hd
  linarith

theorem saddleTime_strictMonoOn (m : ℕ) (hm : 0 < m) :
    StrictMonoOn (saddleTime m) (Ici (((2*m : ℕ) : ℝ))) := by
  have hn : (0 : ℝ) < ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*m by omega)
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro u hu
    exact (saddleTime_analyticAt m hm u (lt_of_lt_of_le hn hu)).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : ((2*m : ℕ) : ℝ) < u := by simpa only [interior_Ici,mem_Ioi] using hu
    exact saddleTime_deriv_pos m hm u hu'.le

theorem large_stationary_unique (m : ℕ) (hm : 0 < m) (t u v : ℝ)
    (hu : ((2*m : ℕ) : ℝ) ≤ u) (hv : ((2*m : ℕ) : ℝ) ≤ v)
    (hsu : phaseSlope m t u = 0) (hsv : phaseSlope m t v = 0) : u = v := by
  have hn : (0 : ℝ) < ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*m by omega)
  apply (saddleTime_strictMonoOn m hm).injOn hu hv
  rw [phaseSlope_zero_saddleTime m hm t u (lt_of_lt_of_le hn hu) hsu,
    phaseSlope_zero_saddleTime m hm t v (lt_of_lt_of_le hn hv) hsv]

theorem phaseSlope_pos_left_of_stationary (m : ℕ) (hm : 0 < m) (t u v : ℝ)
    (hv : ((2*m : ℕ) : ℝ) ≤ v) (hvu : v < u) (hs : phaseSlope m t u = 0) :
    0 < phaseSlope m t v := by
  have hn : (0 : ℝ) < ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*m by omega)
  have hv0 := lt_of_lt_of_le hn hv
  have hu0 := lt_trans hv0 hvu
  have hT := saddleTime_strictMonoOn m hm hv (hv.trans hvu.le) hvu
  rw [phaseSlope_zero_saddleTime m hm t u hu0 hs] at hT
  rw [phaseSlope_factor m hm t v hv0]
  exact mul_pos (mul_pos hn (sub_pos.mpr hT)) (pow_pos hv0 _)

theorem phaseSlope_neg_right_of_stationary (m : ℕ) (hm : 0 < m) (t u v : ℝ)
    (hu : ((2*m : ℕ) : ℝ) ≤ u) (huv : u < v) (hs : phaseSlope m t u = 0) :
    phaseSlope m t v < 0 := by
  have hn : (0 : ℝ) < ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*m by omega)
  have hu0 := lt_of_lt_of_le hn hu
  have hv0 := lt_trans hu0 huv
  have hT := saddleTime_strictMonoOn m hm hu (hu.trans huv.le) huv
  rw [phaseSlope_zero_saddleTime m hm t u hu0 hs] at hT
  rw [phaseSlope_factor m hm t v hv0]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hn (sub_neg.mpr hT)) (pow_pos hv0 _)

theorem weighted_deriv_eq (m : ℕ) (t u : ℝ) (hu : 0 ≤ u) :
    deriv (weighted m 0 t 0) u = weighted m 0 t 0 u * phaseSlope m t u := by
  rw [(weighted_hasDerivAt m t u).deriv]
  have hk := ne_of_gt (kernel_pos u hu)
  simp only [weighted,phaseSlope,pow_zero,one_mul,zero_mul,add_zero]
  field_simp

theorem weighted_strictMonoOn_left_of_stationary (m : ℕ) (hm : 0 < m) (t u : ℝ)
    (_hu : ((2*m : ℕ) : ℝ) ≤ u) (hs : phaseSlope m t u = 0) :
    StrictMonoOn (weighted m 0 t 0) (Icc (((2*m : ℕ) : ℝ)) u) := by
  have hzero : (0 : ℝ) ≤ ((2*m : ℕ) : ℝ) := Nat.cast_nonneg _
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact (weighted_continuousOn m 0 t 0).mono (fun v hv => hzero.trans hv.1)
  · intro v hv
    have hv' : ((2*m : ℕ) : ℝ) < v ∧ v < u := by
      simpa only [interior_Icc,mem_Ioo] using hv
    have hv0 : 0 ≤ v := hzero.trans hv'.1.le
    rw [weighted_deriv_eq m t v hv0]
    exact mul_pos (weighted_pos m t v hv0)
      (phaseSlope_pos_left_of_stationary m hm t u v hv'.1.le hv'.2 hs)

theorem weighted_strictAntiOn_right_of_stationary (m : ℕ) (hm : 0 < m) (t u : ℝ)
    (hu : ((2*m : ℕ) : ℝ) ≤ u) (hs : phaseSlope m t u = 0) :
    StrictAntiOn (weighted m 0 t 0) (Ici u) := by
  have hu0 : 0 ≤ u := (Nat.cast_nonneg _).trans hu
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · exact (weighted_continuousOn m 0 t 0).mono (fun v hv => hu0.trans hv)
  · intro v hv
    have huv : u < v := by simpa only [interior_Ici,mem_Ioi] using hv
    have hv0 := hu0.trans huv.le
    rw [weighted_deriv_eq m t v hv0]
    exact mul_neg_of_pos_of_neg (weighted_pos m t v hv0)
      (phaseSlope_neg_right_of_stationary m hm t u v hu huv hs)

theorem eventually_unique_global_max (m : ℕ) (hm : 0 < m) :
    ∀ᶠ t : ℝ in atTop, ∃! u : ℝ,
      u ∈ Ici (0 : ℝ) ∧ IsMaxOn (weighted m 0 t 0) (Ici 0) u := by
  filter_upwards [maxima_escape m hm ((2*m : ℕ) : ℝ) (Nat.cast_nonneg _)] with t ht
  obtain ⟨u,hu,hmax⟩ := exists_global_max m t
  refine ⟨u,⟨hu,hmax⟩,?_⟩
  intro v hv
  have hu0 : 0 < u := lt_of_le_of_lt (Nat.cast_nonneg _) (ht u hu hmax)
  have hv0 : 0 < v := lt_of_le_of_lt (Nat.cast_nonneg _) (ht v hv.1 hv.2)
  exact large_stationary_unique m hm t v u (ht v hv.1 hv.2).le (ht u hu hmax).le
    (max_real_stationary m t v hv0 hv.2) (max_real_stationary m t u hu0 hmax)

end OperatorDerivativeRewrite.Foundation.RiemannEvenSaddleTimes
