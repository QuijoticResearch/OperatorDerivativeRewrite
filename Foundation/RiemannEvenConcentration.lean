import Foundation.RiemannEvenSaddleTimes
import Foundation.RiemannQuarticGaussianTail

/-! Quantitative bounds for the actual integer-even tilted amplitude.
The saddle-time growth controls the actual phase, yielding a global
right Gaussian envelope at any stationary center in the proved domain. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenConcentration
open RiemannQuarticKernel RiemannEvenDomain RiemannEvenRealSaddle RiemannEvenSaddleTimes

theorem saddleTime_deriv_gt_three_mul (m : ℕ) (hm : 0 < m) (u : ℝ)
    (hu : ((2*m : ℕ) : ℝ) ≤ u) : 3*saddleTime m u < deriv (saddleTime m) u := by
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hs : phaseSlope m (saddleTime m u) u = 0 := by
    rw [phaseSlope_factor m hm _ u hu0]
    simp
  have hupper := stationary_phaseSlope_deriv_upper m hm (saddleTime m u) u
    (saddleTime_pos m hm u hu1).le hu hs
  rw [(phaseSlope_factor_hasDerivAt m hm (saddleTime m u) u hu0 rfl).deriv] at hupper
  have hscale := (stationary_scale_bounds m (saddleTime m u) u hu1 hs).2
  have hc : 0 < ((2*m : ℕ) : ℝ)*u^(2*m-1) := mul_pos (by linarith) (pow_pos hu0 _)
  have hp : (((2*m : ℕ) : ℝ)*u^(2*m-1))*(3*saddleTime m u) <
      (((2*m : ℕ) : ℝ)*u^(2*m-1))*deriv (saddleTime m) u := by nlinarith
  nlinarith

theorem scaled_saddleTime_monotoneOn (m : ℕ) (hm : 0 < m) :
    MonotoneOn (fun u : ℝ => saddleTime m u*Real.exp (-3*u)) (Ici (((2*m : ℕ) : ℝ))) := by
  have hn : (0 : ℝ) < ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*m by omega)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro u hu
    exact ((saddleTime_analyticAt m hm u (lt_of_lt_of_le hn hu)).continuousAt.mul
      (by fun_prop : ContinuousAt (fun u : ℝ => Real.exp (-3*u)) u)).continuousWithinAt
  · intro u hu
    have hu' : ((2*m : ℕ) : ℝ) < u := by simpa only [interior_Ici,mem_Ioi] using hu
    exact ((saddleTime_analyticAt m hm u (lt_trans hn hu')).differentiableAt.mul
      (by fun_prop : DifferentiableAt ℝ (fun u : ℝ => Real.exp (-3*u)) u)).differentiableWithinAt
  · intro u hu
    have hu' : ((2*m : ℕ) : ℝ) < u := by simpa only [interior_Ici,mem_Ioi] using hu
    have hT := (saddleTime_analyticAt m hm u (lt_trans hn hu')).differentiableAt.hasDerivAt
    have he := (((hasDerivAt_id u).const_mul (-3 : ℝ)).exp)
    have hd : HasDerivAt (fun w : ℝ => saddleTime m w*Real.exp (-3*w))
        ((deriv (saddleTime m) u-3*saddleTime m u)*Real.exp (-3*u)) u := by
      convert hT.mul he using 1
      · funext w; rfl
      · simp only [id_eq]
        ring
    rw [hd.deriv]
    exact mul_nonneg (sub_nonneg.mpr (saddleTime_deriv_gt_three_mul m hm u hu'.le).le)
      (Real.exp_pos _).le

theorem saddleTime_exponential_lower (m : ℕ) (hm : 0 < m) (u v : ℝ)
    (hu : ((2*m : ℕ) : ℝ) ≤ u) (huv : u ≤ v) :
    saddleTime m u*Real.exp (3*(v-u)) ≤ saddleTime m v := by
  have h := scaled_saddleTime_monotoneOn m hm hu (hu.trans huv) huv
  have hp := mul_le_mul_of_nonneg_right h (Real.exp_pos (3*v)).le
  have heL : saddleTime m u*Real.exp (-3*u)*Real.exp (3*v) =
      saddleTime m u*Real.exp (3*(v-u)) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  have heR : saddleTime m v*Real.exp (-3*v)*Real.exp (3*v) = saddleTime m v := by
    rw [mul_assoc,← Real.exp_add]
    simp
  simpa only [heL,heR] using hp

theorem saddleTime_linear_lower (m : ℕ) (hm : 0 < m) (u v : ℝ)
    (hu : ((2*m : ℕ) : ℝ) ≤ u) (huv : u ≤ v) :
    saddleTime m u*(1+3*(v-u)) ≤ saddleTime m v := by
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have hp := (saddleTime_pos m hm u (by linarith)).le
  simpa only [add_comm] using
    (mul_le_mul_of_nonneg_left (Real.add_one_le_exp (3*(v-u))) hp).trans
      (saddleTime_exponential_lower m hm u v hu huv)

theorem phaseSlope_right_linear_bound (m : ℕ) (hm : 0 < m) (t u v : ℝ)
    (hu : ((2*m : ℕ) : ℝ) ≤ u) (huv : u ≤ v) (hs : phaseSlope m t u = 0) :
    phaseSlope m t v ≤ -3*((2*m : ℕ) : ℝ)*t*u^(2*m-1)*(v-u) := by
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
  have he := phaseSlope_zero_saddleTime m hm t u hu0 hs
  have ht : 0 < t := by rw [← he]; exact saddleTime_pos m hm u (by linarith)
  have hT := saddleTime_linear_lower m hm u v hu huv
  rw [he] at hT
  have hpow := pow_le_pow_left₀ hu0.le huv (2*m-1)
  have hneg : ((2*m : ℕ) : ℝ)*(-3*t*(v-u)) ≤ 0 := by
    have hd : 0 ≤ v-u := sub_nonneg.mpr huv
    have hp : 0 ≤ ((2*m : ℕ) : ℝ)*t*(v-u) := by positivity
    nlinarith
  calc
    _ = ((2*m : ℕ) : ℝ)*(t-saddleTime m v)*v^(2*m-1) := phaseSlope_factor m hm t v hv0
    _ ≤ ((2*m : ℕ) : ℝ)*(-3*t*(v-u))*v^(2*m-1) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hv0.le _)
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith
    _ ≤ ((2*m : ℕ) : ℝ)*(-3*t*(v-u))*u^(2*m-1) := mul_le_mul_of_nonpos_left hpow hneg
    _ = _ := by ring

theorem actual_right_gaussian_envelope (m : ℕ) (hm : 0 < m) (t u v : ℝ)
    (hu : ((2*m : ℕ) : ℝ) ≤ u) (huv : u ≤ v) (hs : phaseSlope m t u = 0) :
    weighted m 0 t 0 v ≤ weighted m 0 t 0 u*
      Real.exp (-((3/2 : ℝ)*((2*m : ℕ) : ℝ)*t*u^(2*m-1))*(v-u)^2) := by
  let c : ℝ := (3/2 : ℝ)*((2*m : ℕ) : ℝ)*t*u^(2*m-1)
  have hu0 : 0 ≤ u := (Nat.cast_nonneg _).trans hu
  have hF : AntitoneOn (fun w : ℝ => weighted m 0 t 0 w*Real.exp (c*(w-u)^2)) (Ici u) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact ((weighted_continuousOn m 0 t 0).mono (fun w hw => hu0.trans hw)).mul
        (by fun_prop : Continuous (fun w : ℝ => Real.exp (c*(w-u)^2))).continuousOn
    · intro w hw
      exact ((weighted_hasDerivAt m t w).differentiableAt.mul
        (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => Real.exp (c*(w-u)^2)) w)).differentiableWithinAt
    · intro w hw
      have huw : u < w := by simpa only [interior_Ici,mem_Ioi] using hw
      have hw0 := hu0.trans huw.le
      have ha := (weighted_hasDerivAt m t w).differentiableAt.hasDerivAt
      rw [weighted_deriv_eq m t w hw0] at ha
      have he := ((((hasDerivAt_id w).sub_const u).pow 2).const_mul c).exp
      have hd : HasDerivAt (fun w : ℝ => weighted m 0 t 0 w*Real.exp (c*(w-u)^2))
          ((weighted m 0 t 0 w*Real.exp (c*(w-u)^2))*(phaseSlope m t w+2*c*(w-u))) w := by
        convert ha.mul he using 1
        · funext v; rfl
        · simp only [id_eq,Pi.pow_apply]
          norm_num
          ring
      rw [hd.deriv]
      apply mul_nonpos_of_nonneg_of_nonpos
      · exact mul_nonneg (weighted_pos m t w hw0).le (Real.exp_pos _).le
      · have h := phaseSlope_right_linear_bound m hm t u w hu huw.le hs
        dsimp [c]
        nlinarith
  have h := hF (show u ∈ Ici u from by exact le_refl u) (show v ∈ Ici u from huv) huv
  simp only [sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero,Real.exp_zero,mul_one] at h
  have hp := mul_le_mul_of_nonneg_right h (Real.exp_pos (-c*(v-u)^2)).le
  have he : Real.exp (c*(v-u)^2)*Real.exp (-c*(v-u)^2) = 1 := by
    rw [← Real.exp_add]
    rw [show c*(v-u)^2 + -c*(v-u)^2 = 0 by ring,Real.exp_zero]
  change weighted m 0 t 0 v ≤ weighted m 0 t 0 u*Real.exp (-c*(v-u)^2)
  simpa only [mul_assoc,he,mul_one] using hp

theorem phaseSlope_left_linear_bound (m : ℕ) (hm : 0 < m) (t u v : ℝ)
    (hv : ((2*m : ℕ) : ℝ) ≤ v) (hvu : v ≤ u) (hd : u-v ≤ 1/2)
    (hs : phaseSlope m t u = 0) :
    ((2*m : ℕ) : ℝ)*t*v^(2*m-1)*(u-v) ≤ phaseSlope m t v := by
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have hv0 : 0 < v := by linarith
  have hu0 : 0 < u := lt_of_lt_of_le hv0 hvu
  have he := phaseSlope_zero_saddleTime m hm t u hu0 hs
  have ht : 0 < t := by rw [← he]; exact saddleTime_pos m hm u (by linarith)
  have hT := saddleTime_linear_lower m hm v u hv hvu
  rw [he] at hT
  have hd0 : 0 ≤ u-v := sub_nonneg.mpr hvu
  have hden : 0 < 1+3*(u-v) := by linarith
  have hratio : saddleTime m v ≤ t/(1+3*(u-v)) := (le_div_iff₀ hden).mpr hT
  have hpoly : 1 ≤ (1-(u-v))*(1+3*(u-v)) := by nlinarith
  have hratio' : t/(1+3*(u-v)) ≤ t*(1-(u-v)) := by
    apply (div_le_iff₀ hden).mpr
    have hp := mul_le_mul_of_nonneg_left hpoly ht.le
    nlinarith
  have hgap : t*(u-v) ≤ t-saddleTime m v := by linarith [hratio.trans hratio']
  calc
    _ = ((2*m : ℕ) : ℝ)*(t*(u-v))*v^(2*m-1) := by ring
    _ ≤ ((2*m : ℕ) : ℝ)*(t-saddleTime m v)*v^(2*m-1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (by linarith)) (pow_nonneg hv0.le _)
    _ = _ := (phaseSlope_factor m hm t v hv0).symm

theorem actual_left_gaussian_envelope (m : ℕ) (hm : 0 < m) (t u v : ℝ)
    (hv : ((2*m : ℕ) : ℝ) ≤ v) (hvu : v ≤ u) (hd : u-v ≤ 1/2)
    (hs : phaseSlope m t u = 0) :
    weighted m 0 t 0 v ≤ weighted m 0 t 0 u*
      Real.exp (-((1/2 : ℝ)*((2*m : ℕ) : ℝ)*t*v^(2*m-1))*(v-u)^2) := by
  let c : ℝ := (1/2 : ℝ)*((2*m : ℕ) : ℝ)*t*v^(2*m-1)
  have hv0 : 0 ≤ v := (Nat.cast_nonneg _).trans hv
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have hu0 : 0 < u := by linarith
  have ht : 0 < t := by
    rw [← phaseSlope_zero_saddleTime m hm t u hu0 hs]
    exact saddleTime_pos m hm u (by linarith)
  have hF : MonotoneOn (fun w : ℝ => weighted m 0 t 0 w*Real.exp (c*(w-u)^2)) (Icc v u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact ((weighted_continuousOn m 0 t 0).mono (fun w hw => hv0.trans hw.1)).mul
        (by fun_prop : Continuous (fun w : ℝ => Real.exp (c*(w-u)^2))).continuousOn
    · intro w hw
      exact ((weighted_hasDerivAt m t w).differentiableAt.mul
        (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => Real.exp (c*(w-u)^2)) w)).differentiableWithinAt
    · intro w hw
      have hw' : v < w ∧ w < u := by simpa only [interior_Icc,mem_Ioo] using hw
      have hw0 := hv0.trans hw'.1.le
      have ha := (weighted_hasDerivAt m t w).differentiableAt.hasDerivAt
      rw [weighted_deriv_eq m t w hw0] at ha
      have he := ((((hasDerivAt_id w).sub_const u).pow 2).const_mul c).exp
      have hder : HasDerivAt (fun w : ℝ => weighted m 0 t 0 w*Real.exp (c*(w-u)^2))
          ((weighted m 0 t 0 w*Real.exp (c*(w-u)^2))*(phaseSlope m t w+2*c*(w-u))) w := by
        convert ha.mul he using 1
        · funext x; rfl
        · simp only [id_eq,Pi.pow_apply]
          norm_num
          ring
      rw [hder.deriv]
      apply mul_nonneg
      · exact mul_nonneg (weighted_pos m t w hw0).le (Real.exp_pos _).le
      · have hleft := phaseSlope_left_linear_bound m hm t u w (hv.trans hw'.1.le) hw'.2.le
          (by linarith) hs
        have hpow := pow_le_pow_left₀ hv0 hw'.1.le (2*m-1)
        have hp := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (show 0 ≤ ((2*m : ℕ) : ℝ)*t by positivity))
          (show 0 ≤ u-w by linarith)
        dsimp [c]
        nlinarith
  have h := hF (show v ∈ Icc v u from ⟨le_refl v,hvu⟩) (show u ∈ Icc v u from ⟨hvu,le_refl u⟩) hvu
  simp only [sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero,Real.exp_zero,mul_one] at h
  have hp := mul_le_mul_of_nonneg_right h (Real.exp_pos (-c*(v-u)^2)).le
  have he : Real.exp (c*(v-u)^2)*Real.exp (-c*(v-u)^2) = 1 := by
    rw [← Real.exp_add,show c*(v-u)^2 + -c*(v-u)^2 = 0 by ring,Real.exp_zero]
  change weighted m 0 t 0 v ≤ weighted m 0 t 0 u*Real.exp (-c*(v-u)^2)
  simpa only [mul_assoc,he,mul_one] using hp

theorem actual_two_sided_gaussian_envelope (m : ℕ) (hm : 0 < m) (t u v : ℝ)
    (hu : ((2*m : ℕ) : ℝ)+1 ≤ u) (hd : |v-u| ≤ 1/2) (hs : phaseSlope m t u = 0) :
    weighted m 0 t 0 v ≤ weighted m 0 t 0 u*
      Real.exp (-((1/2 : ℝ)*((2*m : ℕ) : ℝ)*t*(u-1/2)^(2*m-1))*(v-u)^2) := by
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have hu0 : 0 < u := by linarith
  have hhalf : 0 ≤ u-1/2 := by linarith
  have ht : 0 < t := by
    rw [← phaseSlope_zero_saddleTime m hm t u hu0 hs]
    exact saddleTime_pos m hm u (by linarith)
  have hbase := (weighted_pos m t u hu0.le).le
  have hvlo : u-1/2 ≤ v := by linarith [(abs_le.mp hd).1]
  by_cases hvu : v ≤ u
  · have h := actual_left_gaussian_envelope m hm t u v (by linarith) hvu
      (by linarith [(abs_le.mp hd).1]) hs
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hbase
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hhalf hvlo (2*m-1))
      (show 0 ≤ (1/2 : ℝ)*((2*m : ℕ) : ℝ)*t by positivity)
    have hsq := mul_le_mul_of_nonneg_right hp (sq_nonneg (v-u))
    nlinarith
  · have huv : u ≤ v := (lt_of_not_ge hvu).le
    have h := actual_right_gaussian_envelope m hm t u v (by linarith) huv hs
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hbase
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hhalf (show u-1/2 ≤ u by linarith) (2*m-1))
      (show 0 ≤ (1/2 : ℝ)*((2*m : ℕ) : ℝ)*t by positivity)
    have hpos : 0 ≤ ((2*m : ℕ) : ℝ)*t*u^(2*m-1) := by positivity
    have hc : (1/2 : ℝ)*((2*m : ℕ) : ℝ)*t*(u-1/2)^(2*m-1) ≤
        (3/2 : ℝ)*((2*m : ℕ) : ℝ)*t*u^(2*m-1) := by nlinarith
    have hsq := mul_le_mul_of_nonneg_right hc (sq_nonneg (v-u))
    nlinarith

theorem actual_left_far_envelope (m : ℕ) (hm : 0 < m) (t u v : ℝ)
    (hu : ((2*m : ℕ) : ℝ)+1 ≤ u) (hv : ((2*m : ℕ) : ℝ) ≤ v) (hvu : v ≤ u-1/2)
    (hs : phaseSlope m t u = 0) :
    weighted m 0 t 0 v ≤ weighted m 0 t 0 u*
      Real.exp (-((1/8 : ℝ)*((2*m : ℕ) : ℝ)*t*(u-1/2)^(2*m-1))) := by
  have hmono := (weighted_strictMonoOn_left_of_stationary m hm t u (by linarith) hs).monotoneOn
  have hstep := hmono (show v ∈ Icc (((2*m : ℕ) : ℝ)) u from ⟨hv,by linarith⟩)
    (show u-1/2 ∈ Icc (((2*m : ℕ) : ℝ)) u from ⟨by linarith,by linarith⟩) hvu
  have h := actual_two_sided_gaussian_envelope m hm t u (u-1/2) hu (by
    rw [show (u-1/2)-u = -(1/2 : ℝ) by ring]
    norm_num) hs
  apply hstep.trans
  convert h using 1 <;> congr 2 <;> ring

theorem actual_right_tail_integral_bound (m : ℕ) (hm : 0 < m) (t u r : ℝ)
    (hu : ((2*m : ℕ) : ℝ) ≤ u) (hr : 0 < r) (hs : phaseSlope m t u = 0) :
    let c : ℝ := (3/2 : ℝ)*((2*m : ℕ) : ℝ)*t*u^(2*m-1)
    (∫ s : ℝ in Ioi r, weighted m 0 t 0 (u+s)) ≤
      weighted m 0 t 0 u*Real.exp (-c*r^2)/(2*c*r) := by
  let c : ℝ := (3/2 : ℝ)*((2*m : ℕ) : ℝ)*t*u^(2*m-1)
  change (∫ s : ℝ in Ioi r, weighted m 0 t 0 (u+s)) ≤
    weighted m 0 t 0 u*Real.exp (-c*r^2)/(2*c*r)
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have hu0 : 0 < u := by linarith
  have ht : 0 < t := by
    rw [← phaseSlope_zero_saddleTime m hm t u hu0 hs]
    exact saddleTime_pos m hm u (by linarith)
  have hc : 0 < c := by dsimp [c]; positivity
  have hpoint (s : ℝ) (hsi : s ∈ Ioi r) :
      weighted m 0 t 0 (u+s) ≤ weighted m 0 t 0 u*Real.exp (-c*s^2) := by
    have h := actual_right_gaussian_envelope m hm t u (u+s) hu (by have hsr : r < s := hsi; linarith) hs
    simpa only [show (u+s)-u = s by ring] using h
  have hcont : Continuous (fun s : ℝ => weighted m 0 t 0 (u+s)) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (weighted_hasDerivAt m t (u+s)).continuousAt.comp
      (by fun_prop : ContinuousAt (fun s : ℝ => u+s) s)
  have hg : Integrable (fun s : ℝ => weighted m 0 t 0 u*Real.exp (-c*s^2)) :=
    (integrable_exp_neg_mul_sq hc).const_mul _
  have hi : IntegrableOn (fun s : ℝ => weighted m 0 t 0 (u+s)) (Ioi r) := by
    apply hg.integrableOn.mono' hcont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsi
    have hsi' : r < s := hsi
    rw [Real.norm_eq_abs,abs_of_pos (weighted_pos m t (u+s) (by linarith))]
    exact hpoint s hsi
  have hbound := setIntegral_mono_on hi hg.integrableOn measurableSet_Ioi hpoint
  rw [integral_const_mul] at hbound
  have htail := RiemannQuarticGaussianTail.real_tail_bound c r hc hr
  calc
    _ ≤ weighted m 0 t 0 u*(∫ s : ℝ in Ioi r, Real.exp (-c*s^2)) := hbound
    _ ≤ weighted m 0 t 0 u*(Real.exp (-c*r^2)/(2*c*r)) :=
      mul_le_mul_of_nonneg_left htail (weighted_pos m t u hu0.le).le
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.RiemannEvenConcentration
