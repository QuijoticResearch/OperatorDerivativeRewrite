import Foundation.RiemannEvenConcentration
import Foundation.RiemannEvenEvolution
import Mathlib.Analysis.Convex.Deriv

/-! Lower estimates for the actual tilted amplitude. The positive even tilt
contributes nonnegative real curvature, so the kernel alone supplies a
uniform local lower Gaussian envelope at a stationary real center. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenNormalization
open RiemannQuarticKernel RiemannEvenDomain RiemannEvenRealSaddle RiemannEvenSaddleTimes

theorem kernel_log_curvature_lower (u : ℝ) (hu : 1 ≤ u) :
    -16*Real.pi*Real.exp (4*u)-4 ≤ RiemannQuarticCurvature.realLogCurvature u := by
  have he := (abs_le.mp (RiemannQuarticCurvature.realLogCurvature_bound u hu)).1
  have hf := RiemannQuarticCurvature.leading_curvature_fraction_le_three u hu
  linarith

theorem phaseSlope_deriv_lower (m : ℕ) (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) :
    -16*Real.pi*Real.exp (4*u)-4 ≤ deriv (phaseSlope m t) u := by
  rw [(phaseSlope_hasDerivAt m t u (by linarith)).deriv]
  have hp : 0 ≤ ((2*m : ℕ) : ℝ)*t*((2*m-1 : ℕ) : ℝ)*u^(2*m-2) := by positivity
  linarith [kernel_log_curvature_lower u hu]

theorem local_phaseSlope_deriv_lower (m : ℕ) (t u v : ℝ) (ht : 0 ≤ t) (hu : 2 ≤ u)
    (hd : |v-u| ≤ 1/2) :
    -(16*Real.pi*Real.exp (4*u+2)+4) ≤ deriv (phaseSlope m t) v := by
  have hvl : 1 ≤ v := by linarith [(abs_le.mp hd).1]
  have he : Real.exp (4*v) ≤ Real.exp (4*u+2) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hd).2])
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 16*Real.pi by positivity)
  linarith [phaseSlope_deriv_lower m t v ht hvl]

theorem actual_local_gaussian_lower (m : ℕ) (t u v : ℝ) (ht : 0 ≤ t) (hu : 2 ≤ u)
    (hd : |v-u| ≤ 1/2) (hs : phaseSlope m t u = 0) :
    let c : ℝ := 8*Real.pi*Real.exp (4*u+2)+2
    weighted m 0 t 0 u*Real.exp (-c*(v-u)^2) ≤ weighted m 0 t 0 v := by
  let c : ℝ := 8*Real.pi*Real.exp (4*u+2)+2
  let D : Set ℝ := Icc (u-1/2) (u+1/2)
  let J : ℝ → ℝ := fun w => phaseSlope m t w+2*c*(w-u)
  let F : ℝ → ℝ := fun w => Real.log (weighted m 0 t 0 w)+c*(w-u)^2
  have hpos (w : ℝ) (hw : w ∈ D) : 0 < weighted m 0 t 0 w := by
    exact weighted_pos m t w (by have hw' : u-1/2 ≤ w := hw.1; linarith)
  have hFd (w : ℝ) (hw : w ∈ D) : HasDerivAt F (J w) w := by
    have hw0 : 0 ≤ w := by have hw' : u-1/2 ≤ w := hw.1; linarith
    have ha := (weighted_hasDerivAt m t w).differentiableAt.hasDerivAt
    rw [weighted_deriv_eq m t w hw0] at ha
    have hlog := ha.log (hpos w hw).ne'
    have hg : HasDerivAt (fun w : ℝ => Real.log (weighted m 0 t 0 w)) (phaseSlope m t w) w := by
      convert hlog using 1
      field_simp [(hpos w hw).ne']
    have hpoly := (((hasDerivAt_id w).sub_const u).pow 2).const_mul c
    convert hg.add hpoly using 1
    · funext x; rfl
    · dsimp [J]
      ring
  have hJd (w : ℝ) (hw : w ∈ D) : HasDerivAt J (deriv (phaseSlope m t) w+2*c) w := by
    have hw0 : 0 ≤ w := by have hw' : u-1/2 ≤ w := hw.1; linarith
    have ha := (phaseSlope_hasDerivAt m t w hw0).differentiableAt.hasDerivAt
    have hp := ((hasDerivAt_id w).sub_const u).const_mul (2*c)
    convert ha.add hp using 1
    · funext x; rfl
    · ring
  have hJmono : MonotoneOn J D := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro w hw; exact (hJd w hw).continuousAt.continuousWithinAt
    · intro w hw; exact (hJd w (interior_subset hw)).differentiableAt.differentiableWithinAt
    · intro w hw
      have hw' := interior_subset hw
      have hdist : |w-u| ≤ 1/2 := abs_le.mpr ⟨by linarith [hw'.1],by linarith [hw'.2]⟩
      have hb := local_phaseSlope_deriv_lower m t u w ht hu hdist
      rw [(hJd w hw').deriv]
      dsimp [c]
      linarith
  have hmono : MonotoneOn (deriv F) (interior D) := by
    intro x hx y hy hxy
    rw [(hFd x (interior_subset hx)).deriv,(hFd y (interior_subset hy)).deriv]
    exact hJmono (interior_subset hx) (interior_subset hy) hxy
  have hconv : ConvexOn ℝ D F := hmono.convexOn_of_deriv (convex_Icc _ _)
    (fun w hw => (hFd w hw).continuousAt.continuousWithinAt)
    (fun w hw => (hFd w (interior_subset hw)).differentiableAt.differentiableWithinAt)
  have huD : u ∈ D := ⟨by linarith,by linarith⟩
  have huI : u ∈ interior D := by simp only [D,interior_Icc,mem_Ioo]; constructor <;> linarith
  have hvD : v ∈ D := ⟨by linarith [(abs_le.mp hd).1],by linarith [(abs_le.mp hd).2]⟩
  have hzero : HasDerivAt F 0 u := by simpa only [J,hs,sub_self,mul_zero,add_zero] using hFd u huD
  have hz : derivWithin F (Ioi u) u = 0 := hzero.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi u)
  have hmin := hconv.isMinOn_of_rightDeriv_eq_zero huI hz
  have hF := hmin hvD
  have hlog : Real.log (weighted m 0 t 0 u)-c*(v-u)^2 ≤ Real.log (weighted m 0 t 0 v) := by
    dsimp [F] at hF
    simp only [sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at hF
    linarith
  have he := Real.exp_le_exp.mpr hlog
  rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (hpos u huD),Real.exp_log (hpos v hvD)] at he
  simpa only [neg_mul] using he

theorem actual_halfline_mass_lower (m : ℕ) (t u : ℝ) (ht : 0 ≤ t) (hu : 2 ≤ u)
    (hs : phaseSlope m t u = 0) :
    let c : ℝ := 8*Real.pi*Real.exp (4*u+2)+2
    weighted m 0 t 0 u*(2*Real.exp (-1)/Real.sqrt c) ≤
      ∫ v : ℝ, weighted m 0 t 0 v ∂RiemannQuarticFlow.halfLine := by
  let c : ℝ := 8*Real.pi*Real.exp (4*u+2)+2
  let r : ℝ := 1/Real.sqrt c
  have hc : 0 < c := by dsimp [c]; positivity
  have hc4 : 4 ≤ c := by
    have he : 1 ≤ Real.exp (4*u+2) := Real.one_le_exp (by linarith)
    have hp := mul_le_mul_of_nonneg_left he (show 0 ≤ 8*Real.pi by positivity)
    dsimp [c]
    nlinarith [Real.pi_gt_three]
  have hroot : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hroot2 : 2 ≤ Real.sqrt c := by nlinarith [Real.sq_sqrt hc.le,Real.sqrt_nonneg c]
  have hr : 0 < r := one_div_pos.mpr hroot
  have hrhalf : r ≤ 1/2 := (div_le_iff₀ hroot).mpr (by linarith)
  have hrsq : c*r^2 = 1 := by
    dsimp [r]
    rw [div_pow,one_pow,Real.sq_sqrt hc.le]
    field_simp
  let D : ℝ := weighted m 0 t 0 u*Real.exp (-1)
  have hpoint (v : ℝ) (hv : v ∈ Icc (u-r) (u+r)) : D ≤ weighted m 0 t 0 v := by
    have hdist : |v-u| ≤ r := abs_le.mpr ⟨by linarith [hv.1],by linarith [hv.2]⟩
    have h := actual_local_gaussian_lower m t u v ht hu (hdist.trans hrhalf) hs
    change weighted m 0 t 0 u*Real.exp (-c*(v-u)^2) ≤ weighted m 0 t 0 v at h
    have hpow := pow_le_pow_left₀ (abs_nonneg (v-u)) hdist 2
    rw [sq_abs] at hpow
    have hmul := mul_le_mul_of_nonneg_left hpow hc.le
    have he := Real.exp_le_exp.mpr (show (-1 : ℝ) ≤ -c*(v-u)^2 by nlinarith)
    exact (mul_le_mul_of_nonneg_left he (weighted_pos m t u (by linarith)).le).trans h
  have hcont : Continuous (weighted m 0 t 0) := continuous_iff_continuousAt.mpr
    (fun v => (weighted_hasDerivAt m t v).continuousAt)
  have hi := hcont.intervalIntegrable (μ := volume) (u-r) (u+r)
  have hconst := (continuous_const : Continuous (fun _ : ℝ => D)).intervalIntegrable
    (μ := volume) (u-r) (u+r)
  have hends : u-r ≤ u+r := by linarith
  have hlocal := intervalIntegral.integral_mono_on hends hconst hi hpoint
  rw [intervalIntegral.integral_const] at hlocal
  simp only [smul_eq_mul] at hlocal
  rw [intervalIntegral.integral_of_le hends] at hlocal
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ici (0 : ℝ))] weighted m 0 t 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
    exact (weighted_pos m t v hv).le
  have hsub : Ioc (u-r) (u+r) ≤ᵐ[volume] Ici (0 : ℝ) := by
    exact Eventually.of_forall fun v hv => by
      change 0 ≤ v
      have hv' : u-r < v := hv.1
      linarith
  have hwhole := setIntegral_mono_set (weighted_integrable m 0 t 0) hnonneg hsub
  have hresult := hlocal.trans hwhole
  change weighted m 0 t 0 u*(2*Real.exp (-1)/Real.sqrt c) ≤ ∫ v : ℝ in Ici 0, weighted m 0 t 0 v
  convert hresult using 1
  dsimp [D,r]
  field_simp
  ring

theorem flow_zero_eq_mass (m : ℕ) (t : ℝ) :
    RiemannEvenFlow.flow m t 0 =
      ((∫ v : ℝ, weighted m 0 t 0 v ∂RiemannQuarticFlow.halfLine : ℝ) : ℂ) := by
  rw [RiemannEvenEvolution.flow_eq_cosine_integral]
  simp only [mul_zero,Complex.cos_zero,mul_one]
  exact integral_complex_ofReal

end OperatorDerivativeRewrite.Foundation.RiemannEvenNormalization
