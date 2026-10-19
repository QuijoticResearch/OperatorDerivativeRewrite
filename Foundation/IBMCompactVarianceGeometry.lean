import Foundation.IBMCompactKernelIncrements
import Foundation.IBMBoundaryCurvature
import Foundation.IBMVarianceClockGeometry

/-! Global geometry of the ACTUAL scenery variance for arbitrary compact
normalized kernels. A larger support window avoids artificial boundary cases. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompactVarianceGeometry
open InfiniteGaussian IBMContinuousScenery IBMContinuousBulkVariance IBMBoundaryCurvature
set_option backward.isDefEq.respectTransparency false

theorem exists_window {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hmass : (∫ u, ρ u) = 1) (x : ℝ) :
    ∃ R : ℝ, |x| < R ∧ (∫ u in Icc (-R) R, ρ (-u)) = 1 ∧
      ∀ y, wholeLineScenery ρ y = offsetScenery (-R) R y ρ := by
  obtain ⟨R0,hR0⟩ := hc.isBounded.exists_norm_le
  let R := max R0 |x|+1
  have hR : R0 < R := by dsimp [R]; linarith [le_max_left R0 |x|]
  have hx : |x| < R := by dsimp [R]; linarith [le_max_right R0 |x|]
  have hpos : 0 ≤ R := le_trans (abs_nonneg x) hx.le
  have hs (z : ℝ) (hz : ρ z ≠ 0) : |z| < R := by
    have hb : |z| ≤ R0 := by simpa only [Real.norm_eq_abs] using hR0 z (subset_tsupport ρ hz)
    exact hb.trans_lt hR
  refine ⟨R,hx,?_,?_⟩
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => ?_)]
    · simpa only [zero_sub] using (integral_sub_left_eq_self ρ volume 0).trans hmass
    · by_contra hz
      have hb := abs_lt.mp (by simpa only [abs_neg] using hs (-u) hz)
      exact hu ⟨hb.1.le,hb.2.le⟩
  · intro y
    apply IBMOffsetTranslation.wholeLineScenery_eq_offsetScenery (-R) R y ρ (by linarith)
    intro u hu
    by_contra hz
    have hb := abs_lt.mp (hs (y-u) hz)
    exact hu ⟨by linarith,by linarith⟩

theorem variance_C2 {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) :
    ContDiff ℝ 2 (wholeLineVariance ρ) := by
  have h : ContDiff ℝ 2 (wholeLineScenery ρ) :=
    hc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ sourceScenery_locallyIntegrable
  exact h.norm_sq ℝ

/-- The global second derivative is the ORIGINAL kernel, not its square
or self-convolution. Evenness and nonnegativity are unnecessary here. -/
theorem variance_second {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (hmass : (∫ u, ρ u) = 1) (x : ℝ) :
    deriv (deriv (wholeLineVariance ρ)) x = 2*ρ x := by
  obtain ⟨R,hx,hm,he⟩ := exists_window hc hmass x
  have hv : (fun y => ‖offsetScenery (-R) R y ρ‖^2) = wholeLineVariance ρ := by
    funext y
    rw [← he y]
    rfl
  have hd := offsetVariance_second_deriv (-R) R x hρ hm
    (by linarith [(abs_lt.mp hx).2]) (by linarith [(abs_lt.mp hx).1])
  rwa [hv] at hd

theorem variance_first_window {ρ : ℝ → ℝ} {R x : ℝ} (hρ : Continuous ρ)
    (hx : |x| < R) (hm : (∫ u in Icc (-R) R, ρ (-u)) = 1)
    (he : ∀ y, wholeLineScenery ρ y = offsetScenery (-R) R y ρ) :
    deriv (wholeLineVariance ρ) x = 1-2*(∫ u in -R..-x, ρ (-u)) := by
  have hv : (fun y => ‖offsetScenery (-R) R y ρ‖^2) = wholeLineVariance ρ := by
    funext y
    rw [← he y]
    rfl
  have hd := (offsetVariance_hasDerivAt (-R) R x hρ hm
    (by linarith [(abs_lt.mp hx).2]) (by linarith [(abs_lt.mp hx).1])).deriv
  rwa [hv] at hd

theorem slope_bound {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (hpos : ∀ u, 0 ≤ ρ u) (hmass : (∫ u, ρ u) = 1) (x : ℝ) :
    ‖deriv (wholeLineVariance ρ) x‖ ≤ 1 := by
  obtain ⟨R,hx,hm,he⟩ := exists_window hc hmass x
  have hl : -R ≤ -x := by linarith [(abs_lt.mp hx).2]
  have hr : -x ≤ R := by linarith [(abs_lt.mp hx).1]
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    ((hρ.comp continuous_neg).intervalIntegrable (μ := volume) (-R) (-x))
    ((hρ.comp continuous_neg).intervalIntegrable (-x) R)
  simp only [Function.comp_def] at hsum
  rw [intervalIntegral.integral_of_le (hl.trans hr),← integral_Icc_eq_integral_Ioc,hm] at hsum
  have hleft : 0 ≤ ∫ u in -R..-x, ρ (-u) := by
    rw [intervalIntegral.integral_of_le hl]
    exact integral_nonneg fun _ => hpos _
  have hright : 0 ≤ ∫ u in -x..R, ρ (-u) := by
    rw [intervalIntegral.integral_of_le hr]
    exact integral_nonneg fun _ => hpos _
  rw [variance_first_window hρ hx hm he,Real.norm_eq_abs,abs_le]
  constructor <;> linarith

theorem slope_positive_bulk {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (hmass : (∫ u, ρ u) = 1) {B x : ℝ}
    (hs : ∀ z, ρ z ≠ 0 → |z| ≤ B) (hx : B < x) : deriv (wholeLineVariance ρ) x = 1 := by
  obtain ⟨R,hR,hm,he⟩ := exists_window hc hmass x
  rw [variance_first_window hρ hR hm he]
  have hz : (∫ u in -R..-x, ρ (-u)) = 0 := by
    rw [intervalIntegral.integral_of_le (by linarith [(abs_lt.mp hR).2])]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    by_contra hn
    have hb := (le_abs_self (-u)).trans (hs (-u) hn)
    linarith [hu.2]
  rw [hz]
  ring

theorem slope_negative_bulk {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (hmass : (∫ u, ρ u) = 1) {B x : ℝ}
    (hs : ∀ z, ρ z ≠ 0 → |z| ≤ B) (hx : x < -B) : deriv (wholeLineVariance ρ) x = -1 := by
  obtain ⟨R,hR,hm,he⟩ := exists_window hc hmass x
  have hl : -R ≤ -x := by linarith [(abs_lt.mp hR).2]
  have hr : -x ≤ R := by linarith [(abs_lt.mp hR).1]
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    ((hρ.comp continuous_neg).intervalIntegrable (μ := volume) (-R) (-x))
    ((hρ.comp continuous_neg).intervalIntegrable (-x) R)
  simp only [Function.comp_def] at hsum
  rw [intervalIntegral.integral_of_le (hl.trans hr),← integral_Icc_eq_integral_Ioc,hm] at hsum
  have hz : (∫ u in -x..R, ρ (-u)) = 0 := by
    rw [intervalIntegral.integral_of_le hr]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    by_contra hn
    have hb := abs_le.mp (hs (-u) hn)
    linarith [hu.1]
  rw [variance_first_window hρ hR hm he]
  linarith

end OperatorDerivativeRewrite.Foundation.IBMCompactVarianceGeometry
