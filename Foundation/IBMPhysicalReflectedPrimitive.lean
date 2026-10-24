import Foundation.IBMPhysicalPrimitiveDerivative

/-! Removing the genuine origin Dirac slope makes the reflected physical
primitive C1. This is a Banach-valued spatial theorem, not yet a stochastic
zero-quadratic-variation or bounded-variation assertion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalReflectedPrimitive
open IBMPhysicalWeakWiener IBMPhysicalPrimitiveDerivative IBMPhysicalDirac
local instance : AddCommGroup Kernel :=
  (inferInstance : NormedAddCommGroup Kernel).toAddCommGroup
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _

def corrected (r : ℝ) : Kernel := primitive |r| - |r| • dirac 0

def slope (r : ℝ) : Kernel :=
  if r ≤ 0 then dirac 0 - dirac (-r) else dirac r - dirac 0

theorem corrected_pos {r : ℝ} (hr : 0 ≤ r) :
    corrected r = primitive r - r • dirac 0 := by rw [corrected, abs_of_nonneg hr]

theorem corrected_neg {r : ℝ} (hr : r ≤ 0) :
    corrected r = primitive (-r) + r • dirac 0 := by
  rw [corrected, abs_of_nonpos hr]
  module

theorem slope_neg {r : ℝ} (hr : r ≤ 0) : slope r = dirac 0 - dirac (-r) := by
  simp only [slope, if_pos hr]

theorem slope_pos {r : ℝ} (hr : 0 ≤ r) : slope r = dirac r - dirac 0 := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    simp [slope]
  · simp [slope, not_le_of_gt hr]

theorem corrected_zero : corrected 0 = 0 := by
  rw [corrected, abs_zero, primitive_zero]
  module

theorem slope_zero : slope 0 = 0 := by simp [slope]

theorem corrected_hasDerivAt (r : ℝ) : HasDerivAt corrected (slope r) r := by
  have hp (x : ℝ) : HasDerivAt (fun y => primitive y - y • dirac 0)
      (dirac x - dirac 0) x := by
    have h := (primitive_hasDerivAt x).sub ((hasDerivAt_id x).smul_const (dirac 0))
    change HasDerivAt (fun y => primitive y - y • dirac 0)
      (dirac x - (1 : ℝ) • dirac 0) x at h
    convert h using 1
    module
  have hn (x : ℝ) : HasDerivAt (fun y => primitive (-y) + y • dirac 0)
      (dirac 0 - dirac (-x)) x := by
    have h := ((primitive_hasDerivAt (-x)).scomp x (hasDerivAt_neg x)).add
      ((hasDerivAt_id x).smul_const (dirac 0))
    change HasDerivAt (fun y => primitive (-y) + y • dirac 0)
      ((-1 : ℝ) • dirac (-x) + (1 : ℝ) • dirac 0) x at h
    convert h using 1
    module
  rcases lt_trichotomy r 0 with hr | hr | hr
  · rw [slope_neg hr.le]
    apply (hn r).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hr] with y hy
    exact corrected_neg hy.le
  · subst r
    rw [slope_zero]
    have hP : HasDerivWithinAt corrected (0 : Kernel) (Ici 0) 0 := by
      have h := (hp 0).hasDerivWithinAt.congr
        (fun y hy => corrected_pos hy) (corrected_pos (le_refl 0))
      change HasDerivWithinAt corrected (dirac 0 - dirac 0) (Ici 0) 0 at h
      convert h using 1
      module
    have hN : HasDerivWithinAt corrected (0 : Kernel) (Iic 0) 0 := by
      have h := (hn 0).hasDerivWithinAt.congr
        (fun y hy => corrected_neg hy) (corrected_neg (le_refl 0))
      change HasDerivWithinAt corrected (dirac 0 - dirac (-0)) (Iic 0) 0 at h
      simp only [neg_zero] at h
      convert h using 1
      module
    have h := hN.union hP
    rw [Iic_union_Ici] at h
    exact h.hasDerivAt (by simp)
  · rw [slope_pos hr.le]
    apply (hp r).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hr] with y hy
    exact corrected_pos hy.le

theorem slope_continuous : Continuous slope := by
  exact (continuous_const.sub (dirac_continuous.comp continuous_neg)).if_le
    (dirac_continuous.sub continuous_const) continuous_id continuous_const
    (fun r hr => by change r = 0 at hr; subst r; simp)

theorem corrected_deriv : deriv corrected = slope :=
  funext fun r => (corrected_hasDerivAt r).deriv

theorem corrected_C1 : ContDiff ℝ 1 corrected := contDiff_one_iff_deriv.mpr
  ⟨fun r => (corrected_hasDerivAt r).differentiableAt, by
    rw [corrected_deriv]
    exact slope_continuous⟩

theorem corrected_origin_bound (r : ℝ) :
    ‖corrected r‖ ≤ (‖IBMPhysicalNoiseClock.physicalDerivative‖ * Real.sqrt |r|) * |r| :=
  origin_remainder_bound (abs_nonneg r)

theorem slope_origin_bound (r : ℝ) :
    ‖slope r‖ ≤ ‖IBMPhysicalNoiseClock.physicalDerivative‖ * Real.sqrt |r| := by
  by_cases hr : r ≤ 0
  · rw [slope_neg hr, norm_sub_rev]
    simpa only [zero_sub, abs_neg, abs_of_nonpos hr, sub_zero] using
      dirac_difference_bound (-r) 0
  · rw [slope_pos (le_of_not_ge hr)]
    simpa only [zero_sub, abs_neg] using dirac_difference_bound r 0

theorem slope_sign_identity (r : ℝ) : slope r =
    BrownianSignIntegral.signum r • (dirac |r| - dirac 0) := by
  rcases lt_trichotomy r 0 with hr | hr | hr
  · rw [slope_neg hr.le, abs_of_neg hr]
    simp only [BrownianSignIntegral.signum, not_lt_of_ge hr.le, ite_false, hr, ite_true]
    module
  · subst r
    rw [slope_zero, abs_zero, BrownianSignIntegral.signum_zero]
    module
  · rw [slope_pos hr.le, abs_of_pos hr]
    simp only [BrownianSignIntegral.signum, hr, ite_true]
    module

theorem reflected_split (r : ℝ) :
    IBMPhysicalPrimitiveDerivative.primitive |r| = corrected r + |r| • dirac 0 := by
  unfold corrected
  module

end OperatorDerivativeRewrite.Foundation.IBMPhysicalReflectedPrimitive
