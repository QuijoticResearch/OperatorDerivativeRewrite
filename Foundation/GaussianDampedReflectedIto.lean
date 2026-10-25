import Foundation.GaussianReflectedC2Ito

/-! Actual reflected Ito for exponential damping. A global C2 extension with
bounded derivatives discharges the original reflected theorem's hypotheses.
The local-time mass is the preexisting constructed Brownian mass path. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianDampedReflectedIto
open InfiniteGaussian GaussianTimeProcess GaussianPredictableFull

def extension (c x : ℝ) : ℝ :=
  if x < 0 then Real.exp (c * x) - 2 * c * x else Real.exp (-c * x)

def slope (c x : ℝ) : ℝ :=
  if x < 0 then c * Real.exp (c * x) - 2 * c else -c * Real.exp (-c * x)

def curvature (c x : ℝ) : ℝ := c ^ 2 * Real.exp (-c * |x|)

theorem extension_nonneg (c : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    extension c x = Real.exp (-c * x) := by simp [extension, not_lt.mpr hx]

theorem extension_zero (c : ℝ) : extension c 0 = 1 := by simp [extension]

theorem slope_zero (c : ℝ) : slope c 0 = -c := by simp [slope]

theorem slope_nonneg (c : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    slope c x = -c * Real.exp (-c * x) := by simp [slope, not_lt.mpr hx]

theorem extension_hasDerivAt (c x : ℝ) : HasDerivAt (extension c) (slope c x) x := by
  have hp (x : ℝ) : HasDerivAt (fun y => Real.exp (-c * y))
      (-c * Real.exp (-c * x)) x := by
    convert (((hasDerivAt_id x).const_mul (-c)).exp) using 1 <;>
      simp only [id_eq] <;> ring
  have hn (x : ℝ) : HasDerivAt (fun y => Real.exp (c * y) - 2 * c * y)
      (c * Real.exp (c * x) - 2 * c) x := by
    convert (((hasDerivAt_id x).const_mul c).exp).sub
      ((hasDerivAt_id x).const_mul (2 * c)) using 1 <;>
      simp only [id_eq] <;> ring
    funext y
    dsimp
    ring
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [slope, ite_eq_left hx]
    apply (hn x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    simp [extension, hy]
  · subst x
    rw [slope_zero]
    apply ReflectedC2Primitive.glue_zero
      (p := fun y => Real.exp (-c * y))
      (n := fun y => Real.exp (c * y) - 2 * c * y)
      (by simpa using hp 0) (by convert hn 0 using 1 <;> simp <;> ring)
    · intro y hy
      exact extension_nonneg c hy
    · intro y hy
      rcases hy.lt_or_eq with hy | hy
      · simp [extension, hy]
      · subst y
        simp [extension]
  · rw [slope, ite_eq_right (not_lt.mpr hx.le)]
    apply (hp x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact extension_nonneg c hy.le

theorem slope_hasDerivAt (c x : ℝ) : HasDerivAt (slope c) (curvature c x) x := by
  have hp (x : ℝ) : HasDerivAt (fun y => -c * Real.exp (-c * y))
      (c ^ 2 * Real.exp (-c * x)) x := by
    convert ((((hasDerivAt_id x).const_mul (-c)).exp).const_mul (-c)) using 1 <;>
      simp only [id_eq] <;> ring
  have hn (x : ℝ) : HasDerivAt (fun y => c * Real.exp (c * y) - 2 * c)
      (c ^ 2 * Real.exp (c * x)) x := by
    convert ((((hasDerivAt_id x).const_mul c).exp).const_mul c).sub_const (2 * c)
      using 1 <;>
      simp only [id_eq] <;> ring
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [curvature, abs_of_neg hx]
    have he : -c * -x = c * x := by ring
    rw [he]
    apply (hn x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    simp [slope, hy]
  · subst x
    simp only [curvature, abs_zero, mul_zero, Real.exp_zero, mul_one]
    apply ReflectedC2Primitive.glue_zero
      (p := fun y => -c * Real.exp (-c * y))
      (n := fun y => c * Real.exp (c * y) - 2 * c)
      (by simpa using hp 0) (by simpa using hn 0)
    · intro y hy
      simp [slope, not_lt.mpr hy]
    · intro y hy
      rcases hy.lt_or_eq with hy | hy
      · simp [slope, hy]
      · subst y
        simp [slope]
        ring
  · rw [curvature, abs_of_pos hx]
    apply (hp x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp [slope, not_lt.mpr hy.le]

theorem extension_deriv (c : ℝ) : deriv (extension c) = slope c :=
  funext fun x => (extension_hasDerivAt c x).deriv

theorem extension_second (c : ℝ) : deriv (deriv (extension c)) = curvature c := by
  rw [extension_deriv]
  exact funext fun x => (slope_hasDerivAt c x).deriv

theorem extension_C2 (c : ℝ) : ContDiff ℝ 2 (extension c) := by
  have hs : ContDiff ℝ 1 (slope c) := contDiff_one_iff_deriv.mpr
    ⟨fun x => (slope_hasDerivAt c x).differentiableAt, by
      rw [show deriv (slope c) = curvature c from funext fun x => (slope_hasDerivAt c x).deriv]
      unfold curvature
      fun_prop⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨fun x => (extension_hasDerivAt c x).differentiableAt,
    by simp, by rw [extension_deriv]; exact hs⟩

theorem slope_bound {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : ‖slope c x‖ ≤ 2 * c := by
  rw [Real.norm_eq_abs]
  by_cases hx : x < 0
  · rw [slope, ite_eq_left hx]
    have he := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hc hx.le)
    have hp := Real.exp_pos (c * x)
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hc hp.le, mul_le_mul_of_nonneg_left he hc]
  · rw [slope, ite_eq_right hx, abs_mul, abs_neg, abs_of_nonneg hc,
      abs_of_pos (Real.exp_pos _)]
    have he := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (le_of_not_gt hx))
    nlinarith [mul_le_mul_of_nonneg_left he hc]

theorem curvature_bound {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : ‖curvature c x‖ ≤ c ^ 2 := by
  rw [curvature, norm_mul, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (abs_nonneg x)))
      (sq_nonneg c)).trans_eq (mul_one _)

def running (c : ℝ) (hc : 0 ≤ c) (T : ℝ≥0) : fullPredictable :=
  GaussianReflectedC2Ito.running (extension c) (extension_C2 c)
    ⟨c ^ 2, sq_nonneg c⟩ (fun x => by rw [extension_second]; exact curvature_bound hc x) T

theorem running_actual (c : ℝ) (hc : 0 ≤ c) (T : ℝ≥0) :
    (running c hc T : GaussianTimeProductL2.TimeProbabilityL2)
      =ᵐ[GaussianTimeProductL2.timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z =>
        -c * BrownianSignIntegral.signum (BrownianClockWeightedEnergy.sigma z) *
          Real.exp (-c * |BrownianClockWeightedEnergy.sigma z|)) := by
  have hh := GaussianReflectedC2Ito.running_coeFn (extension c) (extension_C2 c)
    ⟨c ^ 2, sq_nonneg c⟩
    (fun x => by rw [extension_second]; exact curvature_bound hc x) T
  filter_upwards [hh] with z hz
  change (running c hc T : GaussianTimeProductL2.TimeProbabilityL2) z = _ at hz
  rw [hz]
  by_cases h : z ∈ PredictableRealL2.horizon T
  · simp only [indicator_of_mem h, extension_deriv, slope_nonneg c (abs_nonneg _)]
    ring
  · simp [h]

theorem actual_ito (c : ℝ) (hc : 0 ≤ c) (T : ℝ≥0) :
    (fun Y => Real.exp (-c * |IBMConstructedSources.clockPath Y T|) - 1)
      =ᵐ[gaussianProduct] fun Y => itoIntegral (running c hc T) Y -
        c * BrownianMassContinuousLimit.limitPath Y T +
        (c ^ 2 / 2) * ∫ s in (0 : ℝ)..(T : ℝ),
          Real.exp (-c * |IBMConstructedSources.clockPath Y s.toNNReal|) := by
  have h1 : ∀ x, ‖deriv (deriv (extension c)) x‖ ≤ (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0) := by
    intro x
    rw [extension_second]
    exact curvature_bound hc x
  have h0 : ∀ x, ‖deriv (extension c) x‖ ≤ (⟨2 * c, by positivity⟩ : ℝ≥0) := by
    intro x
    rw [extension_deriv]
    exact slope_bound hc x
  have hi := GaussianReflectedC2Ito.reflected_ito_pathwise (extension c) (extension_C2 c)
    ⟨c ^ 2, sq_nonneg c⟩ h1 ⟨2 * c, by positivity⟩ h0 T
  filter_upwards [hi] with Y hY
  change _ = itoIntegral (running c hc T) Y + _ + _ at hY
  rw [extension_second] at hY
  simp only [extension_nonneg c (abs_nonneg _), extension_zero,
    extension_deriv, slope_zero, curvature, abs_abs] at hY
  rw [intervalIntegral.integral_const_mul] at hY
  linear_combination hY

end OperatorDerivativeRewrite.Foundation.GaussianDampedReflectedIto
