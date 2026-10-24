import Foundation.IBMPhysicalReflectedPrimitive

/-! Physical Holder/Taylor estimates remain valid across the reflected origin.
These are spatial estimates for the actual primitive, not time-variation claims. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalReflectedTaylor
open IBMPhysicalWeakWiener IBMPhysicalReflectedPrimitive IBMPhysicalDirac IBMPhysicalNoiseClock
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul

theorem crossing_slope_bound {r s : ℝ} (hr : r ≤ 0) (hs : 0 ≤ s) :
    ‖slope r - slope s‖ ≤ (2*‖physicalDerivative‖) * Real.sqrt |s-r| := by
  have hA : |r| ≤ |s-r| := by
    rw [abs_of_nonpos hr, abs_of_nonneg (by linarith : 0 ≤ s-r)]
    linarith
  have hB : |s| ≤ |s-r| := by
    rw [abs_of_nonneg hs, abs_of_nonneg (by linarith : 0 ≤ s-r)]
    linarith
  have h1 := (slope_origin_bound r).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hA) (norm_nonneg _))
  have h2 := (slope_origin_bound s).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hB) (norm_nonneg _))
  have h := norm_sub_le (slope r) (slope s)
  linarith

theorem slope_holder (r s : ℝ) :
    ‖slope r - slope s‖ ≤ (2*‖physicalDerivative‖) * Real.sqrt |s-r| := by
  have hnon : 0 ≤ ‖physicalDerivative‖ * Real.sqrt |s-r| := by positivity
  rcases le_total r 0 with hr | hr <;> rcases le_total s 0 with hs | hs
  · have he : slope r - slope s = dirac (-s) - dirac (-r) := by
      rw [slope_neg hr, slope_neg hs]
      module
    rw [he]
    have h := dirac_difference_bound (-s) (-r)
    have heq : -r - -s = s-r := by ring
    rw [heq] at h
    nlinarith
  · exact crossing_slope_bound hr hs
  · have h := crossing_slope_bound hs hr
    simpa only [norm_sub_rev, abs_sub_comm] using h
  · have he : slope r - slope s = dirac r - dirac s := by
      rw [slope_pos hr, slope_pos hs]
      module
    rw [he]
    have h := dirac_difference_bound r s
    nlinarith

theorem corrected_remainder_bound {r s : ℝ} (hrs : r ≤ s) :
    ‖corrected s - corrected r - (s-r) • slope r‖ ≤
      ((2*‖physicalDerivative‖) * Real.sqrt (s-r)) * (s-r) := by
  have hd (x : ℝ) : HasDerivAt (fun y => corrected y - (y-r) • slope r)
      (slope x - slope r) x := by
    have h := (corrected_hasDerivAt x).sub
      (((hasDerivAt_id x).sub_const r).smul_const (slope r))
    change HasDerivAt (fun y => corrected y - (y-r) • slope r)
      (slope x - (1 : ℝ) • slope r) x at h
    convert h using 1
    module
  have hb (x : ℝ) (hx : x ∈ Ico r s) :
      ‖slope x - slope r‖ ≤ (2*‖physicalDerivative‖) * Real.sqrt (s-r) := by
    apply (slope_holder x r).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.sqrt_le_sqrt
    rw [abs_of_nonpos (by linarith [hx.1])]
    linarith [hx.2]
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x (_hx : x ∈ Icc r s) => (hd x).hasDerivWithinAt) hb s
      (right_mem_Icc.mpr hrs)
  have he : (corrected s - (s-r) • slope r) -
      (corrected r - (r-r) • slope r) = corrected s - corrected r - (s-r) • slope r := by
    module
  rw [he] at h
  exact h

theorem arbitrary_remainder_bound (r s : ℝ) :
    ‖corrected s - corrected r - (s-r) • slope r‖ ≤
      ((4*‖physicalDerivative‖) * Real.sqrt |s-r|) * |s-r| := by
  rcases le_total r s with hrs | hsr
  · have h := corrected_remainder_bound hrs
    rw [abs_of_nonneg (sub_nonneg.mpr hrs)]
    have hp : 0 ≤ ‖physicalDerivative‖ * Real.sqrt (s-r) * (s-r) := by positivity
    nlinarith
  · have he : corrected s - corrected r - (s-r) • slope r =
        -(corrected r - corrected s - (r-s) • slope s) + (r-s) • (slope r - slope s) := by
      module
    rw [he]
    have h := norm_add_le (-(corrected r - corrected s - (r-s) • slope s))
      ((r-s) • (slope r - slope s))
    rw [norm_neg, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hsr)] at h
    have h1 := corrected_remainder_bound hsr
    have h2 := mul_le_mul_of_nonneg_left (slope_holder r s) (sub_nonneg.mpr hsr)
    have hab : |s-r| = r-s := by rw [abs_of_nonpos (sub_nonpos.mpr hsr)]; ring
    rw [hab] at h2 ⊢
    nlinarith

theorem squared_remainder_bound (r s : ℝ) :
    ‖corrected s - corrected r - (s-r) • slope r‖^2 ≤
      16 * ‖physicalDerivative‖^2 * |s-r|^3 := by
  calc
    _ ≤ (((4*‖physicalDerivative‖) * Real.sqrt |s-r|) * |s-r|)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (arbitrary_remainder_bound r s) 2
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt (abs_nonneg (s-r))]
      ring

theorem clock_grid_remainder_bound {n : ℕ} (τ : Fin (n + 1) → ℝ≥0)
    (Y : InfiniteGaussian.SampleSpace) :
    (∑ i : Fin n, ‖corrected (IBMConstructedSources.clockPath Y (τ i.succ)) -
      corrected (IBMConstructedSources.clockPath Y (τ i.castSucc)) -
      (IBMConstructedSources.clockPath Y (τ i.succ) -
        IBMConstructedSources.clockPath Y (τ i.castSucc)) •
          slope (IBMConstructedSources.clockPath Y (τ i.castSucc))‖^2) ≤
      16 * ‖physicalDerivative‖^2 * ∑ i : Fin n,
        |IBMConstructedSources.clockPath Y (τ i.succ) -
          IBMConstructedSources.clockPath Y (τ i.castSucc)|^3 := by
  calc
    _ ≤ ∑ i : Fin n, 16 * ‖physicalDerivative‖^2 *
        |IBMConstructedSources.clockPath Y (τ i.succ) -
          IBMConstructedSources.clockPath Y (τ i.castSucc)|^3 :=
      Finset.sum_le_sum fun i _hi => squared_remainder_bound _ _
    _ = _ := (Finset.mul_sum _ _ _).symm

end OperatorDerivativeRewrite.Foundation.IBMPhysicalReflectedTaylor
