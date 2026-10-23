import Foundation.IBMEarlierWeightedOverlap
import Foundation.IBMSineSourceContinuity

/-! Uniform-in-mollifier overlap tails for the actual continuous Brownian clock.
The radius is strictly positive and the earlier time is strictly before the later.
These are two-time estimates, not yet a time-integrated gradient tail theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockTailOverlap
open InfiniteGaussian IBMConstructedSources IBMFoldedTransitionBound

def tail (R x : ℝ) : ℝ := if R < |x| then 1 else 0

theorem tail_measurable (R : ℝ) : Measurable (tail R) := by
  exact Measurable.ite (measurableSet_lt measurable_const continuous_abs.measurable)
    measurable_const measurable_const

theorem tail_nonneg (R x : ℝ) : 0 ≤ tail R x := by
  unfold tail
  split <;> norm_num

theorem tail_le_one (R x : ℝ) : tail R x ≤ 1 := by
  unfold tail
  split <;> norm_num

theorem tail_square_le {R : ℝ} (hR : 0 < R) (x : ℝ) :
    R ^ 2 * tail R x ≤ x ^ 2 := by
  unfold tail
  split_ifs with h
  · have hh : R ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ hR.le h.le 2
    simpa only [mul_one, sq_abs] using hh
  · simp only [mul_zero]; positivity

theorem clock_tail_integrable (R : ℝ) (s : ℝ≥0) :
    Integrable (fun Y => tail R (clockPath Y s)) gaussianProduct := by
  have hm : Measurable (fun Y => clockPath Y s) :=
    (ContinuousMap.measurable_eval s).comp clockPath_measurable
  exact Integrable.of_bound ((tail_measurable R).comp hm).aestronglyMeasurable 1
    (ae_of_all _ fun Y => by
      simpa only [Real.norm_of_nonneg (tail_nonneg R _)] using tail_le_one R _)

theorem clock_tail_le {R : ℝ} (hR : 0 < R) (s : ℝ≥0) :
    (∫ Y, tail R (clockPath Y s) ∂gaussianProduct) ≤ (s : ℝ) / R ^ 2 := by
  have hh := integral_mono ((clock_tail_integrable R s).const_mul (R ^ 2))
    (IBMSineSourceContinuity.clock_square_integrable s)
    (fun Y => tail_square_le hR (clockPath Y s))
  rw [integral_const_mul, IBMSineSourceContinuity.clock_square_integral] at hh
  exact (le_div_iff₀ (sq_pos_of_pos hR)).mpr (by nlinarith [hh])

/-- All widths n,m share the same physical radius bound. No independence
between the earlier clock and its tail event is asserted. -/
theorem clock_tail_overlap_le (n m : ℕ) {R : ℝ} (hR : 0 < R)
    (s t : ℝ≥0) (hst : s < t) :
    (∫ Y, tail R (clockPath Y s) *
      overlap n m |clockPath Y s| |clockPath Y t| ∂gaussianProduct) ≤
        2 * peak (nndist (t : ℝ) (s : ℝ)) * ((s : ℝ) / R ^ 2) := by
  exact (IBMEarlierWeightedOverlap.clockPath_weighted_le n m s t hst (tail R)
    (tail_measurable R) (tail_nonneg R) (tail_le_one R)).trans
      (mul_le_mul_of_nonneg_left (clock_tail_le hR s)
        (mul_nonneg (by norm_num) (peak_nonneg _)))

theorem clock_tail_overlap_integrable (n m : ℕ) (R : ℝ) (s t : ℝ≥0) :
    Integrable (fun Y => tail R (clockPath Y s) *
      overlap n m |clockPath Y s| |clockPath Y t|) gaussianProduct := by
  obtain ⟨M,_,hM⟩ := overlap_bounded n m
  have hc (r : ℝ≥0) : Measurable (fun Y => |clockPath Y r|) :=
    continuous_abs.measurable.comp
      ((ContinuousMap.measurable_eval r).comp clockPath_measurable)
  have hw : Measurable (fun Y => tail R (clockPath Y s)) :=
    (tail_measurable R).comp
      ((ContinuousMap.measurable_eval s).comp clockPath_measurable)
  apply Integrable.of_bound
    ((hw.mul ((overlap_continuous n m).measurable.comp
      ((hc s).prodMk (hc t)))).aestronglyMeasurable) M
  exact ae_of_all _ fun Y => by
    change ‖tail R (clockPath Y s) *
      overlap n m |clockPath Y s| |clockPath Y t|‖ ≤ M
    rw [Real.norm_of_nonneg (mul_nonneg (tail_nonneg R _) (overlap_nonneg _ _ _ _))]
    exact (mul_le_mul (tail_le_one R _) (hM _ _)
      (overlap_nonneg _ _ _ _) zero_le_one).trans_eq (one_mul _)

/-- The nonlinear covariance correction +4 is retained in the uniform tail. -/
theorem clock_tail_envelope_le (n m : ℕ) {R : ℝ} (hR : 0 < R)
    (s t : ℝ≥0) (hst : s < t) :
    (∫ Y, tail R (clockPath Y s) *
      (overlap n m |clockPath Y s| |clockPath Y t| + 4) ∂gaussianProduct) ≤
        (2 * peak (nndist (t : ℝ) (s : ℝ)) + 4) * ((s : ℝ) / R ^ 2) := by
  simp_rw [mul_add]
  rw [integral_add (clock_tail_overlap_integrable n m R s t)
    ((clock_tail_integrable R s).mul_const 4), integral_mul_const]
  have h := clock_tail_overlap_le n m hR s t hst
  have ht := mul_le_mul_of_nonneg_right (clock_tail_le hR s) (by norm_num : (0:ℝ) ≤ 4)
  nlinarith [h,ht]

end OperatorDerivativeRewrite.Foundation.IBMClockTailOverlap
