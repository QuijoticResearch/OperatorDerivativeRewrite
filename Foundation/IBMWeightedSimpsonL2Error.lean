import Foundation.IBMSimpsonL2Error
import Foundation.IBMTimeWeightedSimpson

/-! L2 control of actual time-weighted spatial Simpson errors.
The estimate uses only bounded weights on the time interval, not causality. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMWeightedSimpsonL2Error
open IBMSourceLaws IBMConstructedSources IBMTimeWeightedSimpson
open IBMUniformClockGridEnergy IBMContinuousQuadrature IBMUniformFifthRemainder
attribute [local irreducible] ibmValue clockPath sceneryPath

theorem weighted_error_bound (h f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M B : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0)
    (hB : ∀ t ∈ Icc 0 (T : ℝ), |h t| ≤ B) (n : ℕ) (ω : JointSample) :
    |weightedError h (deriv f) T n ω| ≤ B*M*fifth T n ω := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have he : weightedError h (deriv f) T n ω =
      ∑ i ∈ Finset.range (n+1), h (time T (n+1) i) *
        (IBMSimpsonPeano.simpson (deriv f)
          (ibmValue (grid (T/(n+1)) i) ω) (ibmValue (grid (T/(n+1)) (i+1)) ω) -
          (f (ibmValue (grid (T/(n+1)) (i+1)) ω)-f (ibmValue (grid (T/(n+1)) i) ω))) := by
    simp only [weightedError, weighted, pathSum, derivative_lineIntegral f hf1,
      sub_sub_sub_cancel_right, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [fifth, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  have hb := hB _ (time_mem T.coe_nonneg (by omega : 0 < n+1)
    (by have := Finset.mem_range.mp hi; omega : i ≤ n+1))
  have hm := IBMSimpsonFifthError.error_bound f hf M hM
    (ibmValue (grid (T/(n+1)) i) ω) (ibmValue (grid (T/(n+1)) (i+1)) ω)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl,T.coe_nonneg⟩)
  exact (mul_le_mul hb hm (abs_nonneg _) hB0).trans_eq (by ring)

theorem weighted_error_memLp (h f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M B : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0)
    (hB : ∀ t ∈ Icc 0 (T : ℝ), |h t| ≤ B) (n : ℕ) :
    MemLp (weightedError h (deriv f) T n) 2 jointMeasure := by
  apply ((IBMFifthVariationL2.fifth_memLp T n).const_mul (B*M)).mono'
    ((weighted_measurable h (deriv f) (hf.continuous_deriv (by norm_num)) T n).sub
      (pathSum_measurable h (deriv f) (hf.continuous_deriv (by norm_num)) T n)).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, weightedError] using
      weighted_error_bound h f hf M B hM T hB n ω

def errorClass (h f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M B : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0)
    (hB : ∀ t ∈ Icc 0 (T : ℝ), |h t| ≤ B) (n : ℕ) : Lp ℝ 2 jointMeasure :=
  (weighted_error_memLp h f hf M B hM T hB n).toLp _

theorem errorClass_actual_ae (h f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M B : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0)
    (hB : ∀ t ∈ Icc 0 (T : ℝ), |h t| ≤ B) (n : ℕ) :
    errorClass h f hf M B hM T hB n =ᵐ[jointMeasure] weightedError h (deriv f) T n :=
  (weighted_error_memLp h f hf M B hM T hB n).coeFn_toLp

theorem errorClass_norm_le (h f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M B : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0)
    (hB : ∀ t ∈ Icc 0 (T : ℝ), |h t| ≤ B) (n : ℕ) :
    ‖errorClass h f hf M B hM T hB n‖ ≤ B*M*‖IBMFifthVariationL2.fifthClass T n‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [errorClass_actual_ae h f hf M B hM T hB n,
    IBMFifthVariationL2.fifthClass_actual_ae T n] with ω he hv
  rw [he,hv]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (fifth_nonneg T n ω)] using
    weighted_error_bound h f hf M B hM T hB n ω

theorem errorClass_tendsto (h f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M B : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0)
    (hB : ∀ t ∈ Icc 0 (T : ℝ), |h t| ≤ B) :
    Tendsto (errorClass h f hf M B hM T hB) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (errorClass_norm_le h f hf M B hM T hB)
  simpa using ((tendsto_zero_iff_norm_tendsto_zero.mp
    (IBMFifthVariationL2.fifthClass_tendsto T)).const_mul (B*M))

end OperatorDerivativeRewrite.Foundation.IBMWeightedSimpsonL2Error
