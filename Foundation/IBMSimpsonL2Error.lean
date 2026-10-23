import Foundation.IBMFifthVariationL2
import Foundation.IBMSimpsonFifthError
import Foundation.IBMActualSimpson

/-! Unclipped actual signed spatial Simpson errors vanish in genuine L2
for C5 primitives with globally bounded fifth derivative. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMSimpsonL2Error
open IBMSourceLaws IBMConstructedSources IBMActualSimpson IBMUniformFifthRemainder
open IBMFifthVariationL2
attribute [local irreducible] ibmValue clockPath sceneryPath

theorem error_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0) (n : ℕ) (ω : JointSample) :
    |error f T n ω| ≤ M * fifth T n ω := by
  rw [finite_error_identity]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [fifth, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => IBMSimpsonFifthError.error_bound f hf M hM _ _

theorem error_memLp (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0) (n : ℕ) :
    MemLp (error f T n) 2 jointMeasure := by
  apply ((fifth_memLp T n).const_mul M).mono'
    (error_measurable f (hf.of_le (by norm_num)) T n).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs] using error_bound f hf M hM T n ω

def errorClass (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0) (n : ℕ) : Lp ℝ 2 jointMeasure :=
  (error_memLp f hf M hM T n).toLp (error f T n)

theorem errorClass_actual_ae (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0) (n : ℕ) :
    errorClass f hf M hM T n =ᵐ[jointMeasure] error f T n :=
  (error_memLp f hf M hM T n).coeFn_toLp

theorem errorClass_norm_le (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0) (n : ℕ) :
    ‖errorClass f hf M hM T n‖ ≤ M * ‖fifthClass T n‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [errorClass_actual_ae f hf M hM T n, fifthClass_actual_ae T n] with ω he hv
  rw [he, hv]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (fifth_nonneg T n ω)] using
    error_bound f hf M hM T n ω

/-- Actual stochastic L2 convergence, without clipping or an assumed moment bound. -/
theorem errorClass_tendsto (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (T : ℝ≥0) :
    Tendsto (errorClass f hf M hM T) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (errorClass_norm_le f hf M hM T)
  simpa using ((tendsto_zero_iff_norm_tendsto_zero.mp (fifthClass_tendsto T)).const_mul M)

end OperatorDerivativeRewrite.Foundation.IBMSimpsonL2Error
