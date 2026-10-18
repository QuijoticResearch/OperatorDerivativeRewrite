import Foundation.HigherHeatWeakTimeAdjoint
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Actual L1 step fields and exact step formulas for the bounded weak integral.
These formulas do not by themselves identify the operator with signed increment sums. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatWeakStepFields
open MeasureTheory HigherHeatAnalyticCylinderDomain HigherHeatPairedDualCausality
open HigherHeatTimeDerivative HigherHeatWeakTimeAdjoint

def step (μ : Measure ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (a : Dual) : Field μ := indicatorConstLp 1 hs hμs a

theorem step_ae (μ : Measure ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (a : Dual) :
    (step μ s hs hμs a : ℝ → Dual) =ᵐ[μ] s.indicator (fun _ => a) :=
  indicatorConstLp_coeFn

theorem step_norm (μ : Measure ℝ) (s : Set ℝ) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (a : Dual) : ‖step μ s hs hμs a‖ = ‖a‖ * μ.real s := by
  simpa only [step, ENNReal.toReal_one, div_one, Real.rpow_one] using
    (norm_indicatorConstLp (p := 1) (hs := hs) (hμs := hμs) (c := a)
      (by norm_num) (by norm_num))

theorem transpose_step (μ : Measure ℝ) (r : ℕ) (s : Set ℝ)
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (a : Dual) (G : Domain) :
    transpose μ r (step μ s hs hμs a) G =
      ∫ t in s, a (((atTime t)^r) G) ∂μ := by
  rw [transpose_apply, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [step_ae μ s hs hμs a] with t ht
  rw [ht]
  by_cases h : t ∈ s
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h, ContinuousLinearMap.zero_apply]

theorem firstChannel_step (m : ℕ) (T : ℝ≥0) (s : Set ℝ)
    (hs : MeasurableSet s) (hμs : timeMeasure s ≠ ∞) (a : Dual) (G : Domain) :
    firstChannel m T (step timeMeasure s hs hμs a) G = coefficient m T *
      ∫ t in s, a (((atTime t)^(2*m-1)) G) ∂timeMeasure := by
  change coefficient m T * transpose timeMeasure (2*m-1) (step timeMeasure s hs hμs a) G = _
  rw [transpose_step]

theorem transpose_step_constant (μ : Measure ℝ) (r : ℕ) (s : Set ℝ)
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (a : Dual) (G H : Domain)
    (h : ∀ᵐ t ∂μ.restrict s, ((atTime t)^r) G = H) :
    transpose μ r (step μ s hs hμs a) G = μ.real s * a H := by
  rw [transpose_step]
  calc
    _ = ∫ _t in s, a H ∂μ := integral_congr_ae (h.mono (fun _ ht => congrArg a ht))
    _ = _ := by simp [integral_const, measureReal_def, smul_eq_mul]

theorem firstChannel_step_bound (m : ℕ) (T : ℝ≥0) (s : Set ℝ)
    (hs : MeasurableSet s) (hμs : timeMeasure s ≠ ∞) (a : Dual) :
    ‖firstChannel m T (step timeMeasure s hs hμs a)‖ ≤
      ((2*m:ℕ):ℝ)*(T:ℝ)*(‖a‖ * timeMeasure.real s) := by
  simpa only [step_norm] using firstChannel_bound m T (step timeMeasure s hs hμs a)

end OperatorDerivativeRewrite.Foundation.HigherHeatWeakStepFields
