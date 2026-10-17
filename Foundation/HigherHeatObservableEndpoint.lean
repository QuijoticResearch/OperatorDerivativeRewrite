import Foundation.HigherHeatObservableIto
import Foundation.HigherHeatSchwartzContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! A genuine C1 extension of higher-heat Schwartz expectations through zero heat time. -/
noncomputable section
open MeasureTheory FourierTransform Set
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatObservableEndpoint
open HigherHeatSchwartzCalculus HigherHeatSpatialGenerator HigherHeatObservableIto
open HigherHeatSchwartzContinuity

theorem mean_zero (m : ℕ) (f : 𝓢(ℝ, ℂ)) : mean m 0 f = f 0 := by
  rw [← inverse_phase f 0]
  simp only [mean, HigherHeatL2.symbol_zero, HigherHeatBackwardFourier.phase_zero, mul_one]

theorem mean_real_continuous (m : ℕ) (hm : 0 < m) (f : 𝓢(ℝ, ℂ)) :
    Continuous (fun t : ℝ => mean m t.toNNReal f) :=
  (mean_continuous m hm f).comp continuous_real_toNNReal

theorem mild_identity (m : ℕ) (hm : 0 < m) (f : 𝓢(ℝ, ℂ)) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, mean m t.toNNReal (differential m f)) =
      mean m T.toNNReal f - mean m 0 f := by
  simpa only [Real.toNNReal_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
      (mean_real_continuous m hm f).continuousOn
      (fun t ht => observable_hasDerivAt m f t ht.1)
      ((mean_real_continuous m hm (differential m f)).intervalIntegrable 0 T)

def extension (m : ℕ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  mean m 0 f + ∫ s in (0 : ℝ)..t, mean m s.toNNReal (differential m f)

theorem extension_eq_mean (m : ℕ) (hm : 0 < m) (f : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 ≤ t) :
    extension m f t = mean m t.toNNReal f := by
  rw [extension, mild_identity m hm f t ht]
  abel

theorem extension_hasDerivAt (m : ℕ) (hm : 0 < m) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    HasDerivAt (extension m f) (mean m t.toNNReal (differential m f)) t := by
  have hc := mean_real_continuous m hm (differential m f)
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add _

end OperatorDerivativeRewrite.Foundation.HigherHeatObservableEndpoint
