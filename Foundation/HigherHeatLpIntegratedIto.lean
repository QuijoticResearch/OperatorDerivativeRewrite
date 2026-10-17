import Foundation.HigherHeatLpAbsoluteContinuity
import Foundation.ComplexAbsoluteContinuousFTC

/-! The genuine integrated observable Ito identity for arbitrary actual Lp controls. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.HigherHeatLpIntegratedIto
open HigherHeatLpControls HigherHeatLpTimeChange HigherHeatLpForwardEquation
open HigherHeatSchwartzCalculus HigherHeatSpatialGenerator HigherHeatObservableEndpoint
open HigherHeatLpObservableIto HigherHeatLpEndpointIto HigherHeatLpAbsoluteContinuity

def driftExtension (m : ℕ) [Fact (0 < m)] (u : Control m) (f : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  (‖u t‖^(2*m) : ℂ) * mean m (primitive m u t).toNNReal (differential m f)

theorem drift_integrable (m : ℕ) [h : Fact (0 < m)] (u : Control m) (f : 𝓢(ℝ, ℂ)) :
    Integrable (driftExtension m u f) := by
  have hc : Continuous (fun t : ℝ => mean m (primitive m u t).toNNReal (differential m f)) :=
    (mean_real_continuous m h.out (differential m f)).comp
      ((power_integrable m u).continuous_primitive 0)
  have hm : AEStronglyMeasurable[Real.measureSpace.toMeasurableSpace]
      (driftExtension m u f) volume := by
    change AEStronglyMeasurable[Real.measureSpace.toMeasurableSpace] (fun t : ℝ =>
      (‖u t‖ : ℂ)^(2*m) * mean m (primitive m u t).toNNReal (differential m f)) volume
    have hh := (Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable u).norm.pow (2*m))).mul hc.aestronglyMeasurable
    apply hh.congr
    exact Eventually.of_forall (fun t => by
      change ((‖u t‖^(2*m) : ℝ) : ℂ) * _ = (‖u t‖ : ℂ)^(2*m) * _
      rw [Complex.ofReal_pow])
  apply ((power_integrable m u).const_mul (bound m f : ℝ)).mono' hm
  exact Eventually.of_forall (fun t => by
    rw [driftExtension, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    calc
      _ ≤ ‖u t‖^(2*m) * (bound m f : ℝ) :=
        mul_le_mul_of_nonneg_left (mean_bound m _ (differential m f)) (by positivity)
      _ = _ := mul_comm _ _)

theorem drift_eq_actual (m : ℕ) [Fact (0 < m)] (u : Control m) (f : 𝓢(ℝ, ℂ))
    (t : ℝ) (ht : 0 ≤ t) : driftExtension m u f t =
      (‖u t‖^(2*m) : ℂ) * expectation m u (differential m f) t := by
  rw [driftExtension, HigherHeatLpEndpointIto.expectation_eq_mean m u (differential m f) t ht]

theorem integrated_generator (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (f : 𝓢(ℝ, ℂ)) (T : ℝ) (hT : 0 ≤ T) :
    expectation m u f T - f 0 =
      ∫ t in (0 : ℝ)..T, (‖u t‖^(2*m) : ℂ) * expectation m u (differential m f) t := by
  have hd : ∀ᵐ t, t ∈ uIoc (0 : ℝ) T →
      HasDerivAt (expectation m u f) (driftExtension m u f t) t := by
    filter_upwards [observable_generator m u f] with t ht hmem
    rw [uIoc_of_le hT] at hmem
    rw [drift_eq_actual m u f t hmem.1.le]
    exact ht hmem.1
  have he := ComplexAbsoluteContinuousFTC.integral_eq_sub (expectation m u f)
    (driftExtension m u f) 0 T (expectation_ac m u f T hT) hd
    (drift_integrable m u f).intervalIntegrable
  have hzero : expectation m u f 0 = f 0 := by
    rw [HigherHeatLpEndpointIto.expectation_eq_mean m u f 0 le_rfl]
    simp only [primitive, intervalIntegral.integral_same, Real.toNNReal_zero, mean_zero]
  rw [hzero] at he
  rw [← he]
  apply intervalIntegral.integral_congr_ae
  exact Eventually.of_forall (fun t ht => by
    rw [uIoc_of_le hT] at ht
    exact drift_eq_actual m u f t ht.1.le)

theorem integrated_ito (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (f : 𝓢(ℝ, ℂ)) (T : ℝ) (hT : 0 ≤ T) :
    expectation m u f T - f 0 =
      ∫ t in (0 : ℝ)..T, (‖u t‖^(2*m) : ℂ) * (-1 : ℂ)^(m+1) *
        expectation m u (jet (2*m) f) t := by
  rw [integrated_generator m u f T hT]
  apply intervalIntegral.integral_congr_ae
  exact Eventually.of_forall (fun t ht => by
    rw [uIoc_of_le hT] at ht
    rw [HigherHeatLpEndpointIto.expectation_eq_mean m u (differential m f) t ht.1.le, differential,
      HigherHeatObservableIto.mean_smul,
      ← HigherHeatLpEndpointIto.expectation_eq_mean m u (jet (2*m) f) t ht.1.le, mul_assoc])

end OperatorDerivativeRewrite.Foundation.HigherHeatLpIntegratedIto
