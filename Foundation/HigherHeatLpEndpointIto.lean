import Foundation.HigherHeatObservableEndpoint
import Foundation.HigherHeatLpObservableIto

/-! The actual deterministic-control observable Ito equation, including zero accumulated clock. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.HigherHeatLpEndpointIto
open HigherHeatLpControls HigherHeatLpTimeChange HigherHeatLpForwardEquation
open HigherHeatSchwartzCalculus HigherHeatSpatialGenerator HigherHeatLpObservableIto
open HigherHeatObservableEndpoint

theorem heatLaw_mean (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (f : 𝓢(ℝ, ℂ)) :
    (∫ᵛ y, f y ∂<•HigherHeatStepIntegralRealization.heatLaw m hm T) = mean m T f := by
  by_cases hT : 0 < T
  · rw [HigherHeatStepIntegralRealization.heatLaw, dif_pos hT]
    exact (mean_eq_signed_integral m hm T hT f).symm
  · have hz : T = 0 := le_antisymm (le_of_not_gt hT) bot_le
    subst T
    rw [HigherHeatStepIntegralRealization.heatLaw, dif_neg (by simp),
      HigherHeatStepIntegralRealization.zeroLaw, VectorMeasure.integral_toSignedMeasure,
      integral_dirac, mean_zero]

theorem expectation_eq_mean (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (f : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 ≤ t) :
    expectation m u f t = mean m (primitive m u t).toNNReal f := by
  have hA : 0 ≤ primitive m u t :=
    intervalIntegral.integral_nonneg_of_forall ht (fun _ => by positivity)
  have hc : clock m (restricted m u 0 t) = (primitive m u t).toNNReal := by
    apply NNReal.eq
    rw [restricted_clock, Real.coe_toNNReal _ hA]
    exact (intervalIntegral.integral_of_le ht).symm
  unfold expectation marginal
  rw [hc, heatLaw_mean]

theorem expectation_eq_extension (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (f : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 ≤ t) :
    expectation m u f t = extension m f (primitive m u t) := by
  have hA : 0 ≤ primitive m u t :=
    intervalIntegral.integral_nonneg_of_forall ht (fun _ => by positivity)
  rw [extension_eq_mean m h.out f (primitive m u t) hA]
  exact expectation_eq_mean m u f t ht

theorem observable_generator (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (f : 𝓢(ℝ, ℂ)) : ∀ᵐ t, 0 < t →
      HasDerivAt (expectation m u f)
        ((‖u t‖^(2*m) : ℂ) * expectation m u (differential m f) t) t := by
  filter_upwards [primitive_ae_derivative m u] with t hd ht
  have he : expectation m u f =ᶠ[𝓝 t]
      (fun s => extension m f (primitive m u s)) :=
    (eventually_gt_nhds ht).mono (fun s hs => expectation_eq_extension m u f s hs.le)
  have hD := (extension_hasDerivAt m h.out f (primitive m u t)).scomp t hd
  have hE := hD.congr_of_eventuallyEq he
  rw [← expectation_eq_mean m u (differential m f) t ht.le] at hE
  convert hE using 1 <;> simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_pow]

theorem observable_ito (m : ℕ) [h : Fact (0 < m)] (u : Control m) (f : 𝓢(ℝ, ℂ)) :
    ∀ᵐ t, 0 < t → HasDerivAt (expectation m u f)
      ((‖u t‖^(2*m) : ℂ) * (-1 : ℂ)^(m+1) *
        expectation m u (jet (2*m) f) t) t := by
  filter_upwards [observable_generator m u f] with t hd ht
  have he := hd ht
  rw [expectation_eq_mean m u (differential m f) t ht.le, differential,
    HigherHeatObservableIto.mean_smul,
    ← expectation_eq_mean m u (jet (2*m) f) t ht.le] at he
  simpa only [mul_assoc] using he

end OperatorDerivativeRewrite.Foundation.HigherHeatLpEndpointIto
