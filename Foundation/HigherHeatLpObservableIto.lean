import Foundation.HigherHeatLpForwardEquation
import Foundation.HigherHeatObservableIto

/-! Higher-order observable Ito equations for actual interval-control signed distributions. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.HigherHeatLpObservableIto
open HigherHeatLpControls HigherHeatLpTimeChange HigherHeatLpForwardEquation
open HigherHeatSchwartzCalculus HigherHeatSchwartzTransition

def expectation (m : ℕ) [Fact (0 < m)] (u : Control m) (f : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  ∫ᵛ y, f y ∂<•marginal m (restricted m u 0 t)

theorem expectation_eq_mean (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (f : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 ≤ t) (hA : 0 < primitive m u t) :
    expectation m u f t = mean m (primitive m u t).toNNReal f := by
  have hc : clock m (restricted m u 0 t) = (primitive m u t).toNNReal := by
    apply NNReal.eq
    rw [restricted_clock, Real.coe_toNNReal _ hA.le]
    exact (intervalIntegral.integral_of_le ht).symm
  unfold expectation marginal
  rw [hc, HigherHeatStepIntegralRealization.heatLaw, dif_pos (Real.toNNReal_pos.mpr hA)]
  exact (mean_eq_signed_integral m h.out _ (Real.toNNReal_pos.mpr hA) f).symm

theorem observable_ito (m : ℕ) [h : Fact (0 < m)] (u : Control m) (f : 𝓢(ℝ, ℂ)) :
    ∀ᵐ t, 0 < t → 0 < primitive m u t →
      HasDerivAt (expectation m u f)
        ((‖u t‖ ^ (2*m) : ℂ) * (-1 : ℂ) ^ (m+1) *
          expectation m u (HigherHeatSpatialGenerator.jet (2*m) f) t) t := by
  filter_upwards [primitive_ae_derivative m u] with t hd ht hA
  have he : expectation m u f =ᶠ[𝓝 t]
      (fun s => mean m (primitive m u s).toNNReal f) := by
    have hp : Continuous (primitive m u) := (power_integrable m u).continuous_primitive 0
    filter_upwards [eventually_gt_nhds ht,
      hp.continuousAt.eventually (eventually_gt_nhds hA)] with s hs hAs
    exact expectation_eq_mean m u f s hs.le hAs
  have hD := (HigherHeatObservableIto.observable_ito m f (primitive m u t) hA).scomp t hd
  have hE := hD.congr_of_eventuallyEq he
  rw [← expectation_eq_mean m u (HigherHeatSpatialGenerator.jet (2*m) f) t ht.le hA] at hE
  convert hE using 1 <;> simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_pow]
  ring

end OperatorDerivativeRewrite.Foundation.HigherHeatLpObservableIto
