import Foundation.HigherHeatLpEndpointIto
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! Actual control-dependent Schwartz expectations are absolutely continuous, including flat clocks. -/
noncomputable section
open MeasureTheory Set FourierTransform
open scoped NNReal ENNReal Topology SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.HigherHeatLpAbsoluteContinuity
open HigherHeatSchwartzCalculus HigherHeatSpatialGenerator HigherHeatObservableEndpoint
open HigherHeatLpControls HigherHeatLpTimeChange HigherHeatLpForwardEquation
open HigherHeatLpObservableIto HigherHeatLpEndpointIto

def bound (m : ℕ) (f : 𝓢(ℝ, ℂ)) : ℝ≥0 :=
  ⟨∫ ξ, ‖𝓕 (differential m f) ξ‖, integral_nonneg (fun _ => norm_nonneg _)⟩

theorem extension_lipschitz (m : ℕ) (hm : 0 < m) (f : 𝓢(ℝ, ℂ)) :
    LipschitzWith (bound m f) (extension m f) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (extension_hasDerivAt m hm f t).differentiableAt)
  intro t
  rw [(extension_hasDerivAt m hm f t).deriv]
  exact_mod_cast mean_bound m t.toNNReal (differential m f)

theorem primitive_ac (m : ℕ) [Fact (0 < m)] (u : Control m) (T : ℝ) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (primitive m u) 0 T :=
  (power_integrable m u).intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
    (by simpa only [uIcc_of_le hT] using (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩))

theorem expectation_ac (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (f : 𝓢(ℝ, ℂ)) (T : ℝ) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (expectation m u f) 0 T := by
  have hc := (extension_lipschitz m h.out f).comp_absolutelyContinuousOnInterval
    (primitive_ac m u T hT)
  apply hc.congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  exact (expectation_eq_extension m u f t ht.1).symm

end OperatorDerivativeRewrite.Foundation.HigherHeatLpAbsoluteContinuity
