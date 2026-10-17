import Foundation.HigherHeatLpPropagator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! The almost-everywhere forward equation for actual interval-control Fourier expectations. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatLpForwardEquation
open HigherHeatLpControls HigherHeatLpTimeChange

def primitive (m : ℕ) [Fact (0 < m)] (u : Control m) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..t, ‖u x‖ ^ (2*m)

theorem primitive_ae_derivative (m : ℕ) [Fact (0 < m)] (u : Control m) :
    ∀ᵐ t, HasDerivAt (primitive m u) (‖u t‖ ^ (2*m)) t :=
  (_root_.LocallyIntegrable.ae_hasDerivAt_integral
    (power_integrable m u).locallyIntegrable).mono (fun _ ht => ht 0)

def curve (m : ℕ) [Fact (0 < m)] (u : Control m) (ξ t : ℝ) : ℂ :=
  (Real.exp (-(primitive m u t) * (2 * Real.pi * ξ) ^ (2*m)) : ℝ)

def actual (m : ℕ) [Fact (0 < m)] (u : Control m) (ξ t : ℝ) : ℂ :=
  ∫ᵛ y, HigherHeatCylinderFourier.phase ξ y ∂<•marginal m (restricted m u 0 t)

theorem actual_eq_curve (m : ℕ) [Fact (0 < m)] (u : Control m) (ξ t : ℝ) (ht : 0 ≤ t) :
    actual m u ξ t = curve m u ξ t := by
  unfold actual
  rw [marginal_fourier]
  have he := time_eq_clock m u (⟨t, ht⟩ : ℝ≥0)
  change time m u ⟨t, ht⟩ = clock m (restricted m u 0 t) at he
  rw [← he]
  rfl

theorem curve_ae_derivative (m : ℕ) [Fact (0 < m)] (u : Control m) (ξ : ℝ) :
    ∀ᵐ t, HasDerivAt (curve m u ξ)
      (((-(2 * Real.pi * ξ) ^ (2*m) * ‖u t‖ ^ (2*m) : ℝ) : ℂ) * curve m u ξ t) t := by
  filter_upwards [primitive_ae_derivative m u] with t ht
  have hd := ((ht.neg.mul_const ((2 * Real.pi * ξ) ^ (2*m))).exp).ofReal_comp
  have hd' : HasDerivAt (curve m u ξ)
      ((Real.exp (-(primitive m u t) * (2 * Real.pi * ξ) ^ (2*m)) *
        (-‖u t‖ ^ (2*m) * (2 * Real.pi * ξ) ^ (2*m)) : ℝ) : ℂ) t := hd
  convert hd' using 1
  dsimp only [curve]
  push_cast
  ring

theorem actual_ae_forward_equation (m : ℕ) [Fact (0 < m)] (u : Control m) (ξ : ℝ) :
    ∀ᵐ t, 0 < t → HasDerivAt (actual m u ξ)
      (((-(2 * Real.pi * ξ) ^ (2*m) * ‖u t‖ ^ (2*m) : ℝ) : ℂ) * actual m u ξ t) t := by
  filter_upwards [curve_ae_derivative m u ξ] with t hd ht
  have he : actual m u ξ =ᶠ[𝓝 t] curve m u ξ :=
    (eventually_gt_nhds ht).mono (fun s hs => actual_eq_curve m u ξ s hs.le)
  rw [actual_eq_curve m u ξ t ht.le]
  exact hd.congr_of_eventuallyEq he

end OperatorDerivativeRewrite.Foundation.HigherHeatLpForwardEquation
