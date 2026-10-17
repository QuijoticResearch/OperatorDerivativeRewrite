import Foundation.FourierPathDualControls
import Foundation.HigherHeatLpStepControls

/-! Actual conjugate-control pairings with finite measurable step functions. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualStepPairing
open FourierPathDualControls HigherHeatLpStepControls

variable {ι : Type*} [Fintype ι]

theorem pairing_step (m : ℕ) [Fact (0 < m)] (u : Control m) (s : ι → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hf : ∀ i, volume (s i) ≠ ∞) (c : ι → ℝ) :
    pairing m u (control m s hs hf c) = ∑ i, c i * ∫ x in s i, u x := by
  classical
  have hi (i : ι) : Integrable (fun x : ℝ => u x * (s i).indicator (fun _ => c i) x) :=
    (Lp.memLp u).integrable_mul (memLp_indicator_const (HigherHeatLpControls.power m)
      (hs i) (c i) (Or.inr (hf i)))
  rw [pairing_integral]
  trans ∫ x : ℝ, ∑ i, u x * (s i).indicator (fun _ => c i) x
  · apply integral_congr_ae
    filter_upwards [control_ae m s hs hf c] with x hx
    rw [hx]
    exact Finset.mul_sum _ _ _
  · rw [integral_finsetSum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    have he : (fun x : ℝ => u x * (s i).indicator (fun _ => c i) x) =
        (s i).indicator (fun x => c i * u x) := by
      funext x
      by_cases hx : x ∈ s i <;> simp [hx, mul_comm]
    rw [he, integral_indicator (hs i), integral_const_mul]

theorem step_pairing_bound (m : ℕ) [Fact (0 < m)] (u : Control m) (s : ι → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hf : ∀ i, volume (s i) ≠ ∞) (c : ι → ℝ) :
    |∑ i, c i * ∫ x in s i, u x| ≤ ‖u‖ * ‖control m s hs hf c‖ := by
  rw [← pairing_step m u s hs hf c]
  exact pairing_bound m u _

end OperatorDerivativeRewrite.Foundation.FourierPathDualStepPairing
