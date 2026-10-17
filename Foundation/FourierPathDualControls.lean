import Foundation.HigherHeatLpControls
import Foundation.FourierPathLipschitzDamping
import Mathlib.Basic.Real.ConjExponents
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! Actual conjugate-exponent time controls and their continuous direction primitives. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualControls
open HigherHeatLpControls HigherHeatContinuousCylinders

def exponent (m : ℕ) : ℝ≥0∞ := (power m).conjExponent

instance conjugate (m : ℕ) [Fact (0 < m)] : ENNReal.HolderConjugate (exponent m) (power m) :=
  inferInstanceAs (ENNReal.HolderConjugate (power m).conjExponent (power m))

instance exponent_fact (m : ℕ) [Fact (0 < m)] : Fact (1 ≤ exponent m) :=
  ⟨ENNReal.HolderConjugate.one_le (exponent m) (power m)⟩

abbrev Control (m : ℕ) := Lp (α := ℝ) ℝ (exponent m) volume

theorem control_complete (m : ℕ) [Fact (0 < m)] : CompleteSpace (Control m) := inferInstance

theorem interval_integrable (m : ℕ) [Fact (0 < m)] (u : Control m) (a b : ℝ) :
    IntervalIntegrable u volume a b :=
  ((Lp.memLp u).locallyIntegrable (exponent_fact m).out).integrableOn_isCompact
    isCompact_uIcc |>.intervalIntegrable

def primitive (m : ℕ) [Fact (0 < m)] (u : Control m) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, u s

theorem primitive_continuous (m : ℕ) [Fact (0 < m)] (u : Control m) :
    Continuous (primitive m u) :=
  intervalIntegral.continuous_primitive (interval_integrable m u) 0

def direction (m : ℕ) [Fact (0 < m)] (u : Control m) : Path :=
  ⟨⟨primitive m u, primitive_continuous m u⟩, by simp [primitive]⟩

theorem direction_increment (m : ℕ) [Fact (0 < m)] (u : Control m) (N : ℕ) (j : Fin N) :
    FourierPathDyadicDirections.increment (direction m u) N j =
      ∫ s in (j.val : ℝ)/(N : ℝ)..(j.val+1 : ℝ)/(N : ℝ), u s :=
  intervalIntegral.integral_interval_sub_left (interval_integrable m u 0 _)
    (interval_integrable m u 0 _)

theorem direction_ae_derivative (m : ℕ) [Fact (0 < m)] (u : Control m) :
    ∀ᵐ s, HasDerivAt (fun t => (direction m u).val t) (u s) s :=
  (_root_.LocallyIntegrable.ae_hasDerivAt_integral
    ((Lp.memLp u).locallyIntegrable (exponent_fact m).out)).mono (fun _ hs => hs 0)

theorem direction_injective (m : ℕ) [Fact (0 < m)] : Function.Injective (direction m) := by
  intro u v huv
  apply Lp.ext
  filter_upwards [direction_ae_derivative m u, direction_ae_derivative m v] with s hu hv
  rw [huv] at hu
  exact hu.unique hv

def pairing (m : ℕ) [Fact (0 < m)] :
    Control m →L[ℝ] HigherHeatLpControls.Control m →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing volume (exponent m) (power m)

theorem pairing_integral (m : ℕ) [Fact (0 < m)] (u : Control m)
    (b : HigherHeatLpControls.Control m) : pairing m u b = ∫ s : ℝ, u s * b s :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing_eq_integral u b

theorem pairing_bound (m : ℕ) [Fact (0 < m)] (u : Control m)
    (b : HigherHeatLpControls.Control m) : |pairing m u b| ≤ ‖u‖ * ‖b‖ := by
  rw [← Real.norm_eq_abs]
  change ‖L1.integralCLM' ℝ ((ContinuousLinearMap.mul ℝ ℝ).holder 1 u b)‖ ≤ _
  rw [← L1.integral_eq' ℝ]
  have hh := (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le (r := 1) u b
  have hB : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  have hb : ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖u‖ * ‖b‖ ≤ ‖u‖ * ‖b‖ := by
    nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg b)]
  exact (L1.norm_integral_le _).trans (hh.trans hb)

end OperatorDerivativeRewrite.Foundation.FourierPathDualControls
