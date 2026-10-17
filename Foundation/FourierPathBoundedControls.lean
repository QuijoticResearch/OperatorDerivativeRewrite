import Foundation.FourierPathDyadicDirections
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! Actual direction paths obtained by integrating essentially bounded time controls. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathBoundedControls
open HigherHeatContinuousCylinders

abbrev Control := Lp ℝ ∞ (volume : Measure ℝ)

theorem ae_bound (u : Control) : ∀ᵐ s, ‖u s‖ ≤ ‖u‖ := by
  simpa [lpNorm, (Lp.memLp u).aestronglyMeasurable, Lp.norm_def] using
    ae_le_lpNorm_exponent_top (Lp.memLp u)

theorem interval_integrable (u : Control) (a b : ℝ) : IntervalIntegrable u volume a b := by
  exact ((Lp.memLp u).locallyIntegrable le_top).integrableOn_isCompact
    isCompact_uIcc |>.intervalIntegrable

def primitive (u : Control) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, u s

theorem primitive_sub (u : Control) (a b : ℝ) :
    primitive u b - primitive u a = ∫ s in a..b, u s :=
  intervalIntegral.integral_interval_sub_left (interval_integrable u 0 b)
    (interval_integrable u 0 a)

theorem primitive_lipschitz (u : Control) : LipschitzWith ‖u‖₊ (primitive u) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [Real.dist_eq, ← Real.norm_eq_abs, primitive_sub, Real.dist_eq]
  exact intervalIntegral.norm_integral_le_of_norm_le_const_ae
    ((ae_bound u).mono fun s hs _ => hs)

def direction (u : Control) : Path :=
  ⟨⟨primitive u, (primitive_lipschitz u).continuous⟩, by simp [primitive]⟩

theorem direction_apply (u : Control) (t : ℝ) : (direction u).val t = ∫ s in (0:ℝ)..t, u s := rfl

theorem direction_lipschitz (u : Control) :
    LipschitzOnWith ‖u‖₊ (direction u).val (Set.Icc (0:ℝ) 1) :=
  (primitive_lipschitz u).lipschitzOnWith

theorem direction_increment (u : Control) (N : ℕ) (j : Fin N) :
    FourierPathDyadicDirections.increment (direction u) N j =
      ∫ s in (j.val:ℝ)/(N:ℝ)..(j.val+1:ℝ)/(N:ℝ), u s := by
  exact primitive_sub u _ _

theorem direction_ae_derivative (u : Control) :
    ∀ᵐ s, HasDerivAt (fun t => (direction u).val t) (u s) s := by
  exact (_root_.LocallyIntegrable.ae_hasDerivAt_integral
    ((Lp.memLp u).locallyIntegrable le_top)).mono
    fun s hs => hs 0

theorem direction_injective : Function.Injective direction := by
  intro u v huv
  apply Lp.ext
  filter_upwards [direction_ae_derivative u, direction_ae_derivative v] with s hu hv
  rw [huv] at hu
  exact hu.unique hv

end OperatorDerivativeRewrite.Foundation.FourierPathBoundedControls
