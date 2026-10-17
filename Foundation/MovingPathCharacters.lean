import Foundation.FourierPathStopping
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Metrizable.Basic

/-! Jointly continuous moving-time path characters with exact uniform-norm separation. -/
noncomputable section
open Set
open scoped Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.MovingPathCharacters
open HigherHeatContinuousCylinders HigherHeatCylinderFourier

def character (t : ℝ) : Path →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun ω => phase 1 (ω.val t))
    ((phase_continuous 1).comp (coordinate_continuous t)) 1 (fun ω => (phase_norm _ _).le)

theorem character_apply (t : ℝ) (ω : Path) : character t ω = phase 1 (ω.val t) := rfl

theorem character_norm_le (t : ℝ) : ‖character t‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le zero_le_one).mpr (fun ω => (phase_norm _ _).le)

theorem joint_continuous : Continuous (fun z : ℝ × Path => character z.1 z.2) := by
  have he : Continuous (fun z : ℝ × Path => z.2.val z.1) := by fun_prop
  exact (phase_continuous 1).comp he

def witness (s t : ℝ) : Path :=
  ⟨⟨fun r => r*(r-s)/(2*t*(t-s)), by fun_prop⟩, by simp⟩

theorem witness_at_s (s t : ℝ) : (witness s t).val s = 0 := by simp [witness]

theorem witness_at_t (s t : ℝ) (ht : t ≠ 0) (hst : s ≠ t) :
    (witness s t).val t = 1/2 := by
  dsimp [witness]
  field_simp [ht, sub_ne_zero.mpr hst.symm]

theorem phase_half : phase 1 (1/2) = -1 := by
  rw [phase, Real.fourierChar_apply]
  have he : ((2 * Real.pi * (-((1/2 : ℝ)*1)) : ℝ) : ℂ) * Complex.I = -(Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem character_dist (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hst : s ≠ t) :
    dist (character s) (character t) = 2 := by
  apply le_antisymm
  · calc
      _ ≤ ‖character s‖ + ‖character t‖ := dist_le_norm_add_norm _ _
      _ ≤ 1+1 := add_le_add (character_norm_le s) (character_norm_le t)
      _ = 2 := by norm_num
  · have he := BoundedContinuousFunction.dist_coe_le_dist
      (f := character s) (g := character t) (witness s t)
    rw [character_apply, character_apply, witness_at_s, witness_at_t s t ht.ne' hst,
      phase_half] at he
    norm_num [phase, dist_eq_norm] at he
    simpa only [dist_eq_norm] using he

end OperatorDerivativeRewrite.Foundation.MovingPathCharacters
