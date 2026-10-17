import Foundation.UnitalLpFiniteMass
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Ambient Lebesgue Lp classes cannot retain data supported only on the diagonal. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.DiagonalAmbientNullity
set_option backward.isDefEq.respectTransparency false

def plane : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
def diagonal : Set (ℝ × ℝ) := {p | p.1 = p.2}

theorem diagonal_measurable : MeasurableSet diagonal :=
  (isClosed_eq continuous_fst continuous_snd).measurableSet

theorem diagonal_slice (x : ℝ) : Prod.mk x ⁻¹' diagonal = {x} := by
  ext y
  simp [diagonal, eq_comm]

theorem plane_diagonal_zero : plane diagonal = 0 := by
  rw [plane, Measure.prod_apply diagonal_measurable]
  simp only [diagonal_slice, Real.volume_singleton, lintegral_zero]

theorem ae_off_diagonal : ∀ᵐ p ∂plane, p ∉ diagonal := by
  rw [ae_iff]
  simpa only [not_not, Set.ofPred_mem_eq] using plane_diagonal_zero

theorem supported_diagonal_ae_zero (f : ℝ × ℝ → ℝ)
    (hf : ∀ p ∉ diagonal, f p = 0) : f =ᵐ[plane] 0 := by
  filter_upwards [ae_off_diagonal] with p hp
  exact hf p hp

theorem Lp_diagonal_eq_zero {p : ℝ≥0∞} (f : Lp ℝ p plane)
    (hf : ∀ᵐ x ∂plane, x ∉ diagonal → f x = 0) : f = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [ae_off_diagonal, hf] with x hx hfx
  exact hfx hx

theorem L2_defect_zero (u v w : Lp ℝ 2 plane)
    (hoff : ∀ᵐ x ∂plane, x ∉ diagonal → (u - v - w) x = 0) : u = v + w := by
  have hz : u - v - w = 0 := Lp_diagonal_eq_zero _ hoff
  have he : u = w + v := sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)
  exact he.trans (add_comm w v)

def diagonalValue (c : ℝ) : ℝ × ℝ → ℝ := diagonal.indicator (fun _ => c)

theorem diagonalValue_on (c x : ℝ) : diagonalValue c (x,x) = c := by
  simp [diagonalValue, diagonal]

theorem diagonalValue_ae_zero (c : ℝ) : diagonalValue c =ᵐ[plane] 0 :=
  supported_diagonal_ae_zero _ (fun p hp => by simp [diagonalValue, hp])

theorem diagonalValue_memLp (c : ℝ) (p : ℝ≥0∞) : MemLp (diagonalValue c) p plane :=
  (memLp_congr_ae (diagonalValue_ae_zero c)).mpr (MemLp.zero)

theorem diagonalValue_toL2_zero (c : ℝ) :
    (diagonalValue_memLp c 2).toLp (diagonalValue c) = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  exact (MemLp.coeFn_toLp _).trans (diagonalValue_ae_zero c)

end OperatorDerivativeRewrite.Foundation.DiagonalAmbientNullity
