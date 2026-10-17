import Foundation.PeriodicCoarseGaugeDiagnostics
import Foundation.PeriodicCoarseEnergy

/-! Compression along the adjoint lift differs from energy minimization at fixed average. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseConstraint
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseGaugeDiagnostics PeriodicCoarseEnergy
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def detectedFace : CoarseFace := ⟨(coarseOrigin, 0, 1), by decide⟩

theorem bad_coarse_energy_lower : 16 ≤ coarseEnergy (average badGradient) := by
  have h := Finset.single_le_sum
    (fun (q : CoarseFace) (_ : q ∈ Finset.univ) => sq_nonneg (coarseIncidence (average badGradient) q))
    (Finset.mem_univ detectedFace)
  have hd : coarseIncidence (average badGradient) detectedFace = 4 := averaged_bad_curl
  rw [hd] at h
  norm_num only [show (4 : ℝ)^2 = 16 by norm_num] at h
  exact h

theorem bad_fine_energy_zero : fineEnergy badGradient = 0 := by
  simp [fineEnergy, badGradient_fine_closed]

theorem zero_energy_fiber_minimum : ∃ f : Edge → ℝ,
    average f = average badGradient ∧ fineEnergy f = 0 ∧
      ∀ g : Edge → ℝ, average g = average badGradient → fineEnergy f ≤ fineEnergy g := by
  refine ⟨badGradient, rfl, bad_fine_energy_zero, ?_⟩
  intro g _
  rw [bad_fine_energy_zero]
  exact fineEnergy_nonneg g

theorem compressed_energy_positive :
    1 ≤ fineEnergy (normalizedLift (average badGradient)) := by
  rw [normalized_lift_energy]
  linarith [bad_coarse_energy_lower]

theorem compression_not_fiber_minimum :
    ¬ ∀ (c : CoarseEdge → ℝ) (f : Edge → ℝ), average f = c →
      fineEnergy (normalizedLift c) ≤ fineEnergy f := by
  intro h
  have hb := h (average badGradient) badGradient rfl
  rw [bad_fine_energy_zero] at hb
  linarith [compressed_energy_positive]

theorem scaled_coarse_energy_not_fiber_lower :
    ¬ ∀ (c : CoarseEdge → ℝ) (f : Edge → ℝ), average f = c →
      (1/16 : ℝ) * coarseEnergy c ≤ fineEnergy f := by
  intro h
  have hb := h (average badGradient) badGradient rfl
  rw [bad_fine_energy_zero] at hb
  linarith [bad_coarse_energy_lower]

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseConstraint
