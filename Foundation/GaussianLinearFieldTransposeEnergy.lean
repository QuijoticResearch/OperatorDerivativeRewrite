import Foundation.GaussianLinearFieldTranspose

/-! Correct transpose energy on all completed linear Gaussian fields.
This supplies the precise pairing relevant to the rough-fBM manuscript diagnostic. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianLinearFieldTransposeEnergy
open InfiniteGaussian GaussianSourceHodge GaussianLinearFieldDivergenceCompletion
open GaussianLinearFieldTranspose

/-- The correction is a transpose pairing, which can be negative. -/
theorem completed_transpose_energy {v : GaussianVectorL2} (hv : v ∈ linearGaussianFields) :
    ‖completedDivergence v‖^2 = ‖v‖^2 + inner ℝ (transpose v) v := by
  have he := congrArg (fun w : GaussianVectorL2 => ‖w‖^2) (symmetricPart_eq v)
  rw [norm_smul, mul_pow, Real.norm_eq_abs, norm_add_sq_real, transpose_norm,
    real_inner_comm (transpose v) v] at he
  norm_num at he
  rw [completed_energy hv]
  nlinarith

/-- Skew fields have exact cancellation between source and transpose energies. -/
theorem skew_energy_cancellation {v : GaussianVectorL2} (hv : v ∈ linearGaussianFields)
    (hs : transpose v = -v) :
    completedDivergence v = 0 ∧ inner ℝ (transpose v) v = -‖v‖^2 := by
  refine ⟨(completed_kernel_antisymmetric hv).mpr hs, ?_⟩
  rw [hs, inner_neg_left, real_inner_self_eq_norm_sq]

end OperatorDerivativeRewrite.Foundation.GaussianLinearFieldTransposeEnergy
