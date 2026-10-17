import Foundation.GaussianDiagonalQuadraticL4
import Foundation.GaussianLinearFieldDivergenceCompletion
import Mathlib.Analysis.Matrix.Spectrum

/-! Spectral transport of actual finite Gaussian quadratic observables. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticSpectralTransport
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeFieldNorm GaussianNumberSectors
open GaussianQuadraticSourceHodge GaussianLinearFieldDivergenceCompletion
open GaussianJointRecoveryIntertwining GaussianDiagonalQuadraticL4
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem mixedTarget_self_wick (u : CoefficientSpace) : mixedTarget u u = (wick u 2 : GaussianL2) := by
  apply Lp.ext
  filter_upwards [mixedTarget_coeFn u u, core_coeFn u (‖u‖^2) 2] with ω hm hw
  rw [hm]
  change _ = (GaussianTimeSpaceHermite.core u (‖u‖^2) 2 : GaussianL2) ω
  rw [hw, value_two, real_inner_self_eq_norm_sq]
  ring

theorem mixedTarget_linear_combination (h : I → CoefficientSpace) (c d : I → ℝ) :
    mixedTarget (∑ i, c i • h i) (∑ j, d j • h j) =
      ∑ i, ∑ j, (c i * d j) • mixedTarget (h i) (h j) := by
  have ht (f : GaussianL2) : scalarTensor (∑ i, c i • h i) f =
      ∑ i, c i • scalarTensor (h i) f := by
    change sourceTensor f (∑ i, c i • h i) = _
    simp only [map_sum, map_smul]
    rfl
  rw [← completedDivergence_rank, ht]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_sum, map_smul, smul_smul, completedDivergence_rank, Finset.smul_sum]

def rotatedSources (h : I → CoefficientSpace) (U : Matrix.unitaryGroup I ℝ) : I → CoefficientSpace :=
  fun j => ∑ i, (U : Matrix I I ℝ) i j • h i

theorem rotatedSources_orthonormal (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    (U : Matrix.unitaryGroup I ℝ) : Orthonormal ℝ (rotatedSources h U) := by
  rw [orthonormal_iff_ite]
  intro j k
  simp only [rotatedSources, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp_rw [orthonormal_iff_ite.mp hh]
  have hu := congrArg (fun M : Matrix I I ℝ => M j k) (Unitary.coe_star_mul_self U)
  simpa [Matrix.mul_apply, Matrix.star_apply, mul_ite, ite_mul, mul_assoc,
    mul_comm, mul_left_comm, Matrix.one_apply] using hu

theorem spectral_entry {A : Matrix I I ℝ} (hA : A.IsHermitian) (i k : I) :
    A i k = ∑ j, (hA.eigenvectorUnitary : Matrix I I ℝ) i j * hA.eigenvalues j *
      (hA.eigenvectorUnitary : Matrix I I ℝ) k j := by
  have he := congrArg (fun M : Matrix I I ℝ => M i k) hA.spectral_theorem
  simpa [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal,
    mul_ite, ite_mul, mul_assoc] using he

theorem quadraticTarget_eq_diagonal {A : Matrix I I ℝ} (hA : A.IsHermitian)
    (h : I → CoefficientSpace) :
    quadraticTarget h A =
      (target (rotatedSources h hA.eigenvectorUnitary) hA.eigenvalues : GaussianL2) := by
  symm
  simp only [target, Submodule.coe_sum, Submodule.coe_smul, ← mixedTarget_self_wick,
    rotatedSources, mixedTarget_linear_combination, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  unfold quadraticTarget
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_smul]
  congr 1
  rw [spectral_entry hA]
  apply Finset.sum_congr rfl
  intro j _
  ring

end OperatorDerivativeRewrite.Foundation.GaussianQuadraticSpectralTransport
