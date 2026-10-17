import Foundation.GaussianOrthogonalPolynomialIndependence
import Foundation.GaussianQuadraticCovarianceEquality

/-! Matrix annihilation gives actual independence of finite Gaussian quadratics. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticAnnihilationIndependence
open InfiniteGaussian GaussianNumberSectors GaussianQuadraticSourceHodge
open GaussianQuadraticMatrixContraction GaussianQuadraticCovarianceEquality
open GaussianQuadraticSpectralTransport GaussianDiagonalQuadraticL4
open GaussianOrthogonalPolynomialIndependence
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem symmetric_eigenvectors_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A B : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (hab : A.comp B = 0) (u v : E) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : A u = a • u) (hv : B v = b • v) :
    inner ℝ u v = 0 := by
  have he : inner ℝ (A u) (B v) = 0 := by
    rw [hA u (B v)]
    have hz : A (B v) = 0 := congrArg (fun T : E →ₗ[ℝ] E => T v) hab
    rw [hz, inner_zero_right]
  rw [hu, hv, real_inner_smul_left, real_inner_smul_right] at he
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left ha)).resolve_left hb

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrix_eigenvector_equation {A : Matrix I I ℝ} (hA : A.IsHermitian) (i : I) :
    Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
  apply PiLp.ext
  intro k
  change (Matrix.mulVec A (hA.eigenvectorBasis i : I → ℝ)) k = _
  simpa only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using congrFun (hA.mulVec_eigenvectorBasis i) k

theorem active_eigenvectors_orthogonal {A B : Matrix I I ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hab : A*B = 0)
    (i j : I) (hi : hA.eigenvalues i ≠ 0) (hj : hB.eigenvalues j ≠ 0) :
    inner ℝ (hA.eigenvectorBasis i) (hB.eigenvectorBasis j) = 0 := by
  have hc : (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) = 0 := by
    change (Matrix.toLpLin 2 2 A).comp (Matrix.toLpLin 2 2 B) = 0
    rw [← Matrix.toLpLin_mul_same, hab, map_zero]
  exact symmetric_eigenvectors_orthogonal (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) hc _ _ _ _ hi hj
    (matrix_eigenvector_equation hA i) (matrix_eigenvector_equation hB j)

theorem source_sum_inner (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) (a b : I → ℝ) :
    inner ℝ (∑ i, a i • h i) (∑ i, b i • h i) = ∑ i, a i * b i := by
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    orthonormal_iff_ite.mp hh]
  simp [mul_ite, ite_mul, mul_comm]

theorem rotated_eigenvectors_inner (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A B : Matrix I I ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : I) :
    inner ℝ (rotatedSources h hA.eigenvectorUnitary i) (rotatedSources h hB.eigenvectorUnitary j) =
      inner ℝ (hA.eigenvectorBasis i) (hB.eigenvectorBasis j) := by
  rw [rotatedSources, rotatedSources, source_sum_inner h hh]
  simp only [PiLp.inner_apply, Matrix.IsHermitian.eigenvectorUnitary_apply, Real.inner_apply]

theorem active_rotated_sources_orthogonal (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A B : Matrix I I ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hab : A*B = 0)
    (i j : I) (hi : hA.eigenvalues i ≠ 0) (hj : hB.eigenvalues j ≠ 0) :
    inner ℝ (rotatedSources h hA.eigenvectorUnitary i) (rotatedSources h hB.eigenvectorUnitary j) = 0 := by
  rw [rotated_eigenvectors_inner h hh hA hB]
  exact active_eigenvectors_orthogonal hA hB hab i j hi hj

theorem target_restrict_nonzero (v : I → CoefficientSpace) (a : I → ℝ)
    (s : Finset I) (hs : ∀ i, i ∈ s ↔ a i ≠ 0) :
    (target v a : GaussianL2) = (target (fun i : s => v i) (fun i : s => a i) : GaussianL2) := by
  classical
  simp only [target, Submodule.coe_sum, Submodule.coe_smul]
  calc
    (∑ i, a i • (GaussianTimeSpaceHermite.wick (v i) 2 : GaussianL2)) =
        ∑ i ∈ s, a i • (GaussianTimeSpaceHermite.wick (v i) 2 : GaussianL2) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      have ha : a i = 0 := by simpa only [hs i, not_not] using hi
      simp only [ha, zero_smul]
    _ = _ := (Finset.sum_coe_sort s (fun i => a i • (GaussianTimeSpaceHermite.wick (v i) 2 : GaussianL2))).symm

theorem matrix_mul_zero_implies_independent (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A B : Matrix I I ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hab : A*B = 0) :
    IndepFun (matrixSectorMap h A).val (matrixSectorMap h B).val gaussianProduct := by
  classical
  let s : Finset I := Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0)
  let t : Finset I := Finset.univ.filter (fun j => hB.eigenvalues j ≠ 0)
  have hs (i : I) : i ∈ s ↔ hA.eigenvalues i ≠ 0 := by simp [s]
  have ht (j : I) : j ∈ t ↔ hB.eigenvalues j ≠ 0 := by simp [t]
  change IndepFun (quadraticTarget h A) (quadraticTarget h B) gaussianProduct
  rw [quadraticTarget_eq_diagonal hA, quadraticTarget_eq_diagonal hB,
    target_restrict_nonzero _ _ s hs, target_restrict_nonzero _ _ t ht]
  apply orthogonal_diagonal_quadratics_independent
  · exact (rotatedSources_orthonormal h hh _).comp Subtype.val Subtype.val_injective
  · exact (rotatedSources_orthonormal h hh _).comp Subtype.val Subtype.val_injective
  · intro i j
    exact active_rotated_sources_orthogonal h hh hA hB hab i j
      ((hs i).mp i.property) ((ht j).mp j.property)

theorem matrix_independent_iff_mul_zero (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A B : Matrix I I ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    IndepFun (matrixSectorMap h A).val (matrixSectorMap h B).val gaussianProduct ↔ A*B = 0 :=
  ⟨matrix_independent_implies_mul_zero h hh hA hB,
    matrix_mul_zero_implies_independent h hh hA hB⟩

theorem arbitrary_matrix_independent_iff (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    (A B : Matrix I I ℝ) :
    IndepFun (matrixSectorMap h A).val (matrixSectorMap h B).val gaussianProduct ↔
      symmetrize A * symmetrize B = 0 := by
  have ha : matrixSectorMap h (symmetrize A) = matrixSectorMap h A := by
    apply Subtype.ext
    exact GaussianFiniteQuadraticL4.quadraticTarget_symmetrize h A
  have hb : matrixSectorMap h (symmetrize B) = matrixSectorMap h B := by
    apply Subtype.ext
    exact GaussianFiniteQuadraticL4.quadraticTarget_symmetrize h B
  rw [← ha, ← hb]
  exact matrix_independent_iff_mul_zero h hh
    (GaussianFiniteQuadraticL4.symmetrize_hermitian A) (GaussianFiniteQuadraticL4.symmetrize_hermitian B)

theorem matrix_independent_iff_square_covariance_zero
    (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    {A B : Matrix I I ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    IndepFun (matrixSectorMap h A).val (matrixSectorMap h B).val gaussianProduct ↔
      inner ℝ (GaussianSecondChaosL4.square (matrixSectorMap h A))
        (GaussianSecondChaosL4.square (matrixSectorMap h B)) =
        ‖(matrixSectorMap h A).val‖^2 * ‖(matrixSectorMap h B).val‖^2 := by
  rw [matrix_independent_iff_mul_zero h hh hA hB, matrix_square_covariance_zero_iff h hh hA hB]
end OperatorDerivativeRewrite.Foundation.GaussianQuadraticAnnihilationIndependence
