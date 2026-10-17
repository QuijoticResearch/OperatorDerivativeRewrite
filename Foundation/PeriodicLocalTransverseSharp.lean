import Foundation.PeriodicLocalTransverseGap

/-! Actual sharp transverse witnesses and dot-product spectral orthogonality. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalTransverseSharp
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity PeriodicSingleBlockDecomposition
  PeriodicLocalGradientModes PeriodicLocalWalshAction PeriodicLocalSpectralSet
  PeriodicLocalTransverseGap
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem H_dot_symmetric (f g : Field) : dotProduct f (H g) = dotProduct (H f) g := by
  have he (u v : Field) : dotProduct u (H v) =
      dotProduct (localMatrix.mulVec u) (localMatrix.mulVec v) := by
    rw [H_apply, localHessian, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
    exact dotProduct_comm _ _
  rw [he, dotProduct_comm (H f) g, he]
  exact dotProduct_comm _ _

theorem eigenvector_transverse (f : Field) (ell : ℝ) (he : H f = ell • f) (h3 : ell ≠ 3) :
    transverse f := by
  intro φ
  have hg : H (localGradient φ) = (3 : ℝ) • localGradient φ := gradient_eigenvalue_three φ
  have h := H_dot_symmetric f (localGradient φ)
  rw [hg, he] at h
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
  have hz : (ell-3)*dotProduct f (localGradient φ) = 0 := by nlinarith [h]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr h3)

def witness : Field := walsh ({0,1} : Finset Direction) 0 - walsh ({0,1} : Finset Direction) 1

theorem witness_nonzero : witness ≠ 0 :=
  walsh_difference_nonzero _ _ _ (by decide)

theorem witness_eigen : H witness = (7 : ℝ) • witness := by
  change localHessian.mulVec witness = (7 : ℝ) • witness
  convert walsh_difference_eigenvalue ({0,1} : Finset Direction) 0 1
    (by decide) (by decide) using 1 <;> norm_num [witness]

theorem witness_transverse : transverse witness :=
  eigenvector_transverse witness 7 witness_eigen (by norm_num)

theorem witness_size_positive : 0 < squaredSize witness := by
  have h0 : 0 ≤ squaredSize witness := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : squaredSize witness ≠ 0 := fun h => witness_nonzero ((squaredSize_zero_iff _).mp h)
  exact lt_of_le_of_ne h0 (Ne.symm hn)

theorem witness_energy : energy witness = 7*squaredSize witness := by
  calc
    _ = dotProduct witness (H witness) := (hessian_energy witness).symm
    _ = _ := by
      rw [witness_eigen, dotProduct_smul]
      simp only [smul_eq_mul, dotProduct, PeriodicSingleBlockCoercivity.squaredSize, pow_two]

theorem witness_core_energy : coreEnergy witness = 4*squaredSize witness := by
  have h := witness_energy
  rw [exact_energy_decomposition] at h
  linarith

theorem witness_rayleigh : energy witness / squaredSize witness = 7 := by
  rw [witness_energy]
  field_simp [(ne_of_gt witness_size_positive)]

theorem witness_core_rayleigh : coreEnergy witness / squaredSize witness = 4 := by
  rw [witness_core_energy]
  field_simp [(ne_of_gt witness_size_positive)]

theorem no_stronger_transverse_bound (c : ℝ) (hc : 7 < c) :
    ¬ ∀ f : Field, transverse f → c*squaredSize f ≤ energy f := by
  intro h
  have hw := h witness witness_transverse
  rw [witness_energy] at hw
  nlinarith [witness_size_positive]

theorem no_stronger_internal_bound (c : ℝ) (hc : 4 < c) :
    ¬ ∀ f : Field, transverse f → c*squaredSize f ≤ coreEnergy f := by
  intro h
  have hw := h witness witness_transverse
  rw [witness_core_energy] at hw
  nlinarith [witness_size_positive]

end OperatorDerivativeRewrite.Foundation.PeriodicLocalTransverseSharp
