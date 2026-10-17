import Foundation.PeriodicLocalEigenbasis
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! Native eigenspace dimensions of the actual conditional single-block Hessian. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalMultiplicities
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity
  PeriodicLocalWalshAction PeriodicLocalSpectralSet PeriodicLocalEigenbasis
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem basis_eigen (a : Label) : H (eigenBasis a) = (eigenvalue a : ℝ) • eigenBasis a := by
  rw [eigenBasis_apply]
  exact mode_eigen a

theorem action_repr (v : Field) (a : Label) :
    eigenBasis.repr (H v) a = (eigenvalue a : ℝ)*eigenBasis.repr v a := by
  have hm : (eigenBasis.coord a).comp H = (eigenvalue a : ℝ) • eigenBasis.coord a := by
    apply eigenBasis.ext
    intro b
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [basis_eigen, map_smul]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply, smul_eq_mul]
    by_cases h : b=a <;> simp [h]
  exact congrArg (fun f : Field →ₗ[ℝ] ℝ => f v) hm

theorem coefficient_zero_off_eigenvalue (k : ℕ) (v : Field)
    (hv : v ∈ Module.End.eigenspace H (k : ℝ)) (a : Label) (ha : eigenvalue a ≠ k) :
    eigenBasis.repr v a = 0 := by
  have hh : H v = (k : ℝ) • v := Module.End.mem_eigenspace_iff.mp hv
  have hc := congrArg (fun w => eigenBasis.repr w a) hh
  rw [action_repr] at hc
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  have hz : ((eigenvalue a : ℝ)-(k : ℝ))*eigenBasis.repr v a = 0 := by nlinarith [hc]
  apply (mul_eq_zero.mp hz).resolve_left
  apply sub_ne_zero.mpr
  exact_mod_cast ha

theorem eigenspace_eq_span (k : ℕ) : Module.End.eigenspace H (k : ℝ) =
    Submodule.span ℝ (Set.range (fun a : {a : Label // eigenvalue a = k} => mode a.val)) := by
  apply le_antisymm
  · intro v hv
    rw [← eigenBasis.sum_repr v]
    apply Submodule.sum_mem
    intro a _
    rw [eigenBasis_apply]
    by_cases ha : eigenvalue a = k
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩)
    · rw [coefficient_zero_off_eigenvalue k v hv a ha, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change mode a.val ∈ Module.End.eigenspace H (k : ℝ)
    rw [Module.End.mem_eigenspace_iff, mode_eigen, a.property]

theorem eigenspace_finrank (k : ℕ) : Module.finrank ℝ (Module.End.eigenspace H (k : ℝ)) =
    Fintype.card {a : Label // eigenvalue a = k} := by
  rw [eigenspace_eq_span]
  exact finrank_span_eq_card (mode_linearIndependent.comp _ Subtype.val_injective)

theorem actual_multiplicities :
    Module.finrank ℝ (Module.End.eigenspace H (3 : ℝ)) = 15 ∧
    Module.finrank ℝ (Module.End.eigenspace H (7 : ℝ)) = 6 ∧
    Module.finrank ℝ (Module.End.eigenspace H (9 : ℝ)) = 8 ∧
    Module.finrank ℝ (Module.End.eigenspace H (11 : ℝ)) = 3 := by
  simpa only [← eigenspace_finrank, Nat.cast_ofNat] using eigenvalue_counts

theorem matrix_diagonal : LinearMap.toMatrix eigenBasis eigenBasis H =
    Matrix.diagonal (fun a : Label => (eigenvalue a : ℝ)) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [LinearMap.toMatrix_apply, basis_eigen]
  · simp [LinearMap.toMatrix_apply, basis_eigen, h]

theorem charpoly_product : H.charpoly =
    ∏ a : Label, (Polynomial.X-Polynomial.C (eigenvalue a : ℝ)) := by
  rw [← LinearMap.charpoly_toMatrix H eigenBasis, matrix_diagonal, Matrix.charpoly_diagonal]

theorem eigenvalue_mem (a : Label) :
    eigenvalue a = 3 ∨ eigenvalue a = 7 ∨ eigenvalue a = 9 ∨ eigenvalue a = 11 := by
  revert a
  decide

theorem charpoly_factorization : H.charpoly =
    (Polynomial.X-Polynomial.C (3 : ℝ))^15 * (Polynomial.X-Polynomial.C (7 : ℝ))^6 *
      (Polynomial.X-Polynomial.C (9 : ℝ))^8 * (Polynomial.X-Polynomial.C (11 : ℝ))^3 := by
  rw [charpoly_product]
  have hm : ∀ a ∈ (Finset.univ : Finset Label), eigenvalue a ∈ ({3,7,9,11} : Finset ℕ) := by
    intro a _
    rcases eigenvalue_mem a with h | h | h | h <;> simp [h]
  have hp := Finset.prod_fiberwise_of_maps_to' hm
    (fun k : ℕ => Polynomial.X-Polynomial.C (k : ℝ))
  rw [← hp]
  simp only [Finset.prod_const]
  have h3 : ((Finset.univ : Finset Label).filter (fun a => eigenvalue a=3)).card=15 := by decide
  have h7 : ((Finset.univ : Finset Label).filter (fun a => eigenvalue a=7)).card=6 := by decide
  have h9 : ((Finset.univ : Finset Label).filter (fun a => eigenvalue a=9)).card=8 := by decide
  have h11 : ((Finset.univ : Finset Label).filter (fun a => eigenvalue a=11)).card=3 := by decide
  norm_num [h3,h7,h9,h11, mul_assoc, Polynomial.C_ofNat]

end OperatorDerivativeRewrite.Foundation.PeriodicLocalMultiplicities
