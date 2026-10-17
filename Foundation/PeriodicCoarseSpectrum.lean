import Foundation.PeriodicCoarseEigenbasis
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! Exact eigenspace dimensions and characteristic polynomial of the actual coarse curl Gram. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseSpectrum
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarseGramAction PeriodicCoarseEigenbasis
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem basis_eigen (a : Label) : H (eigenBasis a) = (eigenvalue a : ℝ) • eigenBasis a := by
  rw [eigenBasis_apply]
  exact mode_eigen a

theorem action_repr (f : Field) (a : Label) :
    eigenBasis.repr (H f) a = (eigenvalue a : ℝ) * eigenBasis.repr f a := by
  have h : (eigenBasis.coord a).comp H = (eigenvalue a : ℝ) • eigenBasis.coord a := by
    apply eigenBasis.ext
    intro b
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [basis_eigen, map_smul]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self_apply, smul_eq_mul]
    by_cases hb : b = a <;> simp [hb]
  exact LinearMap.congr_fun h f

theorem coefficient_zero_off (k : ℕ) (f : Field)
    (hf : f ∈ Module.End.eigenspace H (k : ℝ)) (a : Label) (ha : eigenvalue a ≠ k) :
    eigenBasis.repr f a = 0 := by
  have h := congrArg (fun v => eigenBasis.repr v a) (Module.End.mem_eigenspace_iff.mp hf)
  rw [action_repr] at h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h
  have hz : ((eigenvalue a : ℝ)-(k : ℝ))*eigenBasis.repr f a = 0 := by nlinarith [h]
  apply (mul_eq_zero.mp hz).resolve_left
  apply sub_ne_zero.mpr
  exact_mod_cast ha

theorem eigenspace_eq_span (k : ℕ) : Module.End.eigenspace H (k : ℝ) =
    Submodule.span ℝ (Set.range (fun a : {a : Label // eigenvalue a = k} => eigenMode a.val)) := by
  apply le_antisymm
  · intro f hf
    rw [← eigenBasis.sum_repr f]
    apply Submodule.sum_mem
    intro a _
    rw [eigenBasis_apply]
    by_cases ha : eigenvalue a = k
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨a,ha⟩,rfl⟩)
    · rw [coefficient_zero_off k f hf a ha, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    change eigenMode a.val ∈ Module.End.eigenspace H (k : ℝ)
    rw [Module.End.mem_eigenspace_iff, mode_eigen, a.property]

theorem eigenspace_finrank (k : ℕ) : Module.finrank ℝ (Module.End.eigenspace H (k : ℝ)) =
    Fintype.card {a : Label // eigenvalue a = k} := by
  rw [eigenspace_eq_span]
  exact finrank_span_eq_card (eigenMode_linearIndependent.comp _ Subtype.val_injective)

theorem actual_multiplicities :
    Module.finrank ℝ (Module.End.eigenspace H (0 : ℝ)) = 19 ∧
    Module.finrank ℝ (Module.End.eigenspace H (4 : ℝ)) = 12 ∧
    Module.finrank ℝ (Module.End.eigenspace H (8 : ℝ)) = 18 ∧
    Module.finrank ℝ (Module.End.eigenspace H (12 : ℝ)) = 12 ∧
    Module.finrank ℝ (Module.End.eigenspace H (16 : ℝ)) = 3 := by
  let d : ℝ → ℕ := fun r => Module.finrank ℝ (Module.End.eigenspace H r)
  have hd (k : ℕ) (r : ℝ) (hkr : (k : ℝ) = r) :
      d r = Fintype.card {a : Label // eigenvalue a = k} :=
    (congrArg d hkr).symm.trans (eigenspace_finrank k)
  rcases eigenvalue_counts with ⟨h0,h4,h8,h12,h16⟩
  exact ⟨(hd 0 0 (by norm_num)).trans h0, (hd 4 4 (by norm_num)).trans h4,
    (hd 8 8 (by norm_num)).trans h8, (hd 12 12 (by norm_num)).trans h12,
    (hd 16 16 (by norm_num)).trans h16⟩

theorem matrix_diagonal : LinearMap.toMatrix eigenBasis eigenBasis H =
    Matrix.diagonal (fun a : Label => (eigenvalue a : ℝ)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [LinearMap.toMatrix_apply, basis_eigen]
  · simp [LinearMap.toMatrix_apply, basis_eigen, h]

theorem charpoly_product : H.charpoly =
    ∏ a : Label, (Polynomial.X-Polynomial.C (eigenvalue a : ℝ)) := by
  rw [← LinearMap.charpoly_toMatrix H eigenBasis, matrix_diagonal, Matrix.charpoly_diagonal]

theorem charpoly_factorization : H.charpoly =
    Polynomial.X^19 * (Polynomial.X-Polynomial.C (4 : ℝ))^12 *
      (Polynomial.X-Polynomial.C (8 : ℝ))^18 * (Polynomial.X-Polynomial.C (12 : ℝ))^12 *
      (Polynomial.X-Polynomial.C (16 : ℝ))^3 := by
  rw [charpoly_product]
  have hm : ∀ a ∈ (Finset.univ : Finset Label), eigenvalue a ∈ ({0,4,8,12,16} : Finset ℕ) := by
    intro a _
    rcases eigenvalue_mem a with h | h | h | h | h <;> simp [h]
  have hp := Finset.prod_fiberwise_of_maps_to' hm
    (fun k : ℕ => Polynomial.X-Polynomial.C (k : ℝ))
  rw [← hp]
  simp only [Finset.prod_const]
  have h0 : ((Finset.univ : Finset Label).filter (fun a => eigenvalue a = 0)).card = 19 := by decide
  have h4 : ((Finset.univ : Finset Label).filter (fun a => eigenvalue a = 4)).card = 12 := by decide
  have h8 : ((Finset.univ : Finset Label).filter (fun a => eigenvalue a = 8)).card = 18 := by decide
  have h12 : ((Finset.univ : Finset Label).filter (fun a => eigenvalue a = 12)).card = 12 := by decide
  have h16 : ((Finset.univ : Finset Label).filter (fun a => eigenvalue a = 16)).card = 3 := by decide
  norm_num [h0,h4,h8,h12,h16,mul_assoc,Polynomial.C_ofNat]

theorem gram_kernel_eq_closed : LinearMap.ker H = LinearMap.ker coarseIncidence := by
  have he : Module.End.eigenspace H (0 : ℝ) = LinearMap.ker H := by
    ext f
    simp [Module.End.mem_eigenspace_iff, LinearMap.mem_ker]
  have hd : Module.finrank ℝ (LinearMap.ker H) = 19 := by
    rw [← he]
    exact actual_multiplicities.1
  have hl : LinearMap.ker coarseIncidence ≤ LinearMap.ker H := by
    intro f hf
    change H f = 0
    rw [H_apply, gramMatrix, ← Matrix.mulVec_mulVec,
      PeriodicCoarseGramAction.incidenceMatrix_mulVec, hf, Matrix.mulVec_zero]
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq hl
  rw [PeriodicCoarseHodgeRanks.closed_finrank, hd]

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseSpectrum
