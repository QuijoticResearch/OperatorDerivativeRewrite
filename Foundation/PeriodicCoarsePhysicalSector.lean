import Foundation.PeriodicCoarseSpectrum

/-! The actual45-dimensional sector orthogonal to every closed coarse field. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarsePhysicalSector
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarseGramAction PeriodicCoarseEigenbasis PeriodicCoarseSpectrum
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def physicalSpace : Submodule ℝ Field where
  carrier := {f | ∀ g : Field, coarseIncidence g = 0 → dotProduct f g = 0}
  zero_mem' := by intro g _; simp
  add_mem' := by intro f h hf hh g hg; simp [add_dotProduct, hf g hg, hh g hg]
  smul_mem' := by intro r f hf g hg; simp [smul_dotProduct, hf g hg]

def positiveSpan : Submodule ℝ Field :=
  Submodule.span ℝ (Set.range (fun a : {a : Label // eigenvalue a ≠ 0} => eigenMode a.val))

theorem H_dot_symmetric (f g : Field) : dotProduct f (H g) = dotProduct (H f) g := by
  have he (u v : Field) : dotProduct u (H v) =
      dotProduct (PeriodicCoarseGramAction.incidenceMatrix.mulVec u)
        (PeriodicCoarseGramAction.incidenceMatrix.mulVec v) := by
    rw [H_apply, gramMatrix, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
    exact dotProduct_comm _ _
  rw [he, dotProduct_comm (H f) g, he]
  exact dotProduct_comm _ _

theorem zeroMode_closed (a : Label) (ha : eigenvalue a = 0) : coarseIncidence (eigenMode a) = 0 := by
  have h : eigenMode a ∈ LinearMap.ker H := by
    rw [LinearMap.mem_ker, mode_eigen, ha, Nat.cast_zero, zero_smul]
  rw [gram_kernel_eq_closed] at h
  exact h

theorem positiveMode_physical (a : Label) (ha : eigenvalue a ≠ 0) : eigenMode a ∈ physicalSpace := by
  intro g hg
  have hk : H g = 0 := by
    have h : g ∈ LinearMap.ker coarseIncidence := hg
    rw [← gram_kernel_eq_closed] at h
    exact h
  have h := H_dot_symmetric (eigenMode a) g
  rw [hk, mode_eigen] at h
  simp only [dotProduct_zero, smul_dotProduct, smul_eq_mul] at h
  have hn : (eigenvalue a : ℝ) ≠ 0 := by exact_mod_cast ha
  exact (mul_eq_zero.mp h.symm).resolve_left hn

theorem dual_zero_int : ∀ (a : Label), eigenvalue a = 0 →
    ∀ e : CoarseEdge, intDual a e = intEigenMode a e := by decide

theorem dual_zero (a : Label) (ha : eigenvalue a = 0) : dual a = eigenMode a := by
  funext e
  rw [eigenMode_int]
  exact congrArg (fun z : ℤ => (z : ℝ)) (dual_zero_int a ha e)

theorem eigenCoefficient_dot (a : Label) (f : Field) :
    dotProduct f (dual a) = (normalization a : ℝ) * eigenBasis.repr f a := by
  have h := congrArg (fun v => dotProduct v (dual a)) (eigenBasis.sum_repr f)
  rw [sum_dotProduct] at h
  simp only [eigenBasis_apply, smul_dotProduct, eigenMode_dual_pair, smul_eq_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  calc
    _ = eigenBasis.repr f a * (normalization a : ℝ) := h.symm
    _ = _ := mul_comm _ _

theorem physical_zeroCoefficient (f : Field) (hf : f ∈ physicalSpace) (a : Label)
    (ha : eigenvalue a = 0) : eigenBasis.repr f a = 0 := by
  have h := hf (eigenMode a) (zeroMode_closed a ha)
  rw [← dual_zero a ha, eigenCoefficient_dot] at h
  have hp : 0 < (normalization a : ℝ) := by exact_mod_cast normalization_pos a
  exact (mul_eq_zero.mp h).resolve_left hp.ne'

theorem physicalSpace_eq_positiveSpan : physicalSpace = positiveSpan := by
  apply le_antisymm
  · intro f hf
    rw [← eigenBasis.sum_repr f]
    apply Submodule.sum_mem
    intro a _
    rw [eigenBasis_apply]
    by_cases ha : eigenvalue a = 0
    · rw [physical_zeroCoefficient f hf a ha, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨a,ha⟩,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact positiveMode_physical a.val a.property

theorem physicalSpace_finrank : Module.finrank ℝ physicalSpace = 45 := by
  rw [physicalSpace_eq_positiveSpan]
  have hc : Fintype.card {a : Label // eigenvalue a ≠ 0} = 45 := by decide
  unfold positiveSpan
  have hi : LinearIndependent ℝ (fun a : {a : Label // eigenvalue a ≠ 0} => eigenMode a.val) :=
    eigenMode_linearIndependent.comp _ Subtype.val_injective
  exact (finrank_span_eq_card hi).trans hc

theorem physicalSpace_invariant {f : Field} (hf : f ∈ physicalSpace) : H f ∈ physicalSpace := by
  intro g hg
  rw [← H_dot_symmetric]
  have hz : H g = 0 := by
    have h : g ∈ LinearMap.ker coarseIncidence := hg
    rw [← gram_kernel_eq_closed] at h
    exact h
  rw [hz, dotProduct_zero]

theorem physical_zero_kernel (f : Field) (hf : f ∈ physicalSpace) (hH : H f = 0) : f = 0 := by
  apply eigenBasis.repr.injective
  ext a
  simp only [map_zero, Finsupp.zero_apply]
  change eigenBasis.repr f a = 0
  by_cases ha : eigenvalue a = 0
  · exact physical_zeroCoefficient f hf a ha
  · have h := congrArg (fun v : Field => eigenBasis.repr v a) hH
    rw [action_repr] at h
    simp only [map_zero, Finsupp.zero_apply] at h
    have hn : (eigenvalue a : ℝ) ≠ 0 := by exact_mod_cast ha
    exact (mul_eq_zero.mp h).resolve_left hn

end OperatorDerivativeRewrite.Foundation.PeriodicCoarsePhysicalSector
