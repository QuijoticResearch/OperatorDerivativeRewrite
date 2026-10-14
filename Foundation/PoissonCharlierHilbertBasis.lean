import Foundation.PoissonCharlierCompleteness
import Foundation.GaussianHermite

/-! Complete Charlier coordinates and their scalar Gaussian Hilbert transfer.
This is a Hilbert-space equivalence; ordinary multiplication is not preserved. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonCharlierHilbertBasis
open PoissonDifferenceOperators PoissonCharlierLadder PoissonCharlierCompleteness

def normalizer (rate : ℝ≥0) (n : ℕ) : ℝ :=
  Real.sqrt ((n.factorial : ℝ)*(rate : ℝ)^n)

theorem normalizer_pos (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    0 < normalizer rate n := by
  apply Real.sqrt_pos.mpr
  have hp : (0 : ℝ) < rate := hr
  positivity

def normalized (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) : ScalarL2 rate :=
  (normalizer rate n)⁻¹ • PoissonCharlierLadder.scalar rate hr n

theorem normalized_orthonormal (rate : ℝ≥0) (hr : 0 < rate) :
    Orthonormal ℝ (normalized rate hr) := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [normalized,real_inner_smul_left,real_inner_smul_right,scalar_inner]
  by_cases h : n=m
  · subst m
    simp only [ite_true]
    have hs : (normalizer rate n)^2=(n.factorial : ℝ)*(rate : ℝ)^n :=
      Real.sq_sqrt (by positivity)
    have hn := ne_of_gt (normalizer_pos rate hr n)
    field_simp
    nlinarith
  · simp [h]

theorem normalized_span (rate : ℝ≥0) (hr : 0 < rate) :
    Submodule.span ℝ (Set.range (normalized rate hr))=scalarSpan rate hr := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    exact (scalarSpan rate hr).smul_mem _ (Submodule.subset_span ⟨n,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    have he : normalizer rate n • normalized rate hr n=PoissonCharlierLadder.scalar rate hr n := by
      rw [normalized,smul_smul,mul_inv_cancel₀ (ne_of_gt (normalizer_pos rate hr n)),one_smul]
    rw [← he]
    exact (Submodule.span ℝ (Set.range (normalized rate hr))).smul_mem _
      (Submodule.subset_span ⟨n,rfl⟩)

def basis (rate : ℝ≥0) (hr : 0 < rate) : HilbertBasis ℕ ℝ (ScalarL2 rate) :=
  HilbertBasis.mk (normalized_orthonormal rate hr) (by
    rw [normalized_span,scalarSpan_closure])

theorem basis_apply (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    basis rate hr n=normalized rate hr n := by rw [basis,HilbertBasis.coe_mk]

theorem coefficient (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (n : ℕ) :
    (basis rate hr).repr f n=inner ℝ (normalized rate hr n) f := by
  rw [HilbertBasis.repr_apply_apply,basis_apply]

theorem expansion_hasSum (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) :
    HasSum (fun n => (inner ℝ (normalized rate hr n) f) • normalized rate hr n) f := by
  simpa only [coefficient,basis_apply] using (basis rate hr).hasSum_repr f

def gaussianTransfer (rate : ℝ≥0) (hr : 0 < rate) :
    ScalarL2 rate ≃ₗᵢ[ℝ] GaussianCore.GaussianL2 :=
  (basis rate hr).repr.trans GaussianCore.hermiteBasis.repr.symm

theorem transfer_normalized (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    gaussianTransfer rate hr (normalized rate hr n)=GaussianCore.normalizedHermite n := by
  rw [← basis_apply rate hr n,gaussianTransfer]
  simp only [LinearIsometryEquiv.trans_apply,HilbertBasis.repr_self,
    HilbertBasis.repr_symm_single,GaussianCore.hermiteBasis_apply,one_smul]

theorem transfer_coefficient (rate : ℝ≥0) (hr : 0 < rate) (f : ScalarL2 rate) (n : ℕ) :
    inner ℝ (GaussianCore.normalizedHermite n) (gaussianTransfer rate hr f)=
      inner ℝ (normalized rate hr n) f := by
  rw [← transfer_normalized rate hr n]
  exact (gaussianTransfer rate hr).inner_map_map _ _

end OperatorDerivativeRewrite.Foundation.PoissonCharlierHilbertBasis
