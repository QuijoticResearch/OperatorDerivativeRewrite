import Foundation.PeriodicLocalTransverseSpace

/-! Explicit complementary local gradient/transverse projections in the actual eigenbasis. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalHodgeProjection
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity PeriodicLocalGradientModes
  PeriodicLocalWalshAction PeriodicLocalSpectralSet PeriodicLocalEigenbasis PeriodicLocalMultiplicities
  PeriodicLocalHodgeExact PeriodicLocalTransverseGap PeriodicLocalTransverseSharp
  PeriodicLocalTransverseSpace
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def gradientProjection : Field →ₗ[ℝ] Field :=
  eigenBasis.constr ℝ (fun a => if eigenvalue a=3 then eigenBasis a else 0)

def transverseProjection : Field →ₗ[ℝ] Field := LinearMap.id-gradientProjection

theorem gradientProjection_basis (a : Label) :
    gradientProjection (eigenBasis a) = if eigenvalue a=3 then eigenBasis a else 0 :=
  eigenBasis.constr_basis ℝ _ a

theorem transverseProjection_basis (a : Label) :
    transverseProjection (eigenBasis a) = if eigenvalue a=3 then 0 else eigenBasis a := by
  change eigenBasis a - gradientProjection (eigenBasis a) = _
  rw [gradientProjection_basis]
  by_cases h : eigenvalue a=3 <;> simp [h]

theorem gradientProjection_apply (f : Field) : gradientProjection f =
    ∑ a : Label, eigenBasis.repr f a • (if eigenvalue a=3 then eigenBasis a else 0) := by
  exact eigenBasis.constr_apply_fintype ℝ _ f

theorem basis_gradient (a : Label) (ha : eigenvalue a=3) :
    eigenBasis a ∈ LinearMap.range localGradient := by
  have hp := (eigenvalue_three_pivot a).mp ha
  rw [eigenBasis_apply, mode, if_pos hp]
  exact walshSum_in_gradient_range a.val.1

theorem gradientProjection_mem (f : Field) :
    gradientProjection f ∈ LinearMap.range localGradient := by
  rw [gradientProjection_apply]
  apply Submodule.sum_mem
  intro a _
  by_cases ha : eigenvalue a=3
  · simp only [ha, ite_true]
    exact Submodule.smul_mem _ _ (basis_gradient a ha)
  · simp [ha]

theorem gradientProjection_fixed {f : Field} (hf : f ∈ LinearMap.range localGradient) :
    gradientProjection f=f := by
  have he : f ∈ Module.End.eigenspace H (3 : ℝ) := by
    rw [gradient_range_eq_coreKernel, coreKernel_eq_eigenspace] at hf
    exact hf
  rw [gradientProjection_apply, ← eigenBasis.sum_repr f]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : eigenvalue a=3
  · simp [ha]
  · have hc := coefficient_zero_off_eigenvalue 3 f he a ha
    simp [ha, hc]

theorem gradientProjection_zero {f : Field} (hf : transverse f) : gradientProjection f=0 := by
  rw [gradientProjection_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : eigenvalue a=3
  · rw [transverse_three_coefficient hf a ha]
    simp
  · simp [ha]

theorem transverseProjection_mem (f : Field) : transverse (transverseProjection f) := by
  change transverseProjection f ∈ transverseSpace
  rw [← eigenBasis.sum_repr f, map_sum]
  apply Submodule.sum_mem
  intro a _
  rw [map_smul, transverseProjection_basis]
  by_cases ha : eigenvalue a=3
  · simp [ha]
  · simp only [ha, ite_false]
    apply Submodule.smul_mem
    change transverse (eigenBasis a)
    apply eigenvector_transverse _ _ (basis_eigen a)
    exact_mod_cast ha

theorem transverseProjection_fixed {f : Field} (hf : transverse f) :
    transverseProjection f=f := by
  change f-gradientProjection f=f
  rw [gradientProjection_zero hf, sub_zero]

theorem gradientProjection_idempotent (f : Field) :
    gradientProjection (gradientProjection f)=gradientProjection f :=
  gradientProjection_fixed (gradientProjection_mem f)

theorem transverseProjection_idempotent (f : Field) :
    transverseProjection (transverseProjection f)=transverseProjection f :=
  transverseProjection_fixed (transverseProjection_mem f)

theorem decomposition (f : Field) : gradientProjection f+transverseProjection f=f := by
  change gradientProjection f+(f-gradientProjection f)=f
  abel

theorem projection_orthogonal (f : Field) :
    dotProduct (transverseProjection f) (gradientProjection f)=0 := by
  obtain ⟨φ, hφ⟩ := gradientProjection_mem f
  have h := transverseProjection_mem f φ
  rw [hφ] at h
  exact h

theorem gradientProjection_range : LinearMap.range gradientProjection = LinearMap.range localGradient := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact gradientProjection_mem f
  · intro f hf
    exact ⟨f, gradientProjection_fixed hf⟩

theorem gradientProjection_kernel : LinearMap.ker gradientProjection = transverseSpace := by
  ext f
  constructor
  · intro hf
    have hP : gradientProjection f=0 := hf
    have hQ : transverseProjection f=f := by
      change f-gradientProjection f=f
      rw [hP, sub_zero]
    have h := transverseProjection_mem f
    rw [hQ] at h
    exact h
  · intro hf
    exact gradientProjection_zero hf

theorem transverseProjection_range : LinearMap.range transverseProjection = transverseSpace := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact transverseProjection_mem f
  · intro f hf
    exact ⟨f, transverseProjection_fixed hf⟩

theorem transverseProjection_kernel : LinearMap.ker transverseProjection = LinearMap.range localGradient := by
  ext f
  constructor
  · intro hf
    have hQ : transverseProjection f=0 := hf
    have he := decomposition f
    rw [hQ, add_zero] at he
    rw [← he]
    exact gradientProjection_mem f
  · intro hf
    change f-gradientProjection f=0
    rw [gradientProjection_fixed hf, sub_self]

end OperatorDerivativeRewrite.Foundation.PeriodicLocalHodgeProjection
