import Foundation.OneSidedBoundaryGap

/-! A physical interior test field strictly below every nonzero physical boundary quotient. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedGapComparison
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedBoundaryGauge
  OneSidedSourceMatrixData OneSidedPhysicalProjection OneSidedCertifiedResidual
  OneSidedBoundaryGap OneSidedSchurForm
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1000000

def uData : Fin 32 → ℤ := ![201,-67,-67,-67,76,32,32,76,32,32,20,4,76,32,32,20,4,20,4,8,-136,-136,-136,-12,-12,-12,-12,-4,-12,-12,-4,-4]

def cData : Fin 72 → ℤ := ![56,56,56,0,0,0,12,12,76,0,32,32,12,76,12,32,0,-32,4,20,20,4,4,76,12,12,-32,-32,0,20,4,20,-4,4,20,20,4,-4,-4,8,8,8,136,136,136,0,0,0,12,12,0,-12,-12,12,12,-12,0,12,4,-4,-4,12,12,12,12,0,4,4,-4,4,4,4]

def u : Field := fun e => (uData (interiorEquiv.symm e) : ℝ)

theorem integer_norm : (∑ i : Fin 32, uData i^2)=135052 := by decide +kernel

theorem integer_pairing :
    (∑ i : Fin 32, uData i*originStar (interiorPoint i).val)=0 := by decide +kernel

theorem integer_curvature : ∀ r : Fin 72,
    (∑ i : Fin 32, Adata r i*uData i)=cData r := by decide +kernel

theorem integer_energy : (∑ r : Fin 72, cData r^2)=93840 := by decide +kernel

theorem u_at_point (i : Fin 32) : u (interiorPoint i)=(uData i : ℝ) := by
  change (uData (interiorEquiv.symm (interiorEquiv i)) : ℝ)=_
  rw [Equiv.symm_apply_apply]

theorem gauge_at_point (i : Fin 32) :
    gauge (interiorPoint i)=(originStar (interiorPoint i).val : ℝ) := rfl

theorem u_norm : dotProduct u u=135052 := by
  change (∑ e : Interior, u e*u e)=_
  rw [← sum_interior (fun e => u e*u e)]
  simp only [u_at_point]
  simpa only [pow_two] using (show (∑ i : Fin 32, (uData i : ℝ)^2)=135052 by
    exact_mod_cast integer_norm)

theorem u_orthogonal : dotProduct u gauge=0 := by
  change (∑ e : Interior, u e*gauge e)=0
  rw [← sum_interior (fun e => u e*gauge e)]
  simp only [u_at_point,gauge_at_point]
  exact_mod_cast integer_pairing

theorem curvature_at_point (r : Fin 72) :
    fullMatrix.mulVec u (facePoint r)=(signData r : ℝ)*(cData r : ℝ) := by
  change (∑ e : Interior, fullMatrix (facePoint r) e*u e)=_
  rw [← sum_interior (fun e => fullMatrix (facePoint r) e*u e)]
  simp only [fullMatrix_at_points,u_at_point]
  have ht : (∑ i : Fin 32, (Adata r i : ℝ)*(uData i : ℝ))=(cData r : ℝ) := by
    exact_mod_cast integer_curvature r
  calc
    _ = (signData r : ℝ)*(∑ i : Fin 32, (Adata r i : ℝ)*(uData i : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [ht]

theorem curvature_energy : dotProduct (fullMatrix.mulVec u) (fullMatrix.mulVec u)=93840 := by
  change (∑ p : FullFace, fullMatrix.mulVec u p*fullMatrix.mulVec u p)=_
  rw [← sum_faces (fun p => fullMatrix.mulVec u p*fullMatrix.mulVec u p)]
  simp only [curvature_at_point]
  calc
    _ = ∑ r : Fin 72, (cData r : ℝ)^2 := by
      apply Finset.sum_congr rfl
      intro r _
      calc
        _ = ((signData r : ℝ)*(signData r : ℝ))*((cData r : ℝ)*(cData r : ℝ)) := by ring
        _ = _ := by rw [sign_real_square,one_mul]; ring
    _ = 93840 := by exact_mod_cast integer_energy

theorem u_energy : realEnergy (extend u)=93840 := by
  have ht : dotProduct u (fullGram.mulVec u)=
      dotProduct (fullMatrix.mulVec u) (fullMatrix.mulVec u) := by
    rw [fullGram,← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
  rw [fullGram_eq_gram,OneSidedGramSector.gram_energy] at ht
  exact ht.trans curvature_energy

theorem u_nonzero : u≠0 := by
  intro h
  have ht := u_norm
  rw [h,dotProduct_zero] at ht
  norm_num at ht

theorem u_rayleigh : realEnergy (extend u)/dotProduct u u=(23460/33763 : ℝ) := by
  rw [u_energy,u_norm]
  norm_num

theorem u_below_boundary_bound :
    realEnergy (extend u)<(69639/100000 : ℝ)*dotProduct u u := by
  rw [u_energy,u_norm]
  norm_num

theorem boundary_comparison (eta : BoundaryField) (hn : eta≠0)
    (ho : ∀ phi : Potential, dotProduct eta (boundaryGradient phi)=0) :
    realEnergy (extend u)/dotProduct u u<dotProduct eta (schur.mulVec eta)/dotProduct eta eta := by
  have hp : 0<dotProduct eta eta := by
    have hpos : 0≤dotProduct eta eta := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
    have hne : dotProduct eta eta≠0 := fun h => hn (dotProduct_self_eq_zero.mp h)
    exact lt_of_le_of_ne hpos (Ne.symm hne)
  calc
    _ = (23460/33763 : ℝ) := u_rayleigh
    _ < (69639/100000 : ℝ) := by norm_num
    _ ≤ _ := (le_div_iff₀ hp).mpr (boundary_gap eta ho)

end OperatorDerivativeRewrite.Foundation.OneSidedGapComparison
