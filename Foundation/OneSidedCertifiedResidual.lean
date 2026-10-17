import Foundation.OneSidedIntegerResponseData

/-! Transport the checked integer normal equations to the actual Schur compression. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedCertifiedResidual
open OneSidedBlockRank OneSidedCapComplex OneSidedBoundaryGauge OneSidedPinnedInterior
  OneSidedPhysicalProjection OneSidedBoundaryCycleData OneSidedBoundaryCycles
  OneSidedSourceMatrixData OneSidedIntegerResponseData OneSidedSchurCompression
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def interiorEquiv : Fin 32 ≃ Interior := Equiv.ofBijective interiorPoint interiorPoint_bijective

def faceEquiv : Fin 72 ≃ FullFace := Equiv.ofBijective facePoint facePoint_bijective

def responseMatrix : Matrix Interior (Fin 34) ℝ :=
  fun e j => (Xnum (interiorEquiv.symm e) j : ℝ)/(denominator : ℝ)

def residualMatrix : Matrix FullFace (Fin 34) ℝ :=
  fun p j => (signData (faceEquiv.symm p) : ℝ)*
    (Rnum (faceEquiv.symm p) j : ℝ)/(denominator : ℝ)

theorem denominator_real_positive : 0<(denominator : ℝ) := by
  exact_mod_cast denominator_positive

theorem response_at_point (i : Fin 32) (j : Fin 34) :
    responseMatrix (interiorPoint i) j=(Xnum i j : ℝ)/(denominator : ℝ) := by
  change (Xnum (interiorEquiv.symm (interiorEquiv i)) j : ℝ)/_= _
  rw [Equiv.symm_apply_apply]

theorem residual_at_point (r : Fin 72) (j : Fin 34) :
    residualMatrix (facePoint r) j=(signData r : ℝ)*(Rnum r j : ℝ)/(denominator : ℝ) := by
  change (signData (faceEquiv.symm (faceEquiv r)) : ℝ)*
    (Rnum (faceEquiv.symm (faceEquiv r)) j : ℝ)/_= _
  rw [Equiv.symm_apply_apply]

theorem sum_interior (f : Interior → ℝ) : (∑ i : Fin 32, f (interiorPoint i))=∑ e, f e :=
  interiorEquiv.sum_comp f

theorem sum_faces (f : FullFace → ℝ) : (∑ r : Fin 72, f (facePoint r))=∑ p, f p :=
  faceEquiv.sum_comp f

theorem real_response_equation (r : Fin 72) (j : Fin 34) :
    (∑ i : Fin 32, (Adata r i : ℝ)*(Xnum i j : ℝ))+
      (denominator : ℝ)*(∑ k : Fin 80, (Bdata r k : ℝ)*(cycleData k j : ℝ))=(Rnum r j : ℝ) := by
  exact_mod_cast response_equation r j

theorem real_normal_equation (i : Fin 32) (j : Fin 34) :
    (∑ r : Fin 72, (Adata r i : ℝ)*(Rnum r j : ℝ))=0 := by
  exact_mod_cast normal_equation i j

theorem sign_real_square (r : Fin 72) : (signData r : ℝ)*(signData r : ℝ)=1 := by
  exact_mod_cast sign_square r

theorem candidate_at_point (r : Fin 72) (j : Fin 34) :
    candidateResidual responseMatrix (facePoint r) j=residualMatrix (facePoint r) j := by
  simp only [candidateResidual,Matrix.add_apply,Matrix.mul_apply]
  rw [← sum_interior (fun e => fullMatrix (facePoint r) e*responseMatrix e j),
    ← sum_boundary (fun b => boundaryMatrix (facePoint r) b*cycleMatrix b j)]
  simp only [fullMatrix_at_points,response_at_point,boundaryMatrix_at_points,
    cycle_at_point,residual_at_point]
  have ha : (∑ i : Fin 32, ((signData r : ℝ)*(Adata r i : ℝ))*
      ((Xnum i j : ℝ)/(denominator : ℝ)))=
      ((signData r : ℝ)/(denominator : ℝ))*(∑ i : Fin 32, (Adata r i : ℝ)*(Xnum i j : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hb : (∑ k : Fin 80, ((signData r : ℝ)*(Bdata r k : ℝ))*(cycleData k j : ℝ))=
      (signData r : ℝ)*(∑ k : Fin 80, (Bdata r k : ℝ)*(cycleData k j : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [ha,hb,← real_response_equation r j]
  field_simp [ne_of_gt denominator_real_positive]
  <;> ring

theorem candidate_eq_residual : candidateResidual responseMatrix=residualMatrix := by
  ext p j
  obtain ⟨r,rfl⟩ := facePoint_bijective.surjective p
  exact candidate_at_point r j

theorem normal : fullMatrix.transpose*candidateResidual responseMatrix=0 := by
  rw [candidate_eq_residual]
  ext e j
  obtain ⟨i,rfl⟩ := interiorPoint_bijective.surjective e
  change (∑ p : FullFace, fullMatrix p (interiorPoint i)*residualMatrix p j)=0
  rw [← sum_faces (fun p => fullMatrix p (interiorPoint i)*residualMatrix p j)]
  simp only [fullMatrix_at_points,residual_at_point]
  calc
    _ = (∑ r : Fin 72, (Adata r i : ℝ)*(Rnum r j : ℝ))/(denominator : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      calc
        _ = ((signData r : ℝ)*(signData r : ℝ))*
            ((Adata r i : ℝ)*(Rnum r j : ℝ))/(denominator : ℝ) := by ring
        _ = _ := by rw [sign_real_square,one_mul]
    _ = 0 := by rw [real_normal_equation,zero_div]

theorem compressed_eq_residual_gram : compressed=residualMatrix.transpose*residualMatrix := by
  rw [← candidate_eq_residual]
  exact compressed_residual_gram responseMatrix normal

theorem compressed_entry (i j : Fin 34) : compressed i j=
    (∑ r : Fin 72, (Rnum r i : ℝ)*(Rnum r j : ℝ))/(denominator : ℝ)^2 := by
  rw [compressed_eq_residual_gram,Matrix.mul_apply]
  change (∑ p : FullFace, residualMatrix p i*residualMatrix p j)=_
  rw [← sum_faces (fun p => residualMatrix p i*residualMatrix p j),Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  rw [residual_at_point,residual_at_point]
  calc
    _ = ((signData r : ℝ)*(signData r : ℝ))*
        ((Rnum r i : ℝ)*(Rnum r j : ℝ))/(denominator : ℝ)^2 := by
      field_simp [ne_of_gt denominator_real_positive]
      <;> ring
    _ = _ := by rw [sign_real_square,one_mul]

theorem metric_entry (i j : Fin 34) : metric i j=
    ∑ k : Fin 80, (cycleData k i : ℝ)*(cycleData k j : ℝ) := by
  rw [metric,Matrix.mul_apply]
  change (∑ b : Boundary, cycleMatrix b i*cycleMatrix b j)=_
  rw [← sum_boundary (fun b => cycleMatrix b i*cycleMatrix b j)]
  simp only [cycle_at_point]

end OperatorDerivativeRewrite.Foundation.OneSidedCertifiedResidual
