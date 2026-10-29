import Foundation.FourCubeCompletedIntegerData
import Foundation.FourCubeTransverseMass

/-! Identify the new full32 source solution with the actual completed incidence Gram. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeCompletedResponse
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedBoundaryGauge
open OneSidedPinnedInterior OneSidedPhysicalProjection OneSidedSourceMatrixData
open OneSidedBoundaryCycleData OneSidedBoundaryCycles OneSidedCertifiedResidual
open FourCubeCubicCoordinates FourCubeMovingBoundaryQuadratic FourCubeMovingSchurLimit
open FourCubeIntegratedCubic SU2QuaternionOddWord

abbrev d : ℝ := (FourCubeCompletedIntegerData.denominator : ℝ)

def candidate (j : Fin 3) (e : Interior) : ℝ :=
  (FourCubeCompletedIntegerData.Xnum (interiorEquiv.symm e) j : ℝ)/d

def eta (j : Fin 3) (c : Boundary) : ℝ := (FourCubeHarmonicIntegerData.rawSource c j : ℝ)

def rval (j : Fin 3) (p : FullFace) : ℝ :=
  (signData (faceEquiv.symm p) : ℝ)*(FourCubeCompletedIntegerData.Rnum (faceEquiv.symm p) j : ℝ)/d

theorem d_positive : 0 < d := by norm_num [d,FourCubeCompletedIntegerData.denominator]

theorem candidate_point (i : Fin 32) (j : Fin 3) :
    candidate j (interiorPoint i)=(FourCubeCompletedIntegerData.Xnum i j : ℝ)/d := by
  change (FourCubeCompletedIntegerData.Xnum (interiorEquiv.symm (interiorEquiv i)) j : ℝ)/d=_
  rw [Equiv.symm_apply_apply]

theorem eta_point (k : Fin 80) (j : Fin 3) : eta j (point k)=(FourCubeHarmonicIntegerData.Bnum k j : ℝ) := by
  unfold eta
  rw [FourCubeHarmonicIntegerData.boundary_sources]

theorem rval_point (r : Fin 72) (j : Fin 3) :
    rval j (facePoint r)=(signData r : ℝ)*(FourCubeCompletedIntegerData.Rnum r j : ℝ)/d := by
  change (signData (faceEquiv.symm (faceEquiv r)) : ℝ)*
    (FourCubeCompletedIntegerData.Rnum (faceEquiv.symm (faceEquiv r)) j : ℝ)/d=_
  rw [Equiv.symm_apply_apply]

theorem residual_eq (j : Fin 3) :
    fullMatrix.mulVec (candidate j)+boundaryMatrix.mulVec (eta j)=rval j := by
  funext p
  obtain ⟨r,rfl⟩ := facePoint_bijective.surjective p
  change (∑ e : Interior,fullMatrix (facePoint r) e*candidate j e)+
    (∑ c : Boundary,boundaryMatrix (facePoint r) c*eta j c)=rval j (facePoint r)
  rw [← sum_interior (fun e => fullMatrix (facePoint r) e*candidate j e),
    ← sum_boundary (fun c => boundaryMatrix (facePoint r) c*eta j c)]
  simp only [fullMatrix_at_points,boundaryMatrix_at_points,candidate_point,eta_point,rval_point]
  have he : (∑ i : Fin 32,(Adata r i : ℝ)*(FourCubeCompletedIntegerData.Xnum i j : ℝ))+
      d*(∑ k : Fin 80,(Bdata r k : ℝ)*(FourCubeHarmonicIntegerData.Bnum k j : ℝ))=
        (FourCubeCompletedIntegerData.Rnum r j : ℝ) := by
    exact_mod_cast FourCubeCompletedIntegerData.residual_equations r j
  have ha : (∑ i : Fin 32,((signData r : ℝ)*(Adata r i : ℝ))*
      ((FourCubeCompletedIntegerData.Xnum i j : ℝ)/d))=
      ((signData r : ℝ)/d)*(∑ i : Fin 32,(Adata r i : ℝ)*(FourCubeCompletedIntegerData.Xnum i j : ℝ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hb : (∑ k : Fin 80,((signData r : ℝ)*(Bdata r k : ℝ))*(FourCubeHarmonicIntegerData.Bnum k j : ℝ))=
      (signData r : ℝ)*(∑ k : Fin 80,(Bdata r k : ℝ)*(FourCubeHarmonicIntegerData.Bnum k j : ℝ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  rw [ha,hb,← he]
  field_simp [d_positive.ne']


theorem full_normal (j : Fin 3) :
    fullMatrix.transpose.mulVec (rval j)+(fun e => FourCubeCompletedGram.weight e*candidate j e)=0 := by
  funext e
  obtain ⟨i,rfl⟩ := interiorPoint_bijective.surjective e
  change (∑ p : FullFace,fullMatrix p (interiorPoint i)*rval j p)+
    FourCubeCompletedGram.weight (interiorPoint i)*candidate j (interiorPoint i)=0
  rw [← sum_faces (fun p => fullMatrix p (interiorPoint i)*rval j p)]
  simp only [fullMatrix_at_points,rval_point,candidate_point]
  have hm : FourCubeCompletedGram.weight (interiorPoint i)=
      (FourCubeCompletedIntegerData.Mnum i : ℝ) := by
    unfold FourCubeCompletedGram.weight
    exact_mod_cast FourCubeCompletedIntegerData.multiplicities i
  rw [hm]
  have he : (∑ p : Fin 72,(Adata p i : ℝ)*(FourCubeCompletedIntegerData.Rnum p j : ℝ))+
      (FourCubeCompletedIntegerData.Mnum i : ℝ)*(FourCubeCompletedIntegerData.Xnum i j : ℝ)=0 := by
    exact_mod_cast FourCubeCompletedIntegerData.normal_equations i j
  have hs : (∑ p : Fin 72,((signData p : ℝ)*(Adata p i : ℝ))*
      ((signData p : ℝ)*(FourCubeCompletedIntegerData.Rnum p j : ℝ)/d))=
      (∑ p : Fin 72,(Adata p i : ℝ)*(FourCubeCompletedIntegerData.Rnum p j : ℝ))/d := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p _
    calc
      _ = ((signData p : ℝ)*(signData p : ℝ))*
          ((Adata p i : ℝ)*(FourCubeCompletedIntegerData.Rnum p j : ℝ))/d := by ring
      _ = _ := by rw [sign_real_square,one_mul]
  rw [hs]
  calc
    _ = ((∑ p : Fin 72,(Adata p i : ℝ)*(FourCubeCompletedIntegerData.Rnum p j : ℝ))+
        (FourCubeCompletedIntegerData.Mnum i : ℝ)*(FourCubeCompletedIntegerData.Xnum i j : ℝ))/d := by ring
    _ = 0 := by rw [he,zero_div]

/-- The source is the ACTUAL boundary incidence field, not a numerical proxy. -/
def forcing (j : Fin 3) : Field :=
  -(fullMatrix.transpose.mulVec (boundaryMatrix.mulVec (eta j)))

theorem gram_normal (j : Fin 3) :
    FourCubeCompletedGram.gram.mulVec (candidate j)=forcing j := by
  have h := full_normal j
  rw [← residual_eq,Matrix.mulVec_add,Matrix.mulVec_mulVec] at h
  unfold FourCubeCompletedGram.gram
  rw [Matrix.add_mulVec]
  have hd : (Matrix.diagonal FourCubeCompletedGram.weight).mulVec (candidate j)=
      fun e => FourCubeCompletedGram.weight e*candidate j e := by
    funext e
    exact Matrix.mulVec_diagonal _ _ _
  rw [hd]
  change fullGram.mulVec (candidate j)+
    (fun e => FourCubeCompletedGram.weight e*candidate j e)=forcing j
  unfold forcing
  change fullGram.mulVec (candidate j)+
    fullMatrix.transpose.mulVec (boundaryMatrix.mulVec (eta j))+
    (fun e => FourCubeCompletedGram.weight e*candidate j e)=0 at h
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_right_comm] using h)

theorem gram_injective : Function.Injective FourCubeCompletedGram.gram.mulVec := by
  intro f g h
  have hz : FourCubeCompletedGram.gram.mulVec (f-g)=0 := by
    rw [Matrix.mulVec_sub,h,sub_self]
  by_contra hn
  have hp := FourCubeCompletedGram.gram_positive (f-g) (sub_ne_zero.mpr hn)
  rw [hz,dotProduct_zero] at hp
  exact (lt_irrefl 0) hp

/-- Unique solution on ALL32 coordinates. No coordinate is pinned by definition. -/
theorem unique_response (j : Fin 3) (f : Field)
    (hf : FourCubeCompletedGram.gram.mulVec f=forcing j) : f=candidate j :=
  gram_injective (hf.trans (gram_normal j).symm)

theorem origin_response : candidate 0 pole= -1/231 ∧ candidate 1 pole= -16/2079 ∧
    candidate 2 pole= -1/231 := by
  have hp : interiorPoint 0=pole := by decide +kernel
  rw [← hp,candidate_point,candidate_point,candidate_point]
  norm_num [FourCubeCompletedIntegerData.Xnum,d,FourCubeCompletedIntegerData.denominator]

end OperatorDerivativeRewrite.Foundation.FourCubeCompletedResponse
