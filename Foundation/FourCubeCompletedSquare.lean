import Foundation.FourCubeFullHaarAsymptotic

/-! Full32 completed-square identity with the actual boundary incidence matrix.
The old pinned residual orthogonality is not assumed for this completed action. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeCompletedSquare
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedBoundaryGauge
open OneSidedPinnedInterior OneSidedPhysicalProjection

attribute [local irreducible] edges innerFaces upperFaces

def residual (f : Field) (eta : BoundaryField) : FullFace → ℝ :=
  fullMatrix.mulVec f+boundaryMatrix.mulVec eta

def coupling (eta : BoundaryField) : Field :=
  fullMatrix.transpose.mulVec (boundaryMatrix.mulVec eta)

def energy (f : Field) (eta : BoundaryField) : ℝ :=
  dotProduct (residual f eta) (residual f eta)+FourCubeCompletedGram.penalty f

theorem native_norm (f : Field) :
    dotProduct (fullMatrix.mulVec f) (fullMatrix.mulVec f)=realEnergy (extend f) := by
  rw [← Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec]
  change dotProduct f (fullGram.mulVec f)=_
  rw [fullGram_eq_gram,OneSidedGramSector.gram_energy]

theorem cross_pairing (f : Field) (eta : BoundaryField) :
    dotProduct (fullMatrix.mulVec f) (boundaryMatrix.mulVec eta)=dotProduct f (coupling eta) := by
  rw [dotProduct_comm,← Matrix.dotProduct_transpose_mulVec]
  rfl

theorem energy_expansion (f : Field) (eta : BoundaryField) :
    energy f eta=FourCubeCompletedGram.quadratic f+2*dotProduct f (coupling eta)+
      dotProduct (boundaryMatrix.mulVec eta) (boundaryMatrix.mulVec eta) := by
  unfold energy residual
  rw [add_dotProduct,dotProduct_add,dotProduct_add,native_norm,cross_pairing,
    dotProduct_comm (boundaryMatrix.mulVec eta) (fullMatrix.mulVec f),cross_pairing]
  unfold FourCubeCompletedGram.quadratic
  ring

theorem gram_pairing (f g : Field) :
    dotProduct f (FourCubeCompletedGram.gram.mulVec g)=
      dotProduct g (FourCubeCompletedGram.gram.mulVec f) := by
  have ht : FourCubeCompletedGram.gram.transpose=FourCubeCompletedGram.gram := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using FourCubeCompletedGram.gram_hermitian.eq
  rw [← Matrix.dotProduct_transpose_mulVec,ht]

theorem quadratic_sub (f m : Field) :
    FourCubeCompletedGram.quadratic (f-m)=FourCubeCompletedGram.quadratic f+
      FourCubeCompletedGram.quadratic m-2*dotProduct f (FourCubeCompletedGram.gram.mulVec m) := by
  simp only [← FourCubeCompletedGram.gram_energy,Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub]
  rw [gram_pairing m f]
  ring

/-- Cancellation includes the diagonal penalty; native orthogonality alone is false. -/
theorem completed_square (f m : Field) (eta : BoundaryField)
    (hn : FourCubeCompletedGram.gram.mulVec m+coupling eta=0) :
    energy f eta=energy m eta+FourCubeCompletedGram.quadratic (f-m) := by
  have hk : coupling eta= -(FourCubeCompletedGram.gram.mulVec m) := eq_neg_of_add_eq_zero_right hn
  rw [energy_expansion,energy_expansion,hk,dotProduct_neg,dotProduct_neg]
  have hm := FourCubeCompletedGram.gram_energy m
  have hs := quadratic_sub f m
  linarith

theorem unique_minimizer (f m : Field) (eta : BoundaryField)
    (hn : FourCubeCompletedGram.gram.mulVec m+coupling eta=0) :
    energy f eta=energy m eta ↔ f=m := by
  rw [completed_square f m eta hn,add_eq_left,FourCubeCompletedGram.quadratic_zero_iff,sub_eq_zero]

theorem energy_minimal (f m : Field) (eta : BoundaryField)
    (hn : FourCubeCompletedGram.gram.mulVec m+coupling eta=0) : energy m eta ≤ energy f eta := by
  rw [completed_square f m eta hn]
  exact le_add_of_nonneg_right (FourCubeCompletedGram.quadratic_nonneg _)

theorem candidate_normal (j : Fin 3) :
    FourCubeCompletedGram.gram.mulVec (FourCubeCompletedResponse.candidate j)+
      coupling (FourCubeCompletedResponse.eta j)=0 := by
  rw [FourCubeCompletedResponse.gram_normal]
  unfold FourCubeCompletedResponse.forcing coupling
  exact neg_add_cancel _

end OperatorDerivativeRewrite.Foundation.FourCubeCompletedSquare
