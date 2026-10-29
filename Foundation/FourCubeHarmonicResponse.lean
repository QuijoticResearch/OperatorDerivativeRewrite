import Foundation.FourCubeHarmonicIntegerData

/-! Identify the direct finite integer witness with the actual pinned harmonic response. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeHarmonicResponse
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedBoundaryGauge
open OneSidedPinnedInterior OneSidedPhysicalProjection OneSidedSourceMatrixData
open OneSidedBoundaryCycleData OneSidedBoundaryCycles OneSidedCertifiedResidual
open FourCubeCubicCoordinates FourCubeMovingBoundaryQuadratic FourCubeMovingSchurLimit
open FourCubeIntegratedCubic SU2QuaternionOddWord

abbrev d : ℝ := (FourCubeHarmonicIntegerData.denominator : ℝ)

def candidate (j : Fin 3) (e : Interior) : ℝ :=
  (FourCubeHarmonicIntegerData.Xnum (interiorEquiv.symm e) j : ℝ)/d

def eta (j : Fin 3) (c : Boundary) : ℝ := (FourCubeHarmonicIntegerData.rawSource c j : ℝ)

def rval (j : Fin 3) (p : FullFace) : ℝ :=
  (signData (faceEquiv.symm p) : ℝ)*(FourCubeHarmonicIntegerData.Rnum (faceEquiv.symm p) j : ℝ)/d

theorem d_positive : 0 < d := by norm_num [d,FourCubeHarmonicIntegerData.denominator]

theorem candidate_point (i : Fin 32) (j : Fin 3) :
    candidate j (interiorPoint i)=(FourCubeHarmonicIntegerData.Xnum i j : ℝ)/d := by
  change (FourCubeHarmonicIntegerData.Xnum (interiorEquiv.symm (interiorEquiv i)) j : ℝ)/d=_
  rw [Equiv.symm_apply_apply]

theorem eta_point (k : Fin 80) (j : Fin 3) : eta j (point k)=(FourCubeHarmonicIntegerData.Bnum k j : ℝ) := by
  unfold eta
  rw [FourCubeHarmonicIntegerData.boundary_sources]

theorem rval_point (r : Fin 72) (j : Fin 3) :
    rval j (facePoint r)=(signData r : ℝ)*(FourCubeHarmonicIntegerData.Rnum r j : ℝ)/d := by
  change (signData (faceEquiv.symm (faceEquiv r)) : ℝ)*
    (FourCubeHarmonicIntegerData.Rnum (faceEquiv.symm (faceEquiv r)) j : ℝ)/d=_
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
  have he : (∑ i : Fin 32,(Adata r i : ℝ)*(FourCubeHarmonicIntegerData.Xnum i j : ℝ))+
      d*(∑ k : Fin 80,(Bdata r k : ℝ)*(FourCubeHarmonicIntegerData.Bnum k j : ℝ))=
        (FourCubeHarmonicIntegerData.Rnum r j : ℝ) := by
    exact_mod_cast FourCubeHarmonicIntegerData.residual_equations r j
  have ha : (∑ i : Fin 32,((signData r : ℝ)*(Adata r i : ℝ))*
      ((FourCubeHarmonicIntegerData.Xnum i j : ℝ)/d))=
      ((signData r : ℝ)/d)*(∑ i : Fin 32,(Adata r i : ℝ)*(FourCubeHarmonicIntegerData.Xnum i j : ℝ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hb : (∑ k : Fin 80,((signData r : ℝ)*(Bdata r k : ℝ))*(FourCubeHarmonicIntegerData.Bnum k j : ℝ))=
      (signData r : ℝ)*(∑ k : Fin 80,(Bdata r k : ℝ)*(FourCubeHarmonicIntegerData.Bnum k j : ℝ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  rw [ha,hb,← he]
  field_simp [d_positive.ne']
  <;> ring

theorem full_normal (j : Fin 3) : fullMatrix.transpose.mulVec (rval j)=0 := by
  funext e
  obtain ⟨i,rfl⟩ := interiorPoint_bijective.surjective e
  change (∑ p : FullFace,fullMatrix p (interiorPoint i)*rval j p)=0
  rw [← sum_faces (fun p => fullMatrix p (interiorPoint i)*rval j p)]
  simp only [fullMatrix_at_points,rval_point]
  have he : (∑ p : Fin 72,(Adata p i : ℝ)*(FourCubeHarmonicIntegerData.Rnum p j : ℝ))=0 := by
    exact_mod_cast FourCubeHarmonicIntegerData.normal_equations i j
  calc
    _ = (∑ p : Fin 72,(Adata p i : ℝ)*(FourCubeHarmonicIntegerData.Rnum p j : ℝ))/d := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p _
      calc
        _ = ((signData p : ℝ)*(signData p : ℝ))*
            ((Adata p i : ℝ)*(FourCubeHarmonicIntegerData.Rnum p j : ℝ))/d := by ring
        _ = _ := by rw [sign_real_square,one_mul]
    _ = 0 := by rw [he,zero_div]

theorem candidate_pole (j : Fin 3) : candidate j pole=0 := by
  have hp : interiorPoint 0=pole := by decide +kernel
  rw [← hp,candidate_point]
  have hz := congrFun FourCubeHarmonicIntegerData.pinned_row j
  simp only [Pi.zero_apply] at hz
  rw [hz,Int.cast_zero,zero_div]

def chart : FourCubeMovingOddAction.Coordinates := fun e j => candidate j e.val

theorem candidate_lift (j : Fin 3) : lift (fun e : Free => chart e j)=candidate j := by
  funext e
  by_cases hp : e=pole
  · subst e; rw [lift_pole,candidate_pole]
  · change (if h : e=pole then 0 else candidate j e)=candidate j e
    simp [hp]

theorem response_eq (j : Fin 3) : OneSidedSchurForm.response (eta j)=(fun e : Free => chart e j) := by
  apply localGram_injective
  have hn := congrArg (fun z => liftMatrix.transpose.mulVec z) (full_normal j)
  rw [← residual_eq] at hn
  rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,fullMatrix_lift,Matrix.mulVec_zero] at hn
  have hc : fullMatrix.mulVec (candidate j)=localMatrix.mulVec (fun e : Free => chart e j) := by
    rw [← fullMatrix_lift,← Matrix.mulVec_mulVec,liftMatrix_mulVec,candidate_lift]
  rw [hc,Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec] at hn
  change localGram.mulVec (fun e : Free => chart e j)+OneSidedSchurForm.coupling.mulVec (eta j)=0 at hn
  rw [OneSidedSchurForm.response,Matrix.mulVec_neg,local_inverse_solve]
  exact (eq_neg_of_add_eq_zero_left hn).symm

theorem raw_boundary_unit (c : Boundary) :
    rawBoundary 1 1 1 c=(fun j => (FourCubeHarmonicIntegerData.rawSource c j : ℝ)) := by
  ext j
  cases c <;> fin_cases j <;>
    simp only [rawBoundary,boundaryVector,FourCubeHarmonicIntegerData.rawSource]
    <;> split_ifs <;> norm_num [SU2AxisMatrixJets.axisVector]

theorem boundary_component_unit (a : Fin 3) :
    boundaryComponent 1 1 1 a=(2 : ℝ) • eta (![1,2,0] a) := by
  funext c
  have he := raw_boundary_unit c
  fin_cases a
  · have hh := congrFun he 1
    change boundaryVector 1 1 1 c 0/2=(FourCubeHarmonicIntegerData.rawSource c 1 : ℝ) at hh
    change boundaryVector 1 1 1 c 0=2*(FourCubeHarmonicIntegerData.rawSource c 1 : ℝ)
    linarith
  · have hh := congrFun he 2
    change boundaryVector 1 1 1 c 1/2=(FourCubeHarmonicIntegerData.rawSource c 2 : ℝ) at hh
    change boundaryVector 1 1 1 c 1=2*(FourCubeHarmonicIntegerData.rawSource c 2 : ℝ)
    linarith
  · have hh := congrFun he 0
    change boundaryVector 1 1 1 c 2/2=(FourCubeHarmonicIntegerData.rawSource c 0 : ℝ) at hh
    change boundaryVector 1 1 1 c 2=2*(FourCubeHarmonicIntegerData.rawSource c 0 : ℝ)
    linarith

theorem response_two (j : Fin 3) :
    OneSidedSchurForm.response ((2 : ℝ) • eta j)=(2 : ℝ) • OneSidedSchurForm.response (eta j) := by
  unfold OneSidedSchurForm.response
  simp only [Matrix.mulVec_smul,smul_neg]

theorem harmonic_eq_chart : harmonicShift 1 1 1=chart := by
  funext e a
  fin_cases a <;> simp only [harmonicShift,boundary_component_unit,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,response_two,response_eq,
    Pi.smul_apply,smul_eq_mul] <;> ring <;> rfl

end OperatorDerivativeRewrite.Foundation.FourCubeHarmonicResponse
