import Foundation.SparseBlockGoodRegionObstruction

/-! Independent sparse coordinates and their actual ordinary partial Hessian. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SparseBlockPartialHessian
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open SparseBlockWilsonAction SparseWilsonCurvature SU2TraceHessianModel
open SU2MatrixExponentialBridge SU2ExponentialMembership SU2ProductCurveHessian
open SU2MixedLinkBlocks SU2OrderedLinkHessian ChristoffelSkewCancellation

def letterTwo (θ s t : ℝ) (l : Letter) : M2 :=
  if l.1=1 then letterMatrix θ s l else if l.1=2 then letterMatrix θ t l else letterMatrix θ 0 l
def evalTwo (θ s t : ℝ) (w : List Letter) : M2 := (w.map (letterTwo θ s t)).prod
def blockTwo (θ s t : ℝ) : ℝ := ∑ p∈faces, wilson (evalTwo θ s t (faceWord p))

theorem letterTwo_diag (θ t : ℝ) (l : Letter) : letterTwo θ t t l=letterMatrix θ t l := by
  rcases l with ⟨a,b⟩
  fin_cases a <;> cases b <;> simp [letterTwo, letterMatrix]

theorem blockTwo_diag (θ t : ℝ) : blockTwo θ t t=blockAction θ t := by
  have he : letterTwo θ t t=letterMatrix θ t := funext (letterTwo_diag θ t)
  simp [blockTwo, blockAction, evalTwo, evalWord, he]

theorem evalTwo_mem (θ s t : ℝ) (w : List Letter) :
    evalTwo θ s t w∈Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hl (l : Letter) : letterTwo θ s t l∈Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    unfold letterTwo
    split <;> first | exact letterMatrix_mem θ s l | skip
    split <;> first | exact letterMatrix_mem θ t l | exact letterMatrix_mem θ 0 l
  induction w with
  | nil => exact (Matrix.specialUnitaryGroup (Fin 2) ℂ).one_mem
  | cons l w ih =>
    change letterTwo θ s t l*evalTwo θ s t w∈Matrix.specialUnitaryGroup (Fin 2) ℂ
    exact (Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem (hl l) ih

theorem blockTwo_eq (θ s t : ℝ) :
    blockTwo θ s t=twoAction (rotation θ) (tangent 1) (tangent 0) s t+
      4*axisCurve 0 s+4*axisCurve 0 t+3*wilson (rotation θ) := by
  unfold blockTwo
  rw [sum_faceWord (fun w => wilson (evalTwo θ s t w))]
  norm_num [Fin.sum_univ_succ, SparseBlockWilsonAction.multiplicity, canonical,
    evalTwo, letterTwo, letterMatrix]
  have hx : (NormedSpace.exp (-(t • tangent 0)))⁻¹=NormedSpace.exp (t • tangent 0) := by
    rw [← Matrix.exp_neg, neg_neg]
  have hm : NormedSpace.exp (-(t • tangent 0))=NormedSpace.exp ((-t) • tangent 0) := by
    rw [neg_smul]
  rw [wilson_inv _ (rotation_unitary θ).1, wilson_inv _ (axis_unitary s 1), hx, hm,
    axis_action s 1, axis_action (-t) 0, axis_action t 0]
  have he : axisCurve 0 (-t)=axisCurve 0 t := by simp [axisCurve_eq, neg_div, Real.cos_neg]
  rw [he]
  have hw : wilson (1:M2)=0 := by norm_num [wilson, traceReal, Matrix.trace_one]
  rw [hw]
  simp only [twoAction, Matrix.mul_assoc]
  ring

def partialS (θ s t : ℝ) : ℝ :=
  firstSlope (rotation θ) (tangent 1) (tangent 0) s t+4*(Real.sin (s/2)/2)
def partialT (θ s t : ℝ) : ℝ :=
  secondSlope (rotation θ) (tangent 1) (tangent 0) s t+4*(Real.sin (t/2)/2)

theorem blockTwo_hasDerivAt_first (θ s t : ℝ) :
    HasDerivAt (fun u => blockTwo θ u t) (partialS θ s t) s := by
  have he : (fun u => blockTwo θ u t)=(fun u =>
      twoAction (rotation θ) (tangent 1) (tangent 0) u t+
        4*axisCurve 0 u+4*axisCurve 0 t+3*wilson (rotation θ)) :=
    funext (fun u => blockTwo_eq θ u t)
  rw [he]
  have hh := (((first_hasDerivAt (rotation θ) (tangent 1) (tangent 0) s t).add
    ((axisCurve_hasDerivAt 0 s).const_mul 4)).add
    (hasDerivAt_const s (4*axisCurve 0 t))).add (hasDerivAt_const s (3*wilson (rotation θ)))
  convert hh using 1 <;> first | rfl | (simp [partialS])

theorem blockTwo_hasDerivAt_second (θ s t : ℝ) :
    HasDerivAt (blockTwo θ s) (partialT θ s t) t := by
  have he : blockTwo θ s=(fun u =>
      twoAction (rotation θ) (tangent 1) (tangent 0) s u+
        4*axisCurve 0 s+4*axisCurve 0 u+3*wilson (rotation θ)) :=
    funext (fun u => blockTwo_eq θ s u)
  rw [he]
  have hh := (((second_hasDerivAt (rotation θ) (tangent 1) (tangent 0) s t).add
    (hasDerivAt_const t (4*axisCurve 0 s))).add
    ((axisCurve_hasDerivAt 0 t).const_mul 4)).add (hasDerivAt_const t (3*wilson (rotation θ)))
  convert hh using 1 <;> first | rfl | (simp [partialT])

theorem normalized_mixed_value (θ : ℝ) :
    -traceReal (rotation θ*tangent 1*tangent 0)/2= -Real.sin θ/4 := by
  norm_num [traceReal, rotation, tangent, generator, generatorX, generatorY, generatorZ,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Complex.mul_re, Complex.mul_im]
  simp only [Complex.sin_ofReal_re]
  ring

theorem blockTwo_mixed_ST (θ : ℝ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => blockTwo θ s t) 0) 0= -Real.sin θ/4 := by
  have he : (fun t : ℝ => deriv (fun s : ℝ => blockTwo θ s t) 0)=
      (fun t : ℝ => firstSlope (rotation θ) (tangent 1) (tangent 0) 0 t) := by
    funext t
    simpa [partialS] using (blockTwo_hasDerivAt_first θ 0 t).deriv
  rw [he]
  have hs : (fun t : ℝ => firstSlope (rotation θ) (tangent 1) (tangent 0) 0 t)=
      (fun t : ℝ => deriv (fun s : ℝ => twoAction (rotation θ) (tangent 1) (tangent 0) s t) 0) :=
    funext (fun t => (first_hasDerivAt (rotation θ) (tangent 1) (tangent 0) 0 t).deriv.symm)
  rw [hs, mixed_first_then_second, normalized_mixed_value]

theorem blockTwo_mixed_TS (θ : ℝ) :
    deriv (fun s : ℝ => deriv (blockTwo θ s) 0) 0= -Real.sin θ/4 := by
  have he : (fun s : ℝ => deriv (blockTwo θ s) 0)=
      (fun s : ℝ => secondSlope (rotation θ) (tangent 1) (tangent 0) s 0) := by
    funext s
    simpa [partialT] using (blockTwo_hasDerivAt_second θ s 0).deriv
  rw [he]
  have hs : (fun s : ℝ => secondSlope (rotation θ) (tangent 1) (tangent 0) s 0)=
      (fun s : ℝ => deriv (twoAction (rotation θ) (tangent 1) (tangent 0) s) 0) :=
    funext (fun s => (second_hasDerivAt (rotation θ) (tangent 1) (tangent 0) s 0).deriv.symm)
  rw [hs, mixed_second_then_first, normalized_mixed_value]

theorem axis_curvature_value (θ : ℝ) (a : Fin 3) :
    -traceReal (rotation θ*(tangent a)^2)/2=Real.cos θ/4 := by
  have hh := curve_second_derivative_model (rotation θ) (Pi.single a (1:ℝ))
  rw [curve_second_derivative, algebraElement_single, one_smul, quadratic_rotation] at hh
  simpa [Pi.single_apply] using hh

def axisSlice (θ : ℝ) (a : Fin 3) (k t : ℝ) : ℝ :=
  curve (rotation θ) (tangent a) t+4*axisCurve 0 t+k
def axisSliceSlope (θ : ℝ) (a : Fin 3) (t : ℝ) : ℝ :=
  SU2ProductCurveHessian.slope (rotation θ) (tangent a) t+4*(Real.sin (t/2)/2)

theorem axisSlice_hasDerivAt (θ : ℝ) (a : Fin 3) (k t : ℝ) :
    HasDerivAt (axisSlice θ a k) (axisSliceSlope θ a t) t := by
  have hh := ((curve_hasDerivAt (rotation θ) (tangent a) t).add
    ((axisCurve_hasDerivAt 0 t).const_mul 4)).add (hasDerivAt_const t k)
  convert hh using 1 <;> first | rfl | (simp [axisSliceSlope])

theorem axisSlice_second (θ : ℝ) (a : Fin 3) (k : ℝ) :
    deriv (deriv (axisSlice θ a k)) 0=(4+Real.cos θ)/4 := by
  have he : deriv (axisSlice θ a k)=axisSliceSlope θ a :=
    funext (fun t => (axisSlice_hasDerivAt θ a k t).deriv)
  rw [he]
  have hh := (slope_hasDerivAt (rotation θ) (tangent a) 0).add
    ((axisSlope_hasDerivAt 0 0).const_mul 4)
  have hf : (SU2ProductCurveHessian.slope (rotation θ) (tangent a)+
      (fun y : ℝ => 4*(Real.sin (0+y/2)/2)))=axisSliceSlope θ a := by
    funext u
    simp [axisSliceSlope]
  rw [hf] at hh
  have hv := hh.deriv
  simp only [zero_smul, NormedSpace.exp_zero, mul_one, zero_add, zero_div,
    Real.cos_zero, ← pow_two] at hv
  rw [axis_curvature_value] at hv
  linarith

theorem blockTwo_second_SS (θ : ℝ) :
    deriv (deriv (fun s : ℝ => blockTwo θ s 0)) 0=(4+Real.cos θ)/4 := by
  have he : (fun s : ℝ => blockTwo θ s 0)=axisSlice θ 1 (3*wilson (rotation θ)) := by
    funext s
    rw [blockTwo_eq]
    simp [twoAction, axisSlice, curve, axisCurve_eq]
  rw [he, axisSlice_second]

theorem blockTwo_second_TT (θ : ℝ) :
    deriv (deriv (blockTwo θ 0)) 0=(4+Real.cos θ)/4 := by
  have he : blockTwo θ 0=axisSlice θ 0 (3*wilson (rotation θ)) := by
    funext t
    rw [blockTwo_eq]
    simp [twoAction, axisSlice, curve, axisCurve_eq]
  rw [he, axisSlice_second]

def partialHessian (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![deriv (deriv (fun s : ℝ => blockTwo θ s 0)) 0,
      deriv (fun t : ℝ => deriv (fun s : ℝ => blockTwo θ s t) 0) 0;
     deriv (fun s : ℝ => deriv (blockTwo θ s) 0) 0,
      deriv (deriv (blockTwo θ 0)) 0]

theorem partialHessian_eq (θ : ℝ) :
    partialHessian θ=!![(4+Real.cos θ)/4,-Real.sin θ/4;
      -Real.sin θ/4,(4+Real.cos θ)/4] := by
  rw [partialHessian, blockTwo_second_SS, blockTwo_mixed_ST, blockTwo_mixed_TS, blockTwo_second_TT]

def reference : Matrix (Fin 2) (Fin 2) ℝ := (5/4:ℝ) • 1
def errorMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := partialHessian θ-reference

theorem reference_at_zero : partialHessian 0=reference := by
  rw [partialHessian_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [reference]

theorem error_eigen_same (θ : ℝ) :
    (errorMatrix θ).mulVec ![1,1]=((Real.cos θ-1-Real.sin θ)/4) • ![1,1] := by
  ext i
  change (∑ j : Fin 2, errorMatrix θ i j*(![1,1] : Fin 2 → ℝ) j)=_
  fin_cases i <;> norm_num [errorMatrix, partialHessian_eq, reference,
    Fin.sum_univ_two] <;> ring

theorem error_eigen_opposite (θ : ℝ) :
    (errorMatrix θ).mulVec ![1,-1]=((Real.cos θ-1+Real.sin θ)/4) • ![1,-1] := by
  ext i
  change (∑ j : Fin 2, errorMatrix θ i j*(![1,-1] : Fin 2 → ℝ) j)=_
  fin_cases i <;> norm_num [errorMatrix, partialHessian_eq, reference,
    Fin.sum_univ_two] <;> ring

theorem partialHessian_diagonal_curve (θ : ℝ) :
    contraction (partialHessian θ) ![1,1] ![1,1]=deriv (deriv (blockAction θ)) 0 := by
  rw [partialHessian_eq, blockAction_second_derivative]
  norm_num [contraction, Fin.sum_univ_two, curvatureValue]
  ring

theorem error_eigen_same_slope :
    HasDerivAt (fun θ : ℝ => (Real.cos θ-1-Real.sin θ)/4) (-1/4) 0 := by
  have hh := (((Real.hasDerivAt_cos 0).sub_const 1).sub (Real.hasDerivAt_sin 0)).div_const 4
  simpa using hh

theorem error_eigen_opposite_slope :
    HasDerivAt (fun θ : ℝ => (Real.cos θ-1+Real.sin θ)/4) (1/4) 0 := by
  have hh := (((Real.hasDerivAt_cos 0).sub_const 1).add (Real.hasDerivAt_sin 0)).div_const 4
  simpa using hh

theorem restricted_coercive (θ : ℝ) (v : Fin 2 → ℝ) :
    (1/2:ℝ)*(∑ i, (v i)^2) ≤ contraction (partialHessian θ) v v := by
  have ht : 0 ≤ (v 0)^2+(v 1)^2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hc := mul_nonneg (show 0 ≤ 1+Real.cos θ by linarith [Real.neg_one_le_cos θ]) ht
  have hp := mul_nonneg (show 0 ≤ 1-Real.sin θ by linarith [Real.sin_le_one θ])
    (sq_nonneg (v 0+v 1))
  have hm := mul_nonneg (show 0 ≤ 1+Real.sin θ by linarith [Real.neg_one_le_sin θ])
    (sq_nonneg (v 0-v 1))
  rw [partialHessian_eq]
  norm_num [contraction, Fin.sum_univ_two]
  nlinarith

theorem coordinate_norms :
    (∑ e∈OneSidedBlockIncidence.edges, (xDirection e)^2)=1 ∧
      (∑ e∈OneSidedBlockIncidence.edges, (yDirection e)^2)=1 := by decide

theorem coordinate_energies :
    OneSidedBlockIncidence.energy xDirection=5 ∧ OneSidedBlockIncidence.energy yDirection=5 := by decide

theorem coordinate_norm_form (s t : ℝ) :
    (∑ e∈OneSidedBlockIncidence.edges,
      ((s*(yDirection e:ℝ))^2+(t*(xDirection e:ℝ))^2))=s^2+t^2 := by
  have hx : (∑ e∈OneSidedBlockIncidence.edges, (xDirection e:ℝ)^2)=1 := by
    exact_mod_cast coordinate_norms.1
  have hy : (∑ e∈OneSidedBlockIncidence.edges, (yDirection e:ℝ)^2)=1 := by
    exact_mod_cast coordinate_norms.2
  simp_rw [mul_pow]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx, hy]
  ring

theorem realEnergy_scaled (c : ℝ) (f : OneSidedBlockIncidence.EdgeData → ℝ) :
    OneSidedBlockIncidence.realEnergy (fun e => c*f e)=c^2*OneSidedBlockIncidence.realEnergy f := by
  have hc (p : OneSidedBlockIncidence.FaceData) :
      OneSidedBlockIncidence.realCurl (fun e => c*f e) p=c*OneSidedBlockIncidence.realCurl f p := by
    unfold OneSidedBlockIncidence.realCurl
    ring
  unfold OneSidedBlockIncidence.realEnergy
  simp_rw [hc, mul_pow]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem coordinate_reference_form (s t : ℝ) :
    (OneSidedBlockIncidence.realEnergy (fun e => s*(yDirection e:ℝ))+
      OneSidedBlockIncidence.realEnergy (fun e => t*(xDirection e:ℝ)))/4=
      (5/4:ℝ)*(s^2+t^2) := by
  have hx : OneSidedBlockIncidence.realEnergy (fun e => (xDirection e:ℝ))=5 := by
    rw [realEnergy_cast, coordinate_energies.1]
    norm_num
  have hy : OneSidedBlockIncidence.realEnergy (fun e => (yDirection e:ℝ))=5 := by
    rw [realEnergy_cast, coordinate_energies.2]
    norm_num
  rw [realEnergy_scaled, realEnergy_scaled, hx, hy]
  ring

theorem restricted_relative_violation :
    let θ := witnessAngle
    contraction (errorMatrix θ) ![1,1] ![1,1] <
      (Real.sin (3*θ)/(3*θ)-1)*(10/4)-9*(3*θ)^2*2 := by
  dsimp only
  have hv := SparseBlockRelativeObstruction.rational_slack_three
  rw [blockAction_second_derivative] at hv
  unfold SparseBlockRelativeObstruction.relativeLower curvatureValue at hv
  norm_num [errorMatrix, partialHessian_eq, reference, contraction, Fin.sum_univ_two]
  linarith

end OperatorDerivativeRewrite.Foundation.SparseBlockPartialHessian
