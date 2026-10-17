import Foundation.OneSidedBlockIncidence
import Foundation.SparseWilsonCurvature

/-! Exact sparse face words in the one-sided block, before any curvature-bound identification. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SparseBlockWilsonAction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
open OneSidedBlockIncidence SU2TraceHessianModel SU2MatrixExponentialBridge
open SU2ExponentialMembership SU2ProductCurveHessian SU2OrderedLinkHessian

def base : Vertex := ![1,0,0,0]
def backgroundEdge : EdgeData := (base,1)
def yEdge : EdgeData := (shifted base 1,2)
def minusXEdge : EdgeData := (shifted base 2,1)
def mark (e : EdgeData) : Option (Fin 3) :=
  if e=backgroundEdge then some 0 else if e=yEdge then some 1 else
    if e=minusXEdge then some 2 else none
abbrev Letter := Fin 3 × Bool
def edgeWord (e : EdgeData) (positive : Bool) : List Letter :=
  match mark e with | none => [] | some a => [(a,positive)]
def innerWord (p : FaceData) : List Letter :=
  edgeWord (p.1,p.2.1) true ++ edgeWord (shifted p.1 p.2.1,p.2.2) true ++
    edgeWord (shifted p.1 p.2.2,p.2.1) false ++ edgeWord (p.1,p.2.2) false
def upperWord (p : EdgeData × Fin 4) : List Letter :=
  edgeWord p.1 (decide (p.1.2 < p.2))
abbrev Face := FaceData ⊕ (EdgeData × Fin 4)
def faces : Finset Face := innerFaces.disjSum upperFaces
def faceWord : Face → List Letter := Sum.elim innerWord upperWord
def canonical (c : Fin 8) : List Letter :=
  ![[],[(0,true)],[(0,false)],[(2,true)],[(2,false)],[(1,true)],[(1,false)],
    [(0,true),(1,true),(2,false)]] c
def wordClass (w : List Letter) : Fin 8 :=
  if w=canonical 1 then 1 else if w=canonical 2 then 2 else
  if w=canonical 3 then 3 else if w=canonical 4 then 4 else
  if w=canonical 5 then 5 else if w=canonical 6 then 6 else
  if w=canonical 7 then 7 else 0
def multiplicity : Fin 8 → ℕ := ![60,2,1,3,1,2,2,1]

theorem faces_card : faces.card=72 := by decide
theorem canonical_faceWord : ∀ p∈faces, canonical (wordClass (faceWord p))=faceWord p := by decide
theorem wordClass_card : ∀ c : Fin 8,
    (faces.filter (fun p => wordClass (faceWord p)=c)).card=multiplicity c := by decide

theorem sum_faceWord (F : List Letter → ℝ) :
    (∑ p∈faces, F (faceWord p))=∑ c : Fin 8, (multiplicity c:ℝ)*F (canonical c) := by
  calc
    _ = ∑ p∈faces, ∑ c : Fin 8,
        if wordClass (faceWord p)=c then F (canonical c) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [canonical_faceWord p hp]
    _ = ∑ c : Fin 8, ∑ p∈faces,
        if wordClass (faceWord p)=c then F (canonical c) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← Finset.sum_filter]
      simp [wordClass_card]

def letterMatrix (θ t : ℝ) (l : Letter) : M2 :=
  let U := ![rotation θ, NormedSpace.exp (t • tangent 1),
    NormedSpace.exp (t • (-tangent 0))] l.1
  if l.2 then U else U⁻¹
def evalWord (θ t : ℝ) (w : List Letter) : M2 := (w.map (letterMatrix θ t)).prod
def blockAction (θ t : ℝ) : ℝ := ∑ p∈faces, wilson (evalWord θ t (faceWord p))

theorem wilson_inv (U : M2) (hU : Uᴴ*U=1) : wilson U⁻¹=wilson U := by
  rw [Matrix.inv_eq_left_inv hU]
  simp [wilson, traceReal, Matrix.trace_conjTranspose]

theorem algebraElement_single (t : ℝ) (a : Fin 3) :
    algebraElement (Pi.single a t)=t • tangent a := by
  have h1 : algebraElement (Pi.single a (1:ℝ))=tangent a := by
    fin_cases a <;> simp [algebraElement, Fin.sum_univ_three, Pi.single_apply]
  have hv : Pi.single a t=t • Pi.single a (1:ℝ) := by
    ext b
    by_cases h : a=b <;> simp [Pi.single_apply, h]
  rw [hv, algebraElement_smul, h1]

theorem axis_action (t : ℝ) (a : Fin 3) :
    wilson (NormedSpace.exp (t • tangent a))=axisCurve 0 t := by
  have he := algebraElement_single t a
  have hl : lengthSq (Pi.single a t)=t^2 := by
    simp [lengthSq, Pi.single_apply]
  rw [← he, algebraElement_exp_wilson, axisCurve_eq]
  simp only [angle, hl, Real.sqrt_sq_eq_abs, zero_add]
  have ha : |t|/2=|t/2| := by rw [abs_div]; norm_num
  rw [ha, Real.cos_abs]

theorem axis_unitary (t : ℝ) (a : Fin 3) :
    (NormedSpace.exp (t • tangent a))ᴴ*NormedSpace.exp (t • tangent a)=1 := by
  have he := algebraElement_single t a
  rw [← he]
  exact algebraElement_exp_unitary_left _

theorem blockAction_eq (θ t : ℝ) :
    blockAction θ t=action (rotation θ) (tangent 1) (tangent 0) t+
      8*axisCurve 0 t+3*wilson (rotation θ) := by
  unfold blockAction
  rw [sum_faceWord (fun w => wilson (evalWord θ t w))]
  norm_num [Fin.sum_univ_succ, multiplicity, canonical, evalWord, letterMatrix]
  have hx : (NormedSpace.exp (-(t • tangent 0)))⁻¹=NormedSpace.exp (t • tangent 0) := by
    rw [← Matrix.exp_neg, neg_neg]
  have hxm : NormedSpace.exp (-(t • tangent 0))=NormedSpace.exp ((-t) • tangent 0) := by
    rw [neg_smul]
  rw [wilson_inv _ (rotation_unitary θ).1,
    wilson_inv _ (axis_unitary t 1), hx, hxm,
    axis_action t 1, axis_action (-t) 0, axis_action t 0]
  have ha : axisCurve 0 (-t)=axisCurve 0 t := by
    simp [axisCurve_eq, neg_div, Real.cos_neg]
  rw [ha]
  have hw : wilson (1:M2)=0 := by norm_num [wilson, traceReal, Matrix.trace_one]
  rw [hw]
  unfold action matrixPath
  ring

def xDirection (e : EdgeData) : ℤ := if e=minusXEdge then -1 else 0
def yDirection (e : EdgeData) : ℤ := if e=yEdge then 1 else 0
theorem direction_norm_sq :
    (∑ e∈edges, ((xDirection e)^2+(yDirection e)^2))=2 := by decide
theorem direction_incidence_energy : energy xDirection+energy yDirection=10 := by decide
theorem direction_origin_orthogonal :
    (∑ e∈edges, originStar e*xDirection e)=0 ∧
      (∑ e∈edges, originStar e*yDirection e)=0 := by decide

def markedMatrix (θ t : ℝ) (a : Fin 3) : M2 := letterMatrix θ t (a,true)
def linkMatrix (θ t : ℝ) (e : EdgeData) : M2 :=
  match mark e with | none => 1 | some a => markedMatrix θ t a

theorem evalWord_append (θ t : ℝ) (w z : List Letter) :
    evalWord θ t (w++z)=evalWord θ t w*evalWord θ t z := by
  simp [evalWord, List.prod_append]

theorem edgeWord_eval (θ t : ℝ) (e : EdgeData) (b : Bool) :
    evalWord θ t (edgeWord e b)=if b then linkMatrix θ t e else (linkMatrix θ t e)⁻¹ := by
  cases hm : mark e <;> cases b <;>
    simp [edgeWord, evalWord, letterMatrix, linkMatrix, markedMatrix, hm]

theorem innerWord_actual (θ t : ℝ) (p : FaceData) :
    evalWord θ t (innerWord p)=linkMatrix θ t (p.1,p.2.1)*
      linkMatrix θ t (shifted p.1 p.2.1,p.2.2)*
      (linkMatrix θ t (shifted p.1 p.2.2,p.2.1))⁻¹*(linkMatrix θ t (p.1,p.2.2))⁻¹ := by
  simp [innerWord, evalWord_append, edgeWord_eval, Matrix.mul_assoc]

theorem upperWord_actual (θ t : ℝ) (p : EdgeData × Fin 4) :
    evalWord θ t (upperWord p)=
      if p.1.2 < p.2 then linkMatrix θ t p.1 else (linkMatrix θ t p.1)⁻¹ := by
  by_cases h : p.1.2 < p.2 <;> simp [upperWord, edgeWord_eval, h]

theorem markedMatrix_mem (θ t : ℝ) (a : Fin 3) :
    markedMatrix θ t a ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  fin_cases a
  · exact testLinks_mem θ t 0
  · exact testLinks_mem θ t 1
  · exact testLinks_mem θ t 2

theorem matrix_inv_mem (U : M2) (hU : U∈Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U⁻¹∈Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hi : Uᴴ*U=1 := hU.1.1
  rw [Matrix.inv_eq_left_inv hi]
  exact (star (⟨U,hU⟩ : Matrix.specialUnitaryGroup (Fin 2) ℂ)).property

theorem linkMatrix_mem (θ t : ℝ) (e : EdgeData) :
    linkMatrix θ t e∈Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  cases hm : mark e with
  | none => simp [linkMatrix, hm]
  | some a => simpa only [linkMatrix, hm] using markedMatrix_mem θ t a

theorem letterMatrix_mem (θ t : ℝ) (l : Letter) :
    letterMatrix θ t l∈Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rcases l with ⟨a,b⟩
  cases b
  · exact matrix_inv_mem _ (markedMatrix_mem θ t a)
  · exact markedMatrix_mem θ t a

theorem evalWord_mem (θ t : ℝ) (w : List Letter) :
    evalWord θ t w∈Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  induction w with
  | nil => exact (Matrix.specialUnitaryGroup (Fin 2) ℂ).one_mem
  | cons l w ih =>
    change letterMatrix θ t l*evalWord θ t w∈Matrix.specialUnitaryGroup (Fin 2) ℂ
    exact (Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem (letterMatrix_mem θ t l) ih

theorem base_holonomies (θ : ℝ) (p : Face) (hp : p∈faces) :
    evalWord θ 0 (faceWord p)=1 ∨ evalWord θ 0 (faceWord p)=rotation θ ∨
      evalWord θ 0 (faceWord p)=(rotation θ)⁻¹ := by
  rw [← canonical_faceWord p hp]
  generalize wordClass (faceWord p)=c
  fin_cases c <;> simp [canonical, evalWord, letterMatrix]

theorem realEnergy_cast (f : EdgeData → ℤ) :
    realEnergy (fun e => (f e:ℝ))=(energy f:ℝ) := by
  simp [realEnergy, realCurl, energy, curl]

theorem real_direction_norm_sq :
    (∑ e∈edges, (((xDirection e:ℝ)^2)+((yDirection e:ℝ)^2)))=2 := by
  exact_mod_cast direction_norm_sq

theorem real_direction_energy :
    realEnergy (fun e => (xDirection e:ℝ))+realEnergy (fun e => (yDirection e:ℝ))=10 := by
  rw [realEnergy_cast, realEnergy_cast]
  exact_mod_cast direction_incidence_energy

theorem blockAction_reduced (θ : ℝ) : blockAction θ=SparseWilsonCurvature.reducedAction θ :=
  funext (fun t => blockAction_eq θ t)

theorem blockAction_second_derivative (θ : ℝ) :
    deriv (deriv (blockAction θ)) 0=SparseWilsonCurvature.curvatureValue θ := by
  rw [blockAction_reduced]
  exact SparseWilsonCurvature.reducedAction_second_derivative θ

theorem rational_bound_violation :
    deriv (deriv (blockAction SparseWilsonCurvature.witnessAngle)) 0 <
      SparseWilsonCurvature.proposedLower SparseWilsonCurvature.witnessAngle := by
  rw [blockAction_second_derivative]
  exact SparseWilsonCurvature.rational_angle_strict

end OperatorDerivativeRewrite.Foundation.SparseBlockWilsonAction
