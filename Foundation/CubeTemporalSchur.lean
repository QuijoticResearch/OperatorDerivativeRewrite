import Foundation.CubeSlabSecondVariation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Exact temporal Schur geometry of the actual cube. These are Hessian-level
identities, not a Gaussian convergence or Yang--Mills mass-gap theorem. -/
noncomputable section
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.CubeTemporalSchur
open CubeTemporalSlab CubeAxialSlice CubeSlabSecondVariation
private instance vertexDecidableEq : DecidableEq SpatialVertex :=
  fun v w => decidable_of_decidable_of_iff (p := ∀ i,v i=w i) funext_iff.symm

private def Dq : Matrix (Fin 12) (Fin 7) ℚ :=
  !![(0),(0),(0),(1),(0),(0),(0);
    (0),(1),(0),(0),(0),(0),(0);
    (1),(0),(0),(0),(0),(0),(0);
    (-1),(0),(0),(0),(1),(0),(0);
    (-1),(0),(1),(0),(0),(0),(0);
    (0),(-1),(0),(0),(0),(1),(0);
    (0),(-1),(1),(0),(0),(0),(0);
    (0),(0),(-1),(0),(0),(0),(1);
    (0),(0),(0),(-1),(0),(1),(0);
    (0),(0),(0),(-1),(1),(0),(0);
    (0),(0),(0),(0),(-1),(0),(1);
    (0),(0),(0),(0),(0),(-1),(1)]

private def Bq : Matrix (Fin 12) (Fin 5) ℚ :=
  !![(0),(0),(0),(0),(0);
    (0),(0),(0),(0),(0);
    (0),(0),(0),(0),(0);
    (0),(1),(0),(0),(0);
    (0),(0),(0),(1),(0);
    (1),(0),(0),(0),(0);
    (0),(0),(0),(0),(0);
    (0),(0),(1),(0),(0);
    (0),(0),(0),(0),(0);
    (0),(0),(0),(0),(0);
    (0),(0),(0),(0),(1);
    (0),(0),(0),(0),(0)]

private def Liq : Matrix (Fin 7) (Fin 7) ℚ :=
  !![(7/12),(5/24),(3/8),(5/24),(3/8),(1/4),(1/3);
    (5/24),(7/12),(3/8),(5/24),(1/4),(3/8),(1/3);
    (3/8),(3/8),(3/4),(1/4),(3/8),(3/8),(1/2);
    (5/24),(5/24),(1/4),(7/12),(3/8),(3/8),(1/3);
    (3/8),(1/4),(3/8),(3/8),(3/4),(3/8),(1/2);
    (1/4),(3/8),(3/8),(3/8),(3/8),(3/4),(1/2);
    (1/3),(1/3),(1/2),(1/3),(1/2),(1/2),(5/6)]

private def Aq : Matrix (Fin 7) (Fin 5) ℚ :=
  !![(-1/24),(5/24),(1/24),(5/24),(1/24);
    (5/24),(-1/24),(1/24),(-1/6),(-1/12);
    (0),(0),(1/4),(-3/8),(-1/8);
    (-1/6),(-1/6),(-1/12),(-1/24),(1/24);
    (-1/8),(-3/8),(-1/8),(0),(1/4);
    (-3/8),(-1/8),(-1/8),(-1/8),(-1/8);
    (-1/6),(-1/6),(-1/3),(-1/6),(-1/3)]

private def Rq : Matrix (Fin 12) (Fin 5) ℚ :=
  !![(-1/6),(-1/6),(-1/12),(-1/24),(1/24);
    (5/24),(-1/24),(1/24),(-1/6),(-1/12);
    (-1/24),(5/24),(1/24),(5/24),(1/24);
    (-1/12),(5/12),(-1/6),(-5/24),(5/24);
    (1/24),(-5/24),(5/24),(5/12),(-1/6);
    (5/12),(-1/12),(-1/6),(1/24),(-1/24);
    (-5/24),(1/24),(5/24),(-5/24),(-1/24);
    (-1/6),(-1/6),(5/12),(5/24),(-5/24);
    (-5/24),(1/24),(-1/24),(-1/12),(-1/6);
    (1/24),(-5/24),(-1/24),(1/24),(5/24);
    (-1/24),(5/24),(-5/24),(-1/6),(5/12);
    (5/24),(-1/24),(-5/24),(-1/24),(-5/24)]

private def Wq : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(5/12),(-1/12),(-1/6),(1/24),(-1/24);
    (-1/12),(5/12),(-1/6),(-5/24),(5/24);
    (-1/6),(-1/6),(5/12),(5/24),(-5/24);
    (1/24),(-5/24),(5/24),(5/12),(-1/6);
    (-1/24),(5/24),(-5/24),(-1/6),(5/12)]

private def Cq : Matrix (Fin 6) (Fin 5) ℚ :=
  !![(-1),(0),(0),(0),(0);
    (0),(1),(-1),(-1),(1);
    (0),(-1),(0),(0),(0);
    (1),(0),(-1),(0),(0);
    (0),(0),(0),(-1),(0);
    (0),(0),(0),(0),(-1)]

private def Hq : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(2),(0),(-1),(0),(0);
    (0),(2),(-1),(-1),(1);
    (-1),(-1),(2),(1),(-1);
    (0),(-1),(1),(2),(-1);
    (0),(1),(-1),(-1),(2)]

private def Mq : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(5),(1),(-1),(-1),(1);
    (1),(5),(-1),(0),(0);
    (0),(0),(4),(-1),(1);
    (0),(0),(0),(5),(-1);
    (0),(0),(0),(-1),(5)]

private def Sq : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(-1),(1),(0),(1),(1);
    (1),(0),(0),(1),(0);
    (0),(1),(0),(0),(1);
    (0),(0),(1),(0),(-1);
    (0),(0),(1),(0),(1)]

private def Siq : Matrix (Fin 5) (Fin 5) ℚ :=
  !![(-1/2),(1/2),(1/2),(0),(0);
    (0),(0),(1),(1/2),(-1/2);
    (0),(0),(0),(1/2),(1/2);
    (1/2),(1/2),(-1/2),(0),(0);
    (0),(0),(0),(-1/2),(1/2)]

def vertexEnum : Fin 7 → SpatialVertex := ![![0,0,1],![0,1,0],![0,1,1],![1,0,0],![1,0,1],![1,1,0],![1,1,1]]

def edgeEnum : Fin 12 → SpatialEdge := ![
  ⟨(![0,0,0],0),by decide +kernel⟩,
  ⟨(![0,0,0],1),by decide +kernel⟩,
  ⟨(![0,0,0],2),by decide +kernel⟩,
  ⟨(![0,0,1],0),by decide +kernel⟩,
  ⟨(![0,0,1],1),by decide +kernel⟩,
  ⟨(![0,1,0],0),by decide +kernel⟩,
  ⟨(![0,1,0],2),by decide +kernel⟩,
  ⟨(![0,1,1],0),by decide +kernel⟩,
  ⟨(![1,0,0],1),by decide +kernel⟩,
  ⟨(![1,0,0],2),by decide +kernel⟩,
  ⟨(![1,0,1],1),by decide +kernel⟩,
  ⟨(![1,1,0],2),by decide +kernel⟩]

private def targetEnum : Fin 12 → SpatialVertex := ![![1,0,0],![0,1,0],![0,0,1],![1,0,1],![0,1,1],![1,1,0],![0,1,1],![1,1,1],![1,1,0],![1,0,1],![1,1,1],![1,1,1]]

private theorem target_identity (i : Fin 12) :
    shift (edgeEnum i).val.1 (edgeEnum i).val.2=targetEnum i := by
  fin_cases i <;> ext a <;> fin_cases a <;>
    norm_num [edgeEnum,targetEnum,shift,Function.update]

theorem edge_bijective : Function.Bijective edgeEnum := by decide +kernel

private theorem gradient_geometry : ∀ (i : Fin 12) (j : Fin 7), Dq i j=
    (if shift (edgeEnum i).val.1 (edgeEnum i).val.2=vertexEnum j then 1 else 0)-
      (if (edgeEnum i).val.1=vertexEnum j then 1 else 0) := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Dq,edgeEnum,vertexEnum,shift,Function.update,funext_iff,Fin.forall_fin_succ]
private theorem chord_geometry : ∀ (i : Fin 12) (j : Fin 5), Bq i j=
    if chordLabel (edgeEnum i)=some j then 1 else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Bq,edgeEnum,chordLabel]
private theorem curl_geometry : ∀ (i : Fin 6) (j : Fin 5), Cq i j=
    (if chordLabel (faceEdge (faceEnum i) 0)=some j then 1 else 0)+
    (if chordLabel (faceEdge (faceEnum i) 1)=some j then 1 else 0)-
    (if chordLabel (faceEdge (faceEnum i) 2)=some j then 1 else 0)-
    (if chordLabel (faceEdge (faceEnum i) 3)=some j then 1 else 0) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Cq,faceEnum,faceEdge,rawFaceEdge,chordLabel,shift,Function.update]

private theorem inverse_certificate : (Dq.transpose*Dq)*Liq=1 := by decide +kernel
private theorem response_certificate : Bq+Dq*Aq=Rq := by decide +kernel
private theorem orthogonal_certificate : Dq.transpose*Rq=0 := by decide +kernel
private theorem metric_certificate : Rq.transpose*Rq=Wq := by decide +kernel
private theorem spatial_certificate : Cq.transpose*Cq=Hq := by decide +kernel
private theorem generalized_certificate : Wq*Mq=Hq := by decide +kernel
private theorem eigenbasis_certificate : Mq*Sq=Sq*Matrix.diagonal ![4,4,4,6,6] := by decide +kernel
private theorem basis_inverse_certificate : Sq*Siq=1 := by decide +kernel

def grad : Matrix (Fin 12) (Fin 7) ℝ := Dq.map (Rat.castHom ℝ)
def chord : Matrix (Fin 12) (Fin 5) ℝ := Bq.map (Rat.castHom ℝ)
def responseMatrix : Matrix (Fin 7) (Fin 5) ℝ := Aq.map (Rat.castHom ℝ)
def residualMatrix : Matrix (Fin 12) (Fin 5) ℝ := Rq.map (Rat.castHom ℝ)
def kinetic : Matrix (Fin 5) (Fin 5) ℝ := Wq.map (Rat.castHom ℝ)
def spatial : Matrix (Fin 5) (Fin 5) ℝ := Hq.map (Rat.castHom ℝ)
def generalized : Matrix (Fin 5) (Fin 5) ℝ := Mq.map (Rat.castHom ℝ)
def modeBasis : Matrix (Fin 5) (Fin 5) ℝ := Sq.map (Rat.castHom ℝ)
def modeInverse : Matrix (Fin 5) (Fin 5) ℝ := Siq.map (Rat.castHom ℝ)

theorem response_exact : chord+grad*responseMatrix=residualMatrix := by
  ext i j
  have h := congrFun (congrFun response_certificate i) j
  simp only [chord,grad,responseMatrix,residualMatrix,Matrix.mul_apply,Matrix.add_apply,Matrix.map_apply] at h ⊢
  simpa only [map_add,map_sum,map_mul,map_zero] using congrArg (Rat.castHom ℝ) h

theorem orthogonal_exact : grad.transpose*residualMatrix=0 := by
  ext i j
  have h := congrFun (congrFun orthogonal_certificate i) j
  simp only [grad,residualMatrix,Matrix.mul_apply,Matrix.transpose_apply,Matrix.zero_apply,Matrix.map_apply] at h ⊢
  simpa only [map_add,map_sum,map_mul,map_zero] using congrArg (Rat.castHom ℝ) h

theorem metric_exact : residualMatrix.transpose*residualMatrix=kinetic := by
  ext i j
  have h := congrFun (congrFun metric_certificate i) j
  simp only [residualMatrix,kinetic,Matrix.mul_apply,Matrix.transpose_apply,Matrix.map_apply] at h ⊢
  simpa only [map_add,map_sum,map_mul,map_zero] using congrArg (Rat.castHom ℝ) h

theorem generalized_exact : kinetic*generalized=spatial := by
  ext i j
  have h := congrFun (congrFun generalized_certificate i) j
  simp only [kinetic,generalized,spatial,Matrix.mul_apply,Matrix.map_apply] at h ⊢
  simpa only [map_add,map_sum,map_mul,map_zero] using congrArg (Rat.castHom ℝ) h

def temporalEnergy (x : Fin 5 → ℝ) (z : Fin 7 → ℝ) : ℝ :=
  dotProduct (chord.mulVec x+grad.mulVec z) (chord.mulVec x+grad.mulVec z)

/-- Exact elimination of all seven anchored temporal gauge directions. -/
theorem completed_square (x : Fin 5 → ℝ) (z : Fin 7 → ℝ) :
    temporalEnergy x z=dotProduct x (kinetic.mulVec x)+
      dotProduct (grad.mulVec (z-responseMatrix.mulVec x))
        (grad.mulVec (z-responseMatrix.mulVec x)) := by
  have he : chord.mulVec x+grad.mulVec z=residualMatrix.mulVec x+
      grad.mulVec (z-responseMatrix.mulVec x) := by
    rw [Matrix.mulVec_sub,← response_exact,Matrix.add_mulVec,Matrix.mulVec_mulVec]
    abel
  have ho (u : Fin 7 → ℝ) : dotProduct (grad.mulVec u) (residualMatrix.mulVec x)=0 := by
    rw [dotProduct_comm (grad.mulVec u) (residualMatrix.mulVec x),
      ← Matrix.dotProduct_transpose_mulVec grad u (residualMatrix.mulVec x),
      Matrix.mulVec_mulVec,orthogonal_exact]
    simp
  have hm : dotProduct (residualMatrix.mulVec x) (residualMatrix.mulVec x)=
      dotProduct x (kinetic.mulVec x) := by
    rw [← Matrix.dotProduct_transpose_mulVec residualMatrix x (residualMatrix.mulVec x),
      Matrix.mulVec_mulVec,metric_exact]
  unfold temporalEnergy
  rw [he,dotProduct_add,add_dotProduct,add_dotProduct,ho,hm]
  have ho' := ho (z-responseMatrix.mulVec x)
  rw [dotProduct_comm] at ho'
  rw [ho']
  ring

/-- The exact temporal quadratic minimum is attained, without discarding a gauge mode. -/
theorem minimum_attained (x : Fin 5 → ℝ) :
    temporalEnergy x (responseMatrix.mulVec x)=dotProduct x (kinetic.mulVec x) := by
  rw [completed_square]
  simp

theorem energy_lower_bound (x : Fin 5 → ℝ) (z : Fin 7 → ℝ) :
    dotProduct x (kinetic.mulVec x) ≤ temporalEnergy x z := by
  rw [completed_square]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => by
    exact mul_self_nonneg _))

/-- Chord velocities use the SAME axial section as the actual Haar reduction. -/
def axialVelocity (x : Fin 5 → Fin 3 → ℝ) : EdgeVelocity :=
  fun e => (chordLabel e).elim 0 x

def anchor (Z : GaugeVelocity) (a : Fin 3) : Fin 7 → ℝ :=
  fun k => Z (vertexEnum k) a-Z (![0,0,0] : SpatialVertex) a

/-- Exact actual-edge identification of the anchored temporal quadratic coordinates. -/
theorem temporal_component (x : Fin 5 → Fin 3 → ℝ) (Z : GaugeVelocity)
    (i : Fin 12) (a : Fin 3) :
    (axialVelocity x (edgeEnum i)+gradient Z (edgeEnum i)) a=
      chord.mulVec (fun j => x j a) i+grad.mulVec (anchor Z a) i := by
  unfold gradient
  rw [target_identity]
  fin_cases i <;>
    norm_num [axialVelocity,anchor,edgeEnum,targetEnum,vertexEnum,chord,grad,Dq,Bq,
      Matrix.mulVec,dotProduct,Fin.sum_univ_succ,chordLabel,Pi.add_apply,Pi.sub_apply,
      Matrix.head_cons,Matrix.tail_cons] <;> ring

/-- The actual temporal Hessian is the sum of the three anchored scalar energies. -/
theorem temporal_energy_actual (x : Fin 5 → Fin 3 → ℝ) (Z : GaugeVelocity) :
    temporalQuadratic (axialVelocity x) 0 Z=
      ∑ a : Fin 3,temporalEnergy (fun j => x j a) (anchor Z a) := by
  have h := Fintype.sum_equiv (Equiv.ofBijective edgeEnum edge_bijective)
    (fun i => SU2MatrixExponentialBridge.lengthSq (axialVelocity x (edgeEnum i)+gradient Z (edgeEnum i)))
    (fun e => SU2MatrixExponentialBridge.lengthSq (axialVelocity x e+gradient Z e)) (fun _ => rfl)
  unfold temporalQuadratic
  simp only [Pi.zero_apply,sub_zero]
  rw [← h]
  unfold SU2MatrixExponentialBridge.lengthSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [temporal_component]
  simp only [temporalEnergy,dotProduct,Pi.add_apply,pow_two]

/-- Eliminating temporal gauge velocities gives a verified lower bound for the ACTUAL Hessian. -/
theorem temporal_actual_lower (x : Fin 5 → Fin 3 → ℝ) (Z : GaugeVelocity) :
    (∑ a : Fin 3,dotProduct (fun j => x j a) (kinetic.mulVec (fun j => x j a))) ≤
      temporalQuadratic (axialVelocity x) 0 Z := by
  rw [temporal_energy_actual]
  exact Finset.sum_le_sum (fun a _ => energy_lower_bound _ _)

/-- A root-anchored representative of any seven relative vertex velocities. -/
def fillGauge (z : Fin 7 → Fin 3 → ℝ) (v : SpatialVertex) : Fin 3 → ℝ :=
  if v 0=0 then
    if v 1=0 then (if v 2=0 then 0 else z 0)
    else (if v 2=0 then z 1 else z 2)
  else if v 1=0 then (if v 2=0 then z 3 else z 4)
  else (if v 2=0 then z 5 else z 6)

theorem anchor_fill (z : Fin 7 → Fin 3 → ℝ) (a : Fin 3) :
    anchor (fillGauge z) a=(fun k => z k a) := by
  funext k
  fin_cases k <;> simp [anchor,fillGauge,vertexEnum]

/-- The lower bound is attained by ACTUAL vertex velocities, retaining constant shifts. -/
theorem temporal_actual_minimum (x : Fin 5 → Fin 3 → ℝ) :
    ∃ Z : GaugeVelocity, temporalQuadratic (axialVelocity x) 0 Z=
      ∑ a : Fin 3,dotProduct (fun j => x j a) (kinetic.mulVec (fun j => x j a)) := by
  refine ⟨fillGauge (fun k a => responseMatrix.mulVec (fun j => x j a) k),?_⟩
  rw [temporal_energy_actual]
  apply Finset.sum_congr rfl
  intro a _
  rw [anchor_fill]
  exact minimum_attained _

def curlMatrix : Matrix (Fin 6) (Fin 5) ℝ := Cq.map (Rat.castHom ℝ)

/-- Exact actual-face curl coefficients on the same axial chord section. -/
theorem curl_component (x : Fin 5 → Fin 3 → ℝ) (i : Fin 6) (a : Fin 3) :
    curl (axialVelocity x) (faceEnum i) a=curlMatrix.mulVec (fun j => x j a) i := by
  fin_cases i <;>
    norm_num [curl,axialVelocity,curlMatrix,Cq,faceEnum,faceEdge,rawFaceEdge,chordLabel,
      shift,Function.update,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Pi.add_apply,Pi.sub_apply,
      Matrix.head_cons,Matrix.tail_cons] <;> ring

theorem spatial_exact : curlMatrix.transpose*curlMatrix=spatial := by
  ext i j
  have h := congrFun (congrFun spatial_certificate i) j
  simp only [curlMatrix,spatial,Matrix.mul_apply,Matrix.transpose_apply,Matrix.map_apply] at h ⊢
  simpa only [map_add,map_sum,map_mul,map_zero] using congrArg (Rat.castHom ℝ) h

/-- The actual spatial Hessian is the same certified curl Gram form. -/
theorem spatial_energy_actual (x : Fin 5 → Fin 3 → ℝ) :
    spatialQuadratic (axialVelocity x)=
      ∑ a : Fin 3,dotProduct (fun j => x j a) (spatial.mulVec (fun j => x j a)) := by
  have h := Fintype.sum_equiv (Equiv.ofBijective faceEnum face_enum_bijective)
    (fun i => SU2MatrixExponentialBridge.lengthSq (curl (axialVelocity x) (faceEnum i)))
    (fun p => SU2MatrixExponentialBridge.lengthSq (curl (axialVelocity x) p)) (fun _ => rfl)
  unfold spatialQuadratic
  rw [← h]
  unfold SU2MatrixExponentialBridge.lengthSq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [curl_component]
  simp only [pow_two]
  change dotProduct (curlMatrix.mulVec (fun j => x j a)) (curlMatrix.mulVec (fun j => x j a))=_
  rw [← Matrix.dotProduct_transpose_mulVec curlMatrix (fun j => x j a)
    (curlMatrix.mulVec (fun j => x j a)),Matrix.mulVec_mulVec,spatial_exact]

/-- Exact reference frequencies relative to the temporal Schur metric. -/
theorem mode_diagonal : generalized*modeBasis=modeBasis*Matrix.diagonal ![4,4,4,6,6] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [generalized,modeBasis,Mq,Sq,Matrix.mul_apply,Matrix.diagonal_apply,
      Matrix.map_apply,Fin.sum_univ_succ,Matrix.head_cons,Matrix.tail_cons]

theorem mode_basis_inverse : modeBasis*modeInverse=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modeBasis,modeInverse,Sq,Siq,Matrix.mul_apply,Matrix.one_apply,
      Matrix.map_apply,Fin.sum_univ_succ,Matrix.head_cons,Matrix.tail_cons]

theorem temporal_difference_actual (x y : Fin 5 → Fin 3 → ℝ) (Z : GaugeVelocity) :
    temporalQuadratic (axialVelocity x) (axialVelocity y) Z=
      temporalQuadratic (axialVelocity (fun j => x j-y j)) 0 Z := by
  unfold temporalQuadratic
  simp only [Pi.zero_apply,sub_zero]
  apply Finset.sum_congr rfl
  intro e _
  have h : axialVelocity x e-axialVelocity y e=axialVelocity (fun j => x j-y j) e := by
    unfold axialVelocity
    cases he : chordLabel e <;> simp [he]
  rw [h]

/-- A precise lower bound for the ACTUAL two-boundary slab Hessian. -/
theorem second_variation_axial_lower (x y : Fin 5 → Fin 3 → ℝ) (Z : GaugeVelocity) :
    (∑ a : Fin 3,dotProduct (fun j => x j a) (spatial.mulVec (fun j => x j a)))/8+
      (∑ a : Fin 3,dotProduct (fun j => y j a) (spatial.mulVec (fun j => y j a)))/8+
      (∑ a : Fin 3,dotProduct (fun j => x j a-y j a)
        (kinetic.mulVec (fun j => x j a-y j a)))/4 ≤
      deriv (deriv (ray (axialVelocity x) (axialVelocity y) Z)) 0 := by
  rw [second_variation,spatial_energy_actual,spatial_energy_actual,temporal_difference_actual]
  have h := temporal_actual_lower (fun j => x j-y j) Z
  simp only [Pi.sub_apply] at h
  linarith

/-- The lower bound is attained among actual temporal vertex velocities, not merely
in an unrelated scalar surrogate. This identifies the exact effective Hessian. -/
theorem second_variation_axial_minimum (x y : Fin 5 → Fin 3 → ℝ) :
    ∃ Z : GaugeVelocity, deriv (deriv (ray (axialVelocity x) (axialVelocity y) Z)) 0=
      (∑ a : Fin 3,dotProduct (fun j => x j a) (spatial.mulVec (fun j => x j a)))/8+
      (∑ a : Fin 3,dotProduct (fun j => y j a) (spatial.mulVec (fun j => y j a)))/8+
      (∑ a : Fin 3,dotProduct (fun j => x j a-y j a)
        (kinetic.mulVec (fun j => x j a-y j a)))/4 := by
  obtain ⟨Z,hZ⟩ := temporal_actual_minimum (fun j => x j-y j)
  refine ⟨Z,?_⟩
  rw [second_variation,spatial_energy_actual,spatial_energy_actual,temporal_difference_actual,hZ]
  rfl

end OperatorDerivativeRewrite.Foundation.CubeTemporalSchur
