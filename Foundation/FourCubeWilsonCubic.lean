import Foundation.FourCubeAxialTree
import Foundation.OneSidedCapComplex
import Foundation.SU2JointPlaquetteCubic

/-! A genuine tree-fixed SU2 field on the existing four-cube. All24 internal
plaquettes are included; the cubic is not a single-face truncation. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeWilsonCubic
open OneSidedBlockIncidence FourCubeChordIncidence QuaternionSU2Representation
open SU2JointPlaquetteCubic

def base : Vertex := ![0,0,0,1]
def selectedFace : FaceData := (base,(0,1))
def edgeA : EdgeData := (base,0)
def edgeB : EdgeData := (shifted base 0,1)
def edgeC : EdgeData := (shifted base 1,0)

def field (x y z : ℝ) (e : EdgeData) : SU2 :=
  if e=edgeA then axis 0 x else if e=edgeB then axis 1 y else
  if e=edgeC then (axis 2 z)⁻¹ else 1

theorem selected_not_tree : edgeA∉axialTree ∧ edgeB∉axialTree ∧ edgeC∉axialTree := by decide

theorem field_tree (x y z : ℝ) (e : EdgeData) (he : e∈axialTree) : field x y z e=1 := by
  have ha : e≠edgeA := by intro h; rw [h] at he; exact selected_not_tree.1 he
  have hb : e≠edgeB := by intro h; rw [h] at he; exact selected_not_tree.2.1 he
  have hc : e≠edgeC := by intro h; rw [h] at he; exact selected_not_tree.2.2 he
  simp [field,ha,hb,hc]

def faceAction (U : EdgeData → SU2) (p : FaceData) : ℝ :=
  1-halfTrace (U (faceEdge p 0)*U (faceEdge p 1)*(U (faceEdge p 2))⁻¹*(U (faceEdge p 3))⁻¹)

def innerAction (U : EdgeData → SU2) : ℝ := ∑ p∈innerFaces,faceAction U p

def faceClass (p : FaceData) : Fin 5 :=
  if p=selectedFace then 0 else if edgeA∈boundary p then 1 else
  if edgeB∈boundary p then 2 else if edgeC∈boundary p then 3 else 4

def values (x y z : ℝ) : Fin 5 → ℝ :=
  ![action x y z,1-Real.cos x,1-Real.cos y,1-Real.cos z,0]

theorem axis_trace (a : Fin 3) (t : ℝ) : halfTrace (axis a t)=Real.cos t := by
  change SU2TraceHessianModel.traceReal (repr (axisRaw a t))/2=_
  rw [repr_halfTrace]
  fin_cases a <;> norm_num [axisRaw]

theorem trace_one : halfTrace (1 : SU2)=1 := by
  norm_num [halfTrace,SU2TraceHessianModel.traceReal,Matrix.trace_fin_two]

theorem triple_action (x y z : ℝ) :
    1-halfTrace (axis 0 x*axis 1 y*axis 2 z)=action x y z := by
  simp [action,configuration,SU2SevenLinkTransfer.first,SU2SevenLinkTransfer.leftPath]

theorem faceClass_count : ∀ i : Fin 5,
    (innerFaces.filter (fun p => faceClass p=i)).card=(![1,2,2,2,17] : Fin 5 → ℕ) i := by decide

private theorem face_class_action (x y z : ℝ) (p : FaceData) (hp : p∈innerFaces) :
    faceAction (field x y z) p=values x y z (faceClass p) := by
  rw [innerFaces_eq] at hp
  simp only [faceList,List.toFinset_cons,List.toFinset_nil,Finset.mem_insert,
    Finset.notMem_empty,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [faceAction,faceEdge,field,edgeA,edgeB,edgeC,base,shifted,
    faceClass,selectedFace,boundary,values,axis_trace,SU2WilsonConvolution.halfTrace_inv,
    trace_one,triple_action,funext_iff,Fin.forall_fin_succ,Fin.exists_fin_succ,Function.update_apply]

theorem innerAction_formula (x y z : ℝ) :
    innerAction (field x y z)=action x y z+
      2*((1-Real.cos x)+(1-Real.cos y)+(1-Real.cos z)) := by
  unfold innerAction
  rw [Finset.sum_congr rfl (fun p hp => face_class_action x y z p hp)]
  rw [← Finset.sum_fiberwise' innerFaces faceClass (values x y z)]
  simp only [Finset.sum_const,faceClass_count,nsmul_eq_mul]
  norm_num [Fin.sum_univ_succ,values]
  ring

theorem field_tree_certificate (x y z : ℝ) : FourCubeAxialTree.graph.IsTree ∧
    ∀ e∈axialTree,field x y z e=1 := ⟨FourCubeAxialTree.isTree,field_tree x y z⟩

def upperAction (U : EdgeData → SU2) : ℝ := ∑ p∈upperFaces,(1-halfTrace (U p.1))

def upperClass (p : EdgeData × Fin 4) : Fin 4 :=
  if p.1=edgeA then 0 else if p.1=edgeB then 1 else if p.1=edgeC then 2 else 3

def upperValues (x y z : ℝ) : Fin 4 → ℝ := ![1-Real.cos x,1-Real.cos y,1-Real.cos z,0]

private theorem upper_fiber_card (e : EdgeData) :
    (upperFaces.filter (fun p => p.1=e)).card=
      (Finset.univ.filter (fun j : Fin 4 => e∈edges ∧ j≠e.2 ∧ e.1 j=1)).card := by
  have he : upperFaces.filter (fun p => p.1=e)=
      (Finset.univ.filter (fun j : Fin 4 => e∈edges ∧ j≠e.2 ∧ e.1 j=1)).image (fun j => (e,j)) := by
    ext p
    rcases p with ⟨a,j⟩
    simp only [upperFaces,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image,Prod.mk.injEq]
    aesop
  rw [he,Finset.card_image_of_injective _ (fun i j h => (Prod.mk.inj h).2)]

private theorem first_upper_fiber (i : Fin 3) :
    upperFaces.filter (fun p => upperClass p=i.castSucc)=
      upperFaces.filter (fun p => p.1=(![edgeA,edgeB,edgeC] : Fin 3 → EdgeData) i) := by
  have hBA : edgeB≠edgeA := by decide
  have hCA : edgeC≠edgeA := by decide
  have hCB : edgeC≠edgeB := by decide
  fin_cases i <;> ext p <;> simp only [Finset.mem_filter] <;>
    by_cases ha : p.1=edgeA <;> by_cases hb : p.1=edgeB <;> by_cases hc : p.1=edgeC <;>
    simp_all [upperClass]

private theorem first_upper_count (i : Fin 3) :
    (upperFaces.filter (fun p => upperClass p=i.castSucc)).card=(![1,2,2] : Fin 3 → ℕ) i := by
  rw [first_upper_fiber,upper_fiber_card]
  fin_cases i <;> decide

theorem upperClass_count : ∀ i : Fin 4,
    (upperFaces.filter (fun p => upperClass p=i)).card=(![1,2,2,43] : Fin 4 → ℕ) i := by
  have h0 := first_upper_count 0
  have h1 := first_upper_count 1
  have h2 := first_upper_count 2
  have ht := Finset.sum_fiberwise upperFaces upperClass (fun _ => (1:ℕ))
  simp only [Finset.sum_const,Nat.nsmul_eq_mul,mul_one,upperFaces_card] at ht
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · change (upperFaces.filter (fun p => upperClass p=0)).card=1 at h0
    change (upperFaces.filter (fun p => upperClass p=1)).card=2 at h1
    change (upperFaces.filter (fun p => upperClass p=2)).card=2 at h2
    change (upperFaces.filter (fun p => upperClass p=3)).card=43
    rw [Fin.sum_univ_four,h0,h1,h2] at ht
    omega

private theorem upper_class_action (x y z : ℝ) (p : EdgeData × Fin 4) :
    1-halfTrace (field x y z p.1)=upperValues x y z (upperClass p) := by
  have hBA : edgeB≠edgeA := by decide
  have hCA : edgeC≠edgeA := by decide
  have hCB : edgeC≠edgeB := by decide
  by_cases ha : p.1=edgeA
  · simp [field,ha,upperClass,upperValues,axis_trace,hBA,hCA,hCB]
  · by_cases hb : p.1=edgeB
    · simp [field,ha,hb,upperClass,upperValues,axis_trace,hBA,hCA,hCB]
    · by_cases hc : p.1=edgeC
      · simp [field,ha,hb,hc,upperClass,upperValues,axis_trace,SU2WilsonConvolution.halfTrace_inv,hBA,hCA,hCB]
      · simp [field,ha,hb,hc,upperClass,upperValues,trace_one]

theorem upperAction_formula (x y z : ℝ) : upperAction (field x y z)=
    (1-Real.cos x)+2*(1-Real.cos y)+2*(1-Real.cos z) := by
  unfold upperAction
  simp_rw [upper_class_action]
  rw [← Finset.sum_fiberwise' upperFaces upperClass (upperValues x y z)]
  simp only [Finset.sum_const,upperClass_count,nsmul_eq_mul]
  norm_num [Fin.sum_univ_succ,upperValues]
  ring

/-- The existing one-sided model with all exterior ribbon links fixed to1:
24 internal and48 single-retained-link boundary terms. -/
def boundaryFixedAction (U : EdgeData → SU2) : ℝ := innerAction U+upperAction U

theorem boundaryFixedAction_formula (x y z : ℝ) : boundaryFixedAction (field x y z)=
    action x y z+3*(1-Real.cos x)+4*(1-Real.cos y)+4*(1-Real.cos z) := by
  rw [boundaryFixedAction,innerAction_formula,upperAction_formula]
  ring

theorem inner_odd_part (t : ℝ) : innerAction (field t t t)-innerAction (field (-t) (-t) (-t))=
    2*Real.sin t^3 := by
  rw [innerAction_formula,innerAction_formula]
  simp only [Real.cos_neg]
  linarith [odd_part t]

theorem boundary_fixed_odd_part (t : ℝ) :
    boundaryFixedAction (field t t t)-boundaryFixedAction (field (-t) (-t) (-t))=2*Real.sin t^3 := by
  rw [boundaryFixedAction_formula,boundaryFixedAction_formula]
  simp only [Real.cos_neg]
  linarith [odd_part t]

/-- All other internal plaquettes contribute zero to this mixed entry. -/
theorem inner_mixed_hessian (z : ℝ) :
    deriv (fun y : ℝ => deriv (fun x : ℝ => innerAction (field x y z)) 0) 0=Real.sin z := by
  have hx (y : ℝ) : deriv (fun x : ℝ => innerAction (field x y z)) 0=
      deriv (fun x : ℝ => action x y z) 0 := by
    have hg : HasDerivAt (fun x : ℝ => 2*((1-Real.cos x)+(1-Real.cos y)+(1-Real.cos z))) 0 0 := by
      convert ((((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (Real.hasDerivAt_cos 0)).add_const
        (1-Real.cos y)).add_const (1-Real.cos z)).const_mul 2 using 1 <;> simp
    have he : (fun x : ℝ => innerAction (field x y z))=(fun x =>
        action x y z+2*((1-Real.cos x)+(1-Real.cos y)+(1-Real.cos z))) :=
      funext (fun x => innerAction_formula x y z)
    rw [he]
    change deriv ((fun x : ℝ => action x y z)+
      (fun x => 2*((1-Real.cos x)+(1-Real.cos y)+(1-Real.cos z)))) 0=_
    rw [deriv_add (action_x_hasDerivAt 0 y z).differentiableAt hg.differentiableAt,hg.deriv,add_zero]
  simp_rw [hx]
  exact mixed_hessian z

theorem inner_mixed_third :
    deriv (fun z : ℝ => deriv (fun y : ℝ => deriv (fun x : ℝ => innerAction (field x y z)) 0) 0) 0=1 := by
  simp_rw [inner_mixed_hessian]
  simpa using (Real.hasDerivAt_sin 0).deriv

/-- Arbitrarily large coupling witnesses for the actual FULL internal action. -/
theorem inner_thermal_counterexample (C C0 R : ℝ) (hC : 0 ≤ C) (hC0 : 0 ≤ C0) :
    ∃ s : ℝ, R < s ∧ 1 < s ∧ C+C0 < s^2*
      |deriv (fun y : ℝ => deriv (fun x : ℝ => innerAction (field x y (1/s))) 0) 0| := by
  simpa only [inner_mixed_hessian,mixed_remainder_hessian] using thermal_window_counterexample C C0 R hC hC0

def gaugeField (g : Vertex → SU2) (U : EdgeData → SU2) (e : EdgeData) : SU2 :=
  g e.1*U e*(g (shifted e.1 e.2))⁻¹

theorem faceAction_gauge (g : Vertex → SU2) (U : EdgeData → SU2) (p : FaceData) :
    faceAction (gaugeField g U) p=faceAction U p := by
  dsimp only [faceAction,gaugeField,faceEdge]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  rw [OneSidedCapComplex.shifted_commute p.1 p.2.2 p.2.1]
  have he := SU2WilsonConvolution.loop4_gauge (g p.1) (g (shifted p.1 p.2.1))
    (g (shifted (shifted p.1 p.2.1) p.2.2)) (g (shifted p.1 p.2.2))
    (U (p.1,p.2.1)) (U (shifted p.1 p.2.1,p.2.2))
    (U (shifted p.1 p.2.2,p.2.1))⁻¹ (U (p.1,p.2.2))⁻¹
  simpa only [SU2WilsonConvolution.loop4,mul_inv_rev,inv_inv,mul_assoc] using
    congrArg (fun r : ℝ => 1-r) he

theorem innerAction_gauge (g : Vertex → SU2) (U : EdgeData → SU2) :
    innerAction (gaugeField g U)=innerAction U := by
  unfold innerAction
  simp_rw [faceAction_gauge]

end OperatorDerivativeRewrite.Foundation.FourCubeWilsonCubic
