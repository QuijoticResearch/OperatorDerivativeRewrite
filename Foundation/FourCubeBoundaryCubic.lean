import Foundation.FourCubeWilsonCubic

/-! Actual boundary variables on the existing112-edge/72-face cap complex.
The two tested boundary links are distinct from retained interior links. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeBoundaryCubic
open QuaternionSU2Representation SU2JointPlaquetteCubic
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex FourCubeChordIncidence
open FourCubeWilsonCubic

-- Avoid eager expansion of the concrete finite set during subtype elaboration.
attribute [local irreducible] upperFaces

def chosenRibbon : Upper := ⟨(edgeA,3),by norm_num [upperFaces,edges,edgeA,base]⟩
def chosenCap : Cap := capHigh chosenRibbon

def links (x y z : ℝ) : FullEdge → SU2
  | .inl e => if e.val=edgeA then axis 2 z else 1
  | .inr (.inl c) => if c.val=chosenCap.val then axis 0 x else 1
  | .inr (.inr p) => if p.val=chosenRibbon.val then (axis 1 y)⁻¹ else 1

theorem boundary_cap_value (x y z : ℝ) : links x y z (.inr (.inl chosenCap))=axis 0 x := by simp [links]
theorem boundary_upper_value (x y z : ℝ) : links x y z (.inr (.inr chosenRibbon))=(axis 1 y)⁻¹ := by simp [links]
theorem interior_value (x y z : ℝ) : links x y z (.inl (ribbonInterior chosenRibbon))=axis 2 z := by simp [links,ribbonInterior,chosenRibbon]

theorem tree_fixed (x y z : ℝ) (e : Interior) (he : e.val∈axialTree) : links x y z (.inl e)=1 := by
  have hn : e.val≠edgeA := by intro h; rw [h] at he; exact selected_not_tree.1 he
  simp [links,hn]

/-- Identity outside the retained index set is only an extension convention. -/
def retained (U : FullEdge → SU2) (e : EdgeData) : SU2 :=
  if he : e∈edges then U (.inl ⟨e,he⟩) else 1

theorem retained_links (x y z : ℝ) (e : EdgeData) :
    retained (links x y z) e=if e=edgeA then axis 2 z else 1 := by
  have ha : edgeA∈edges := by decide
  by_cases he : e∈edges
  · simp [retained,he,links]
  · have hn : e≠edgeA := by intro h; rw [h] at he; exact he ha
    simp [retained,he,hn]

def ribbonWord (U : FullEdge → SU2) (p : Upper) : SU2 :=
  U (.inl (ribbonInterior p))*U (.inr (.inl (capHigh p)))*
    (U (.inr (.inr p)))⁻¹*(U (.inr (.inl (capLow p))))⁻¹

def fullAction (U : FullEdge → SU2) : ℝ :=
  innerAction (retained U)+∑ p : Upper, (1-halfTrace (ribbonWord U p))

private theorem cyclic_action (x y z : ℝ) :
    1-halfTrace (axis 2 z*axis 0 x*axis 1 y)=action x y z := by
  rw [mul_assoc,SU2WilsonConvolution.halfTrace_mul_comm (axis 2 z) (axis 0 x*axis 1 y)]
  exact triple_action x y z

private theorem retained_face (x y z : ℝ) (p : FaceData) (hp : p∈innerFaces) :
    faceAction (retained (links x y z)) p=if edgeA∈boundary p then 1-Real.cos z else 0 := by
  rw [innerFaces_eq] at hp
  simp only [faceList,List.toFinset_cons,List.toFinset_nil,Finset.mem_insert,
    Finset.notMem_empty,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [faceAction,faceEdge,retained_links,edgeA,base,shifted,boundary,
    axis_trace,SU2WilsonConvolution.halfTrace_inv,trace_one,funext_iff,
    Fin.forall_fin_succ,Fin.exists_fin_succ,Function.update_apply]

theorem retained_action (x y z : ℝ) :
    innerAction (retained (links x y z))=3*(1-Real.cos z) := by
  unfold innerAction
  rw [Finset.sum_congr rfl (fun p hp => retained_face x y z p hp),← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [edge_degree edgeA (by decide)]
  norm_num

def ribbonClass (p : EdgeData × Fin 4) : Fin 3 :=
  if p=chosenRibbon.val then 0 else
  if (p.1.1,p.2)=chosenCap.val ∨ (shifted p.1.1 p.1.2,p.2)=chosenCap.val then 1 else 2

def ribbonValues (x y z : ℝ) : Fin 3 → ℝ := ![action x y z,1-Real.cos x,0]

private theorem ribbon_interior_selected (p : Upper) :
    p.val.1 = edgeA ↔ p.val = chosenRibbon.val := by
  have hp : p.val ∈ upperFaces := p.property
  simp only [upperFaces,Finset.mem_filter,Finset.mem_univ,true_and] at hp
  constructor
  · intro he
    have hv : p.val.1.1 p.val.2 = 1 := hp.2.2
    have he' : p.val.1.1 = edgeA.1 := congrArg Prod.fst he
    have hj : p.val.2 = 3 := by
      rw [he'] at hv
      generalize hj : p.val.2 = j at hv ⊢
      fin_cases j <;> simp_all [edgeA,base]
    exact Prod.ext he hj
  · exact fun he => congrArg Prod.fst he

private theorem ribbon_caps_distinct (p : Upper) : capHigh p ≠ capLow p := by
  have hp : p.val ∈ upperFaces := p.property
  simp only [upperFaces,edges,Finset.mem_filter,Finset.mem_univ,true_and] at hp
  intro he
  have hh := congrArg (fun c : Cap => c.val.1 p.val.1.2) he
  change shifted p.val.1.1 p.val.1.2 p.val.1.2 = p.val.1.1 p.val.1.2 at hh
  simp [shifted,hp.1] at hh

private theorem ribbon_class_action (x y z : ℝ) (p : Upper) :
    1-halfTrace (ribbonWord (links x y z) p)=ribbonValues x y z (ribbonClass p.val) := by
  by_cases he : p=chosenRibbon
  · subst p
    norm_num [ribbonWord,links,ribbonInterior,capHigh,capLow,chosenCap,
      chosenRibbon,edgeA,base,shifted,ribbonClass,ribbonValues,axis_trace,
      trace_one,cyclic_action,funext_iff,Fin.forall_fin_succ,Function.update_apply]
  · have hv : p.val ≠ chosenRibbon.val := fun h => he (Subtype.ext h)
    have hi : p.val.1 ≠ edgeA := fun h => hv ((ribbon_interior_selected p).mp h)
    have hd := ribbon_caps_distinct p
    by_cases hh : (capHigh p).val=chosenCap.val
    · have hl : (capLow p).val ≠ chosenCap.val := by
        intro hl
        exact hd (Subtype.ext (hh.trans hl.symm))
      change (shifted p.val.1.1 p.val.1.2,p.val.2)=chosenCap.val at hh
      change (p.val.1.1,p.val.2)≠chosenCap.val at hl
      simp [ribbonWord,links,ribbonInterior,capHigh,capLow,ribbonClass,ribbonValues,
        hi,hv,hh,hl,axis_trace]
    · by_cases hl : (capLow p).val=chosenCap.val
      · change (shifted p.val.1.1 p.val.1.2,p.val.2)≠chosenCap.val at hh
        change (p.val.1.1,p.val.2)=chosenCap.val at hl
        simp [ribbonWord,links,ribbonInterior,capHigh,capLow,ribbonClass,ribbonValues,
          hi,hv,hh,hl,axis_trace,SU2WilsonConvolution.halfTrace_inv]
      · change (shifted p.val.1.1 p.val.1.2,p.val.2)≠chosenCap.val at hh
        change (p.val.1.1,p.val.2)≠chosenCap.val at hl
        simp [ribbonWord,links,ribbonInterior,capHigh,capLow,ribbonClass,ribbonValues,
          hi,hv,hh,hl,trace_one]

private theorem ribbon_zero_fiber :
    upperFaces.filter (fun p => ribbonClass p=0)={chosenRibbon.val} := by
  ext p
  simp only [Finset.mem_filter,Finset.mem_singleton]
  by_cases he : p=chosenRibbon.val
  · subst p
    simp [ribbonClass,chosenRibbon.property]
  · simp only [ribbonClass,if_neg he]
    split_ifs <;> simp [he]

private theorem ribbon_one_fiber :
    upperFaces.filter (fun p => ribbonClass p=1)=
      {(edgeB,3),((shifted base 0,2),3)} := by
  ext ⟨⟨v,d⟩,j⟩
  simp only [Finset.mem_filter,upperFaces,Finset.mem_filter,Finset.mem_univ,true_and,
    edges,Finset.mem_insert,Finset.mem_singleton]
  revert d j
  fin_cases v <;> decide

theorem ribbonClass_count : ∀ i : Fin 3,
    (upperFaces.filter (fun p => ribbonClass p=i)).card=(![1,2,45] : Fin 3 → ℕ) i := by
  have h0 : (upperFaces.filter (fun p => ribbonClass p=0)).card=1 := by
    rw [ribbon_zero_fiber]; simp
  have h1 : (upperFaces.filter (fun p => ribbonClass p=1)).card=2 := by
    rw [ribbon_one_fiber]
    norm_num [edgeB,base,shifted,funext_iff,Fin.forall_fin_succ]
  have ht := Finset.sum_fiberwise upperFaces ribbonClass (fun _ => (1:ℕ))
  simp only [Finset.sum_const,Nat.nsmul_eq_mul,mul_one,upperFaces_card] at ht
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · change (upperFaces.filter (fun p => ribbonClass p=2)).card=45
    rw [Fin.sum_univ_three,h0,h1] at ht
    omega

/-- Actual72-face Wilson action with two boundary-link variables and one
retained interior-link background; every axial-tree link is identically1. -/
theorem fullAction_formula (x y z : ℝ) : fullAction (links x y z)=
    action x y z+2*(1-Real.cos x)+3*(1-Real.cos z) := by
  unfold fullAction
  rw [retained_action]
  simp_rw [ribbon_class_action]
  rw [Finset.sum_coe_sort upperFaces (fun p => ribbonValues x y z (ribbonClass p))]
  rw [← Finset.sum_fiberwise' upperFaces ribbonClass (ribbonValues x y z)]
  simp only [Finset.sum_const,ribbonClass_count,nsmul_eq_mul]
  norm_num [Fin.sum_univ_succ,ribbonValues]
  ring

theorem boundary_mixed_hessian (z : ℝ) :
    deriv (fun y : ℝ => deriv (fun x : ℝ => fullAction (links x y z)) 0) 0=Real.sin z := by
  have hx (y : ℝ) : deriv (fun x : ℝ => fullAction (links x y z)) 0=
      deriv (fun x : ℝ => action x y z) 0 := by
    have hg : HasDerivAt (fun x : ℝ => 2*(1-Real.cos x)+3*(1-Real.cos z)) 0 0 := by
      convert (((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (Real.hasDerivAt_cos 0)).const_mul 2).add_const
        (3*(1-Real.cos z)) using 1 <;> simp
    have he : (fun x : ℝ => fullAction (links x y z))=(fun x =>
        action x y z+(2*(1-Real.cos x)+3*(1-Real.cos z))) := by
      funext x
      rw [fullAction_formula]; ring
    rw [he]
    change deriv ((fun x : ℝ => action x y z)+
      (fun x => 2*(1-Real.cos x)+3*(1-Real.cos z))) 0=_
    rw [deriv_add (action_x_hasDerivAt 0 y z).differentiableAt hg.differentiableAt,hg.deriv,add_zero]
  simp_rw [hx]
  exact mixed_hessian z

theorem mixed_third_at_identity :
    deriv (fun z : ℝ => deriv (fun y : ℝ =>
      deriv (fun x : ℝ => fullAction (links x y z)) 0) 0) 0=1 := by
  simp_rw [boundary_mixed_hessian]
  simpa using (Real.hasDerivAt_sin 0).deriv

theorem boundary_thermal_counterexample (C C0 R : ℝ) (hC : 0 ≤ C) (hC0 : 0 ≤ C0) :
    ∃ s : ℝ, R < s ∧ 1 < s ∧ C+C0 < s^2*
      |deriv (fun y : ℝ => deriv (fun x : ℝ => fullAction (links x y (1/s))) 0) 0| := by
  simpa only [boundary_mixed_hessian,mixed_remainder_hessian] using
    thermal_window_counterexample C C0 R hC hC0

theorem boundary_first_at_zero (y z : ℝ) :
    deriv (fun x : ℝ => fullAction (links x y z)) 0=Real.sin y*Real.sin z := by
  simp_rw [fullAction_formula]
  have hg := ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (Real.hasDerivAt_cos 0)).const_mul 2
  have hd := ((action_x_hasDerivAt 0 y z).add hg).add_const (3*(1-Real.cos z))
  simpa using hd.deriv

/-- The first variable is a cap boundary link; the differentiated third variable
is a retained interior link. The middle boundary link is the background. -/
theorem boundary_interior_mixed_hessian (y : ℝ) :
    deriv (fun z : ℝ => deriv (fun x : ℝ => fullAction (links x y z)) 0) 0=Real.sin y := by
  simp_rw [boundary_first_at_zero]
  simpa using ((Real.hasDerivAt_sin 0).const_mul (Real.sin y)).deriv

theorem full_odd_part (t : ℝ) :
    fullAction (links t t t)-fullAction (links (-t) (-t) (-t))=2*Real.sin t^3 := by
  rw [fullAction_formula,fullAction_formula]
  simp only [Real.cos_neg]
  linarith [odd_part t]

theorem no_uniform_boundary_quadratic_plus_constant :
    ¬ ∃ C C0 ε : ℝ, 0 ≤ C ∧ 0 ≤ C0 ∧ 0 < ε ∧
      ∀ β z : ℝ, 1 ≤ β → 0 < z → z < ε →
        β*|deriv (fun y : ℝ => deriv (fun x : ℝ => fullAction (links x y z)) 0) 0|
          ≤ C*β*z^2+C0 := by
  simpa only [boundary_mixed_hessian,mixed_remainder_hessian] using
    no_uniform_quadratic_plus_constant

end OperatorDerivativeRewrite.Foundation.FourCubeBoundaryCubic
