import Foundation.PeriodicAugmentedBridge
import Foundation.QuaternionTiltCovariance

/-! Exact one-link dependence of the actual periodic augmented Wilson density.
Spatial incidence gives at most four staples, with two distinct temporal staples.
The normalized frozen-link law is identified; global disintegration is separate. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicLinkStaples
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab SU2WilsonConvolution
set_option backward.isDefEq.respectTransparency false

def leftTemporal (U : State) (a : Gauge) (e : SpatialEdge) : SU2 :=
  (a (shift e.1 e.2))⁻¹ * (U e)⁻¹ * a e.1
def rightTemporal (W : State) (b : Gauge) (e : SpatialEdge) : SU2 :=
  b (shift e.1 e.2) * (W e)⁻¹ * (b e.1)⁻¹

private theorem trace_rotate (a b c : SU2) : halfTrace (a*b*c) = halfTrace (b*c*a) := by
  simpa only [mul_assoc] using halfTrace_mul_comm a (b*c)

theorem left_temporal_trace (U V : State) (a : Gauge) (e : SpatialEdge) (A : SU2) :
    halfTrace (temporalWord U (Function.update V e A) a e) = halfTrace (A * leftTemporal U a e) := by
  simp only [temporalWord, Function.update_self]
  rw [← halfTrace_inv (U e * a (shift e.1 e.2) * A⁻¹ * (a e.1)⁻¹)]
  simp only [mul_inv_rev, inv_inv]
  change halfTrace (a e.1 * (A * ((a (shift e.1 e.2))⁻¹ * (U e)⁻¹))) = _
  rw [halfTrace_mul_comm]
  simp only [leftTemporal, mul_assoc]

theorem right_temporal_trace (V W : State) (b : Gauge) (e : SpatialEdge) (A : SU2) :
    halfTrace (temporalWord (Function.update V e A) W b e) = halfTrace (A * rightTemporal W b e) := by
  simp only [temporalWord, Function.update_self, rightTemporal, mul_assoc]

private theorem sum_difference_single {ι : Type*} [Fintype ι] (f g : ι → ℝ) (e : ι)
    (h : ∀ i, i ≠ e → f i = g i) : (∑ i, f i) - (∑ i, g i) = f e - g e := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_single e
  · intro i _ hi; rw [h i hi]; ring
  · simp

theorem temporal_action_change_left (U V : State) (a : Gauge) (e : SpatialEdge) (A : SU2) :
    temporalAction U (Function.update V e A) a - temporalAction U (Function.update V e 1) a =
      halfTrace (leftTemporal U a e) - halfTrace (A * leftTemporal U a e) := by
  classical
  unfold temporalAction
  rw [sum_difference_single _ _ e (fun f hf => by simp [temporalWord, Function.update_of_ne hf])]
  rw [left_temporal_trace, left_temporal_trace, one_mul]
  ring

theorem temporal_action_change_right (V W : State) (b : Gauge) (e : SpatialEdge) (A : SU2) :
    temporalAction (Function.update V e A) W b - temporalAction (Function.update V e 1) W b =
      halfTrace (rightTemporal W b e) - halfTrace (A * rightTemporal W b e) := by
  classical
  unfold temporalAction
  rw [sum_difference_single _ _ e (fun f hf => by simp [temporalWord, Function.update_of_ne hf])]
  rw [right_temporal_trace, right_temporal_trace, one_mul]
  ring

def faceEdge (p : SpatialFace) : Fin 4 → SpatialEdge :=
  ![(p.val.1,p.val.2.1), (shift p.val.1 p.val.2.1,p.val.2.2),
    (shift p.val.1 p.val.2.2,p.val.2.1), (p.val.1,p.val.2.2)]

theorem shift_ne_self (v : SpatialVertex) (i : Fin 3) : shift v i ≠ v := by
  intro h
  have hh := congrFun h i
  simp only [shift, ite_true] at hh
  have hz : (1:ZMod 4) = 0 := add_left_cancel (by simpa only [add_zero] using hh)
  exact (by decide : (1:ZMod 4) ≠ 0) hz

theorem faceEdge_injective (p : SpatialFace) : Function.Injective (faceEdge p) := by
  have hd : p.val.2.1 ≠ p.val.2.2 := ne_of_lt p.property
  have hsi := shift_ne_self p.val.1 p.val.2.1
  have hsj := shift_ne_self p.val.1 p.val.2.2
  have h01 : faceEdge p 0 ≠ faceEdge p 1 := fun h => hd (congrArg Prod.snd h)
  have h02 : faceEdge p 0 ≠ faceEdge p 2 := fun h => hsj (congrArg Prod.fst h).symm
  have h03 : faceEdge p 0 ≠ faceEdge p 3 := fun h => hd (congrArg Prod.snd h)
  have h12 : faceEdge p 1 ≠ faceEdge p 2 := fun h => hd (congrArg Prod.snd h).symm
  have h13 : faceEdge p 1 ≠ faceEdge p 3 := fun h => hsi (congrArg Prod.fst h)
  have h23 : faceEdge p 2 ≠ faceEdge p 3 := fun h => hd (congrArg Prod.snd h)
  intro k l h
  fin_cases k <;> fin_cases l <;> first
    | rfl
    | exact False.elim (h01 h)
    | exact False.elim (h01 h.symm)
    | exact False.elim (h02 h)
    | exact False.elim (h02 h.symm)
    | exact False.elim (h03 h)
    | exact False.elim (h03 h.symm)
    | exact False.elim (h12 h)
    | exact False.elim (h12 h.symm)
    | exact False.elim (h13 h)
    | exact False.elim (h13 h.symm)
    | exact False.elim (h23 h)
    | exact False.elim (h23 h.symm)

def faceRemainder (V : State) (p : SpatialFace) : Fin 4 → SU2 :=
  ![V (faceEdge p 1) * (V (faceEdge p 2))⁻¹ * (V (faceEdge p 3))⁻¹,
    (V (faceEdge p 2))⁻¹ * (V (faceEdge p 3))⁻¹ * V (faceEdge p 0),
    (V (faceEdge p 1))⁻¹ * (V (faceEdge p 0))⁻¹ * V (faceEdge p 3),
    V (faceEdge p 2) * (V (faceEdge p 1))⁻¹ * (V (faceEdge p 0))⁻¹]

private theorem trace_slot_one (a b c d : SU2) : halfTrace (a*b*c⁻¹*d⁻¹) =
    halfTrace (b*(c⁻¹*d⁻¹*a)) := by
  simpa only [mul_assoc] using trace_rotate a b (c⁻¹*d⁻¹)

private theorem trace_slot_two (a b c d : SU2) : halfTrace (a*b*c⁻¹*d⁻¹) =
    halfTrace (c*(b⁻¹*a⁻¹*d)) := by
  rw [← halfTrace_inv (a*b*c⁻¹*d⁻¹)]
  simp only [mul_inv_rev, inv_inv]
  simpa only [mul_assoc] using halfTrace_mul_comm d (c*(b⁻¹*a⁻¹))

private theorem trace_slot_three (a b c d : SU2) : halfTrace (a*b*c⁻¹*d⁻¹) =
    halfTrace (d*(c*b⁻¹*a⁻¹)) := by
  rw [← halfTrace_inv (a*b*c⁻¹*d⁻¹)]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem spatial_trace_at_slot (V : State) (p : SpatialFace) (k : Fin 4) (A : SU2) :
    halfTrace (spatialWord (Function.update V (faceEdge p k) A) p) =
      halfTrace (A * faceRemainder V p k) := by
  classical
  have hn (i j : Fin 4) (hij : i ≠ j) : faceEdge p i ≠ faceEdge p j :=
    fun h => hij (faceEdge_injective p h)
  change halfTrace ((Function.update V (faceEdge p k) A) (faceEdge p 0) *
    (Function.update V (faceEdge p k) A) (faceEdge p 1) *
    ((Function.update V (faceEdge p k) A) (faceEdge p 2))⁻¹ *
    ((Function.update V (faceEdge p k) A) (faceEdge p 3))⁻¹) = _
  have heval (i : Fin 4) : (Function.update V (faceEdge p k) A) (faceEdge p i) =
      if i = k then A else V (faceEdge p i) := by
    by_cases hi : i = k
    · subst i
      rw [Function.update_self, if_pos rfl]
    · rw [Function.update_of_ne (hn i k hi) A V, if_neg hi]
  simp_rw [heval]
  fin_cases k
  · simp [faceRemainder, mul_assoc]
  · simpa [faceRemainder] using trace_slot_one (V (faceEdge p 0)) A
      (V (faceEdge p 2)) (V (faceEdge p 3))
  · simpa [faceRemainder] using trace_slot_two (V (faceEdge p 0))
      (V (faceEdge p 1)) A (V (faceEdge p 3))
  · simpa [faceRemainder] using trace_slot_three (V (faceEdge p 0))
      (V (faceEdge p 1)) (V (faceEdge p 2)) A

def backshift (v : SpatialVertex) (i : Fin 3) : SpatialVertex :=
  fun k => v k - if k=i then 1 else 0

theorem backshift_shift (v : SpatialVertex) (i : Fin 3) : backshift (shift v i) i = v := by
  funext k; simp [backshift, shift]

def sortedFace (v : SpatialVertex) (i j : Fin 3) (hij : i ≠ j) : SpatialFace :=
  if h : i < j then ⟨(v,(i,j)),h⟩ else ⟨(v,(j,i)),lt_of_le_of_ne (le_of_not_gt h) hij.symm⟩

def candidateFace (e : SpatialEdge) (q : {j : Fin 3 // j ≠ e.2} × Bool) : SpatialFace :=
  sortedFace (if q.2 then e.1 else backshift e.1 q.1) e.2 q.1 q.1.property.symm

def candidates (e : SpatialEdge) : Finset SpatialFace :=
  by
    classical
    exact Finset.univ.image (candidateFace e)

theorem other_directions_card (i : Fin 3) : Fintype.card {j : Fin 3 // j ≠ i} = 2 := by
  fin_cases i <;> decide

theorem candidates_card_le (e : SpatialEdge) : (candidates e).card ≤ 4 := by
  calc
    _ ≤ (Finset.univ : Finset ({j : Fin 3 // j ≠ e.2} × Bool)).card := Finset.card_image_le
    _ = 4 := by simp [other_directions_card]

theorem face_in_candidates (p : SpatialFace) (k : Fin 4) : p ∈ candidates (faceEdge p k) := by
  classical
  have hd := ne_of_lt p.property
  unfold candidates
  apply Finset.mem_image.mpr
  fin_cases k
  · refine ⟨(⟨p.val.2.2,hd.symm⟩,true),Finset.mem_univ _,?_⟩
    simp [candidateFace, faceEdge, sortedFace, p.property]
  · refine ⟨(⟨p.val.2.1,hd⟩,false),Finset.mem_univ _,?_⟩
    simp [candidateFace, faceEdge, sortedFace, not_lt.mpr p.property.le, backshift_shift]
  · refine ⟨(⟨p.val.2.2,hd.symm⟩,false),Finset.mem_univ _,?_⟩
    simp [candidateFace, faceEdge, sortedFace, p.property, backshift_shift]
  · refine ⟨(⟨p.val.2.1,hd⟩,true),Finset.mem_univ _,?_⟩
    simp [candidateFace, faceEdge, sortedFace, not_lt.mpr p.property.le]

def incidentFaces (e : SpatialEdge) : Finset SpatialFace :=
  by
    classical
    exact Finset.univ.filter (fun p => ∃ k, faceEdge p k = e)

attribute [local irreducible] incidentFaces

theorem mem_incidentFaces (e : SpatialEdge) (p : SpatialFace) :
    p ∈ incidentFaces e ↔ ∃ k, faceEdge p k = e := by
  unfold incidentFaces
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem incidentFaces_card_le (e : SpatialEdge) : (incidentFaces e).card ≤ 4 := by
  have hs : incidentFaces e ⊆ candidates e := by
    intro p hp
    obtain ⟨k,hk⟩ := (mem_incidentFaces e p).mp hp
    rw [← hk]
    exact face_in_candidates p k
  exact (Finset.card_le_card hs).trans (candidates_card_le e)

def spatialStaple (V : State) (e : SpatialEdge) (p : SpatialFace) : SU2 :=
  by
    classical
    exact if h : ∃ k, faceEdge p k = e then faceRemainder V p (Classical.choose h) else 1

theorem spatial_trace_incident (V : State) (e : SpatialEdge) (p : SpatialFace)
    (hp : p ∈ incidentFaces e) (A : SU2) :
    halfTrace (spatialWord (Function.update V e A) p) = halfTrace (A * spatialStaple V e p) := by
  have h := (mem_incidentFaces e p).mp hp
  unfold spatialStaple
  rw [dif_pos h]
  have he := Classical.choose_spec h
  have ht := spatial_trace_at_slot V p (Classical.choose h) A
  simpa only [he] using ht

theorem spatial_word_nonincident (V : State) (e : SpatialEdge) (p : SpatialFace)
    (hp : p ∉ incidentFaces e) (A : SU2) :
    spatialWord (Function.update V e A) p = spatialWord V p := by
  have hn (k : Fin 4) : faceEdge p k ≠ e := by
    intro h
    exact hp ((mem_incidentFaces e p).mpr ⟨k,h⟩)
  change (Function.update V e A) (faceEdge p 0) * (Function.update V e A) (faceEdge p 1) *
    ((Function.update V e A) (faceEdge p 2))⁻¹ * ((Function.update V e A) (faceEdge p 3))⁻¹ = _
  simp only [Function.update_of_ne (hn 0), Function.update_of_ne (hn 1),
    Function.update_of_ne (hn 2), Function.update_of_ne (hn 3)]
  rfl

theorem spatial_action_change (V : State) (e : SpatialEdge) (A : SU2) :
    spatialAction (Function.update V e A) - spatialAction (Function.update V e 1) =
      ∑ p ∈ incidentFaces e, (halfTrace (spatialStaple V e p) - halfTrace (A * spatialStaple V e p)) := by
  classical
  unfold spatialAction
  rw [← Finset.sum_sub_distrib]
  have he : (∑ p : SpatialFace, ((1-halfTrace (spatialWord (Function.update V e A) p)) -
      (1-halfTrace (spatialWord (Function.update V e 1) p)))) =
      ∑ p ∈ incidentFaces e, ((1-halfTrace (spatialWord (Function.update V e A) p)) -
        (1-halfTrace (spatialWord (Function.update V e 1) p))) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [spatial_word_nonincident V e p hp A, spatial_word_nonincident V e p hp 1]
    ring
  rw [he]
  apply Finset.sum_congr rfl
  intro p hp
  rw [spatial_trace_incident V e p hp A, spatial_trace_incident V e p hp 1, one_mul]
  ring

abbrev StapleIndex := SpatialFace ⊕ Fin 2

def stapleSet (e : SpatialEdge) : Finset StapleIndex :=
  (incidentFaces e).disjSum Finset.univ

theorem stapleSet_card_le (e : SpatialEdge) : (stapleSet e).card ≤ 6 := by
  have h := incidentFaces_card_le e
  simp only [stapleSet, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin]
  omega

def stapleWord (U V W : State) (a b : Gauge) (e : SpatialEdge) : StapleIndex → SU2
  | .inl p => spatialStaple V e p
  | .inr k => if k=0 then leftTemporal U a e else rightTemporal W b e

theorem central_action_change (U V W : State) (a b : Gauge) (e : SpatialEdge) (A : SU2) :
    PeriodicAugmentedBridge.centralAction U W (Function.update V e A,(a,b)) -
      PeriodicAugmentedBridge.centralAction U W (Function.update V e 1,(a,b)) =
      ∑ r ∈ stapleSet e, (halfTrace (stapleWord U V W a b e r) -
        halfTrace (A * stapleWord U V W a b e r)) := by
  have hs := spatial_action_change V e A
  have hl := temporal_action_change_left U V a e A
  have hr := temporal_action_change_right V W b e A
  simp only [stapleSet, Finset.sum_disjSum, stapleWord, Fin.sum_univ_two,
    Fin.isValue, ite_true, show (1:Fin 2) ≠ 0 by decide, ite_false]
  unfold PeriodicAugmentedBridge.centralAction
  dsimp only
  linear_combination hs + hl + hr

open scoped Matrix in
theorem matrix_staple_trace (s : Finset StapleIndex) (B : StapleIndex → SU2) (A : SU2) :
    SU2TraceHessianModel.traceReal ((A : SU2TraceHessianModel.M2) * SU2StaplePolar.staple s B)/2 =
      ∑ r ∈ s, halfTrace (A * B r) := by
  classical
  simp [SU2StaplePolar.staple, Finset.mul_sum, SU2TraceHessianModel.traceReal,
    Matrix.trace_sum, halfTrace, Finset.sum_div]

theorem central_action_matrix_change (U V W : State) (a b : Gauge) (e : SpatialEdge) (A : SU2) :
    PeriodicAugmentedBridge.centralAction U W (Function.update V e A,(a,b)) -
      PeriodicAugmentedBridge.centralAction U W (Function.update V e 1,(a,b)) =
      SU2TraceHessianModel.traceReal (SU2StaplePolar.staple (stapleSet e) (stapleWord U V W a b e))/2 -
      SU2TraceHessianModel.traceReal ((A : SU2TraceHessianModel.M2) *
        SU2StaplePolar.staple (stapleSet e) (stapleWord U V W a b e))/2 := by
  rw [central_action_change, matrix_staple_trace]
  have h := matrix_staple_trace (stapleSet e) (stapleWord U V W a b e) 1
  simp only [Submonoid.coe_one, one_mul] at h
  rw [h, Finset.sum_sub_distrib]

def localDensity (β : ℝ) (U V W : State) (a b : Gauge) (e : SpatialEdge) (A : SU2) : ℝ :=
  PeriodicAugmentedBridge.density β U W (Function.update V e A,(a,b))

def localConstant (β : ℝ) (U V W : State) (a b : Gauge) (e : SpatialEdge) : ℝ :=
  localDensity β U V W a b e 1 * Real.exp (-β *
    (SU2TraceHessianModel.traceReal (SU2StaplePolar.staple (stapleSet e) (stapleWord U V W a b e))/2))

theorem localConstant_pos (β : ℝ) (U V W : State) (a b : Gauge) (e : SpatialEdge) :
    0 < localConstant β U V W a b e :=
  mul_pos (PeriodicAugmentedBridge.density_pos β U W _) (Real.exp_pos _)

theorem localDensity_factor (β : ℝ) (U V W : State) (a b : Gauge) (e : SpatialEdge) (A : SU2) :
    localDensity β U V W a b e A = localConstant β U V W a b e *
      Real.exp ((β/2) * SU2TraceHessianModel.traceReal ((A : SU2TraceHessianModel.M2) *
        SU2StaplePolar.staple (stapleSet e) (stapleWord U V W a b e))) := by
  have h := central_action_matrix_change U V W a b e A
  unfold localConstant localDensity
  rw [PeriodicAugmentedBridge.density_phase, PeriodicAugmentedBridge.density_phase]
  simp only [← Real.exp_add]
  congr 1
  linear_combination -β * h

theorem localDensity_tilt_factor (β : ℝ) (U V W : State) (a b : Gauge) (e : SpatialEdge) (A : SU2) :
    localDensity β U V W a b e A = localConstant β U V W a b e *
      Real.exp (SU2StapleTiltLaw.concentration (stapleSet e) (stapleWord U V W a b e) β *
        SU2StapleTiltLaw.axis (SU2StaplePolar.orientation
          (SU2StaplePolar.quaternionSum (stapleSet e) (stapleWord U V W a b e))) A) := by
  rw [localDensity_factor, SU2StapleTiltLaw.wilson_exponent]

open BoundedExponentialTiltResponse in
theorem localDensity_integral (β : ℝ) (U V W : State) (a b : Gauge) (e : SpatialEdge) :
    (∫ A, localDensity β U V W a b e A ∂law) = localConstant β U V W a b e *
      partition law (SU2StapleTiltLaw.axis (SU2StaplePolar.orientation
        (SU2StaplePolar.quaternionSum (stapleSet e) (stapleWord U V W a b e))))
        (SU2StapleTiltLaw.concentration (stapleSet e) (stapleWord U V W a b e) β) := by
  simp only [localDensity_tilt_factor, integral_const_mul, partition, weighted, one_mul]

open BoundedExponentialTiltResponse in
theorem localDensity_integral_pos (β : ℝ) (U V W : State) (a b : Gauge) (e : SpatialEdge) :
    0 < ∫ A, localDensity β U V W a b e A ∂law := by
  rw [localDensity_integral]
  exact mul_pos (localConstant_pos β U V W a b e) (partition_pos law _
    (SU2StapleTiltLaw.axis_measurable _) (SU2StapleTiltLaw.axis_bound _) _)

open BoundedExponentialTiltResponse in
theorem normalized_link_integral (β : ℝ) (U V W : State) (a b : Gauge) (e : SpatialEdge)
    (f : SU2 → ℝ) :
    (∫ A, f A * localDensity β U V W a b e A ∂law) /
      (∫ A, localDensity β U V W a b e A ∂law) =
      ∫ A, f A ∂SU2StapleTiltLaw.stapleLaw law (stapleSet e) (stapleWord U V W a b e) β := by
  rw [SU2StapleTiltLaw.stapleLaw, tilted_integral law _ f
    (SU2StapleTiltLaw.axis_measurable _) (SU2StapleTiltLaw.axis_bound _), localDensity_integral]
  simp_rw [localDensity_tilt_factor]
  have he : (fun A => f A * (localConstant β U V W a b e *
      Real.exp (SU2StapleTiltLaw.concentration (stapleSet e) (stapleWord U V W a b e) β *
        SU2StapleTiltLaw.axis (SU2StaplePolar.orientation
          (SU2StaplePolar.quaternionSum (stapleSet e) (stapleWord U V W a b e))) A))) =
      fun A => localConstant β U V W a b e * (f A *
      Real.exp (SU2StapleTiltLaw.concentration (stapleSet e) (stapleWord U V W a b e) β *
        SU2StapleTiltLaw.axis (SU2StaplePolar.orientation
          (SU2StaplePolar.quaternionSum (stapleSet e) (stapleWord U V W a b e))) A)) := by
    funext A; ring
  rw [he, integral_const_mul]
  unfold expectation weighted
  exact mul_div_mul_left _ _ (localConstant_pos β U V W a b e).ne'

def linkLaw (β : ℝ) (U V W : State) (a b : Gauge) (e : SpatialEdge) : Measure SU2 :=
  law.withDensity (fun A => ENNReal.ofReal (localDensity β U V W a b e A /
    ∫ B, localDensity β U V W a b e B ∂law))

theorem linkLaw_eq_stapleLaw (β : ℝ) (U V W : State) (a b : Gauge) (e : SpatialEdge) :
    linkLaw β U V W a b e =
      SU2StapleTiltLaw.stapleLaw law (stapleSet e) (stapleWord U V W a b e) β := by
  rw [linkLaw, SU2StapleTiltLaw.stapleLaw_density]
  congr 1
  funext A
  congr 1
  rw [localDensity_factor, localDensity_integral, SU2StapleTiltLaw.partition_axis]
  exact mul_div_mul_left _ _ (localConstant_pos β U V W a b e).ne'

theorem linkLaw_probability (β : ℝ) (U V W : State) (a b : Gauge) (e : SpatialEdge) :
    IsProbabilityMeasure (linkLaw β U V W a b e) := by
  rw [linkLaw_eq_stapleLaw]
  exact SU2StapleTiltLaw.stapleLaw_probability _ _ _ _

/-- The frozen-other-fields density has a uniform, all-direction six-staple variance bound.
Global disintegration of the augmented measure is a further theorem. -/
theorem linkLaw_variance_lower (β : ℝ) (hβ : 0 ≤ β) (U V W : State)
    (a b : Gauge) (e : SpatialEdge) (C : SU2) :
    6/(49*(1+6*β)^2) ≤ (∫ A, halfTrace (C*A)^2 ∂linkLaw β U V W a b e) -
      (∫ A, halfTrace (C*A) ∂linkLaw β U V W a b e)^2 := by
  rw [linkLaw_eq_stapleLaw]
  have h := QuaternionTiltCovariance.staple_directional_variance_lower law (stapleSet e)
    (stapleWord U V W a b e) β hβ C
  have hc : ((stapleSet e).card:ℝ) ≤ 6 := by exact_mod_cast stapleSet_card_le e
  have hn : 0 ≤ ((stapleSet e).card:ℝ) := Nat.cast_nonneg _
  have hm : β*((stapleSet e).card:ℝ) ≤ 6*β := by nlinarith
  have hsq : (1+β*((stapleSet e).card:ℝ))^2 ≤ (1+6*β)^2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  apply le_trans _ h
  apply (div_le_div_iff₀ (by positivity : 0 < 49*(1+6*β)^2)
    (by positivity : 0 < 49*(1+β*((stapleSet e).card:ℝ))^2)).mpr
  nlinarith


theorem linkLaw_update_base (β : ℝ) (U V W : State) (a b : Gauge) (e : SpatialEdge) (D : SU2) :
    linkLaw β U (Function.update V e D) W a b e = linkLaw β U V W a b e := by
  classical
  have hu (A : SU2) : Function.update (Function.update V e D) e A = Function.update V e A := by
    funext f
    by_cases h : f = e
    · subst f; simp only [Function.update_self]
    · simp only [Function.update_of_ne h]
  unfold linkLaw localDensity
  simp_rw [hu]

end OperatorDerivativeRewrite.Foundation.PeriodicLinkStaples
