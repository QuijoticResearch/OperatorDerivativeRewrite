import Foundation.FourCubePinnedHaar

/-! Global nonlinear control at identity boundary for the actual pinned72-face action. -/
noncomputable section
open MeasureTheory
open scoped Quaternion
namespace OperatorDerivativeRewrite.Foundation.FourCubePinnedCoercivity
open QuaternionSU2Representation OneSidedBlockIncidence OneSidedBlockRank
open OneSidedCapComplex FourCubeHaarParity FourCubeHaarChannels FourCubeIntegratedCubic
open FourCubePinnedHaar
open OneSidedPinnedInterior (pole Free)
attribute [local irreducible] edges upperFaces

def defect (U : SU2) : ℝ := 1-halfTrace U

theorem defect_nonneg (U : SU2) : 0 ≤ defect U := by
  have h := (abs_le.mp (halfTrace_bound U)).2
  exact sub_nonneg.mpr h

theorem defect_one : defect 1=0 := by
  rw [defect,FourCubeWilsonCubic.trace_one,sub_self]

theorem defect_inv (U : SU2) : defect U⁻¹=defect U := by
  change 1-halfTrace U⁻¹=1-halfTrace U
  rw [SU2WilsonConvolution.halfTrace_inv]

private theorem quaternion_distance (u : QuaternionAngularHaar.Group) :
    ‖(u : ℍ)-1‖^2=2*(1-(u : ℍ).re) := by
  have hn : Quaternion.normSq (u : ℍ)=1 := by
    rw [Quaternion.normSq_eq_norm_mul_self,CStarRing.norm_coe_unitary,one_mul]
  rw [pow_two,← Quaternion.normSq_eq_norm_mul_self]
  norm_num [Quaternion.normSq_def'] at hn ⊢
  nlinarith

theorem defect_zero_iff (U : SU2) : defect U=0 ↔ U=1 := by
  constructor
  · intro h
    obtain ⟨u,rfl⟩ := hom_surjective U
    have hd := quaternion_distance u
    have hr : (u : ℍ).re=1 := by
      have hr : 1-(u : ℍ).re=0 := by
        simpa only [defect,halfTrace_map,QuaternionAngularHaar.realCoordinate] using h
      linarith
    rw [hr] at hd
    have hz : (u : ℍ)-1=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg ((u : ℍ)-1)])
    have hu : u=1 := Subtype.ext (sub_eq_zero.mp hz)
    simp [hu]
  · intro h
    rw [h,defect_one]

theorem defect_triple (A B C : SU2) :
    defect (A*B*C) ≤ 3*(defect A+defect B+defect C) := by
  obtain ⟨a,rfl⟩ := hom_surjective A
  obtain ⟨b,rfl⟩ := hom_surjective B
  obtain ⟨c,rfl⟩ := hom_surjective C
  have he : ((a*b*c : QuaternionAngularHaar.Group) : ℍ)-1=
      (((a : ℍ)-1)*(b : ℍ))*c+((b : ℍ)-1)*c+((c : ℍ)-1) := by
    change (a : ℍ)*(b : ℍ)*(c : ℍ)-1=_
    noncomm_ring
  have ht : ‖((a*b*c : QuaternionAngularHaar.Group) : ℍ)-1‖ ≤
      ‖(a : ℍ)-1‖+‖(b : ℍ)-1‖+‖(c : ℍ)-1‖ := by
    rw [he]
    calc
      _  ≤  ‖(((a : ℍ)-1)*(b : ℍ))*c+((b : ℍ)-1)*c‖+‖(c : ℍ)-1‖ := norm_add_le _ _
      _  ≤  (‖(((a : ℍ)-1)*(b : ℍ))*c‖+‖((b : ℍ)-1)*c‖)+‖(c : ℍ)-1‖ :=
        by have h := norm_add_le (((a : ℍ)-1)*(b : ℍ)*(c : ℍ)) (((b : ℍ)-1)*(c : ℍ)); linarith
      _ = _ := by simp only [norm_mul,CStarRing.norm_coe_unitary,mul_one]
  have hs := sq_le_sq₀ (norm_nonneg (((a*b*c : QuaternionAngularHaar.Group) : ℍ)-1)) (by positivity :
    0 ≤ ‖(a : ℍ)-1‖+‖(b : ℍ)-1‖+‖(c : ℍ)-1‖)
  have hsq := hs.mpr ht
  have ha := quaternion_distance a
  have hb := quaternion_distance b
  have hc := quaternion_distance c
  have habc := quaternion_distance (a*b*c)
  simp only [defect,← hom.map_mul,halfTrace_map,QuaternionAngularHaar.realCoordinate]
  nlinarith [sq_nonneg (‖(a : ℍ)-1‖-‖(b : ℍ)-1‖),
    sq_nonneg (‖(a : ℍ)-1‖-‖(c : ℍ)-1‖),
    sq_nonneg (‖(b : ℍ)-1‖-‖(c : ℍ)-1‖)]


def vacuumAction (s : InteriorState) : ℝ :=
  FourCubeBoundaryCubic.fullAction (fill (fun _ => 1) s)

def ribbonEnergy (s : InteriorState) : ℝ := ∑ p : Upper,defect (s (ribbonInterior p))

def faceWord (s : InteriorState) (p : FaceData) : SU2 :=
  coreField s (p.1,p.2.1)*coreField s (shifted p.1 p.2.1,p.2.2)*
    (coreField s (shifted p.1 p.2.2,p.2.1))⁻¹*(coreField s (p.1,p.2.2))⁻¹

theorem vacuum_decomposition (s : InteriorState) :
    vacuumAction s=internalAction s+ribbonEnergy s := by
  unfold vacuumAction FourCubeBoundaryCubic.fullAction
  rw [retained_fill]
  simp only [ribbon_fill,word,inv_one,mul_one]
  rfl

private theorem inner_nonneg (s : InteriorState) : 0 ≤ internalAction s := by
  unfold internalAction FourCubeWilsonCubic.innerAction
  apply Finset.sum_nonneg
  intro p _
  exact defect_nonneg (faceWord s p)

private theorem ribbon_nonneg (s : InteriorState) : 0 ≤ ribbonEnergy s :=
  Finset.sum_nonneg (fun p _ => defect_nonneg _)

theorem vacuum_nonneg (s : InteriorState) : 0 ≤ vacuumAction s := by
  rw [vacuum_decomposition]
  exact add_nonneg (inner_nonneg s) (ribbon_nonneg s)

private theorem face_le_inner (s : InteriorState) (p : FaceData) (hp : p∈innerFaces) :
    defect (faceWord s p) ≤ internalAction s := by
  exact Finset.single_le_sum (fun q _ => defect_nonneg (faceWord s q)) hp

private theorem ribbon_le (s : InteriorState) (p : Upper) :
    defect (s (ribbonInterior p)) ≤ ribbonEnergy s :=
  by
    unfold ribbonEnergy
    exact Finset.single_le_sum (fun q _ => defect_nonneg (s (ribbonInterior q)))
      (Finset.mem_univ p)

private theorem ribbon_pair_le (s : InteriorState) (p q : Upper) (hpq : p≠q) :
    defect (s (ribbonInterior p))+defect (s (ribbonInterior q)) ≤ ribbonEnergy s := by
  rw [ribbonEnergy,← Finset.sum_pair hpq (f := fun r : Upper => defect (s (ribbonInterior r)))]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro r _ _
  exact defect_nonneg _

private theorem off_ribbon (e : Interior) (he : e.val.1≠origin) :
    ∃ p : Upper,ribbonInterior p=e := by
  obtain ⟨j,hj⟩ := OneSidedBlockKernel.upper_witness e.val e.property he
  exact ⟨⟨(e.val,j),hj⟩,Subtype.ext rfl⟩

theorem off_origin_bound (s : InteriorState) (e : Interior) (he : e.val.1≠origin) :
    defect (s e) ≤ vacuumAction s := by
  obtain ⟨p,hp⟩ := off_ribbon e he
  have hh := ribbon_le s p
  rw [hp] at hh
  rw [vacuum_decomposition]
  linarith [inner_nonneg s]

private theorem core_on (s : InteriorState) (e : Interior) : coreField s e.val=s e := by
  simp [coreField,e.property]

private theorem root_bound (s : InteriorState) (hs : s pole=1) (j : Fin 3) :
    defect (s ⟨(origin,j.succ),by simp [edges,origin]⟩) ≤ 3*vacuumAction s := by
  have hj : (0 : Fin 4)≠j.succ := Ne.symm (Fin.succ_ne_zero j)
  have ha := OneSidedBlockKernel.shifted_edge_geometry 0 j.succ hj
  have hb := OneSidedBlockKernel.shifted_edge_geometry j.succ 0 (Fin.succ_ne_zero j)
  let a : Interior := ⟨(shifted origin 0,j.succ),ha.1⟩
  let b : Interior := ⟨(shifted origin j.succ,0),hb.1⟩
  let c : Interior := ⟨(origin,j.succ),by simp [edges,origin]⟩
  have hab : a≠b := by
    intro he
    have hd := congrArg (fun e : Interior => e.val.2) he
    exact Fin.succ_ne_zero j hd
  obtain ⟨p,hp⟩ := off_ribbon a ha.2
  obtain ⟨q,hq⟩ := off_ribbon b hb.2
  have hpq : p≠q := by
    intro he
    apply hab
    rw [← hp,← hq,he]
  have hpair := ribbon_pair_le s p q hpq
  rw [hp,hq] at hpair
  let f : FaceData := (origin,(0,j.succ))
  have hf := face_le_inner s f (OneSidedBlockKernel.origin_face_geometry j)
  have hw : faceWord s f=s a*(s b)⁻¹*(s c)⁻¹ := by
    have h0 : coreField s (origin,0)=1 := (core_on s pole).trans hs
    change coreField s (origin,0)*coreField s a.val*(coreField s b.val)⁻¹*
      (coreField s c.val)⁻¹=_
    rw [h0,one_mul,core_on,core_on,core_on]
  have he : s c=(faceWord s f)⁻¹*s a*(s b)⁻¹ := by rw [hw]; group
  have ht := defect_triple (faceWord s f)⁻¹ (s a) (s b)⁻¹
  rw [← he,defect_inv,defect_inv] at ht
  change defect (s c) ≤ 3*vacuumAction s
  rw [vacuum_decomposition]
  linarith

/-- A global nonlinear, pointwise link estimate at identity boundary, with the root edge pinned. -/
theorem pinned_link_bound (s : InteriorState) (hs : s pole=1) (e : Interior) :
    defect (s e) ≤ 3*vacuumAction s := by
  by_cases he : e.val.1=origin
  · rcases e with ⟨⟨v,i⟩,hi⟩
    dsimp at he
    subst v
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      change defect (s pole) ≤ 3*vacuumAction s
      rw [hs,defect_one]
      exact mul_nonneg (by norm_num) (vacuum_nonneg s)
    · intro hi
      exact root_bound s hs j
  · have hh := off_origin_bound s e he
    linarith [vacuum_nonneg s]

def pinnedAction (y : PinnedState) : ℝ := vacuumAction (fillPole 1 y)

theorem pinnedAction_nonneg (y : PinnedState) : 0 ≤ pinnedAction y := vacuum_nonneg _

theorem pinned_coordinate_bound (y : PinnedState) (e : Free) :
    defect (y e) ≤ 3*pinnedAction y := by
  have hs : fillPole 1 y pole=1 := by simp [fillPole]
  have hh := pinned_link_bound (fillPole 1 y) hs e.val
  simpa only [pinnedAction,fillPole,dif_neg e.property] using hh

theorem vacuum_one : vacuumAction (fun _ => 1)=0 := by
  have hc : coreField (fun _ => 1)=fun _ => 1 := by funext e; simp [coreField]
  rw [vacuum_decomposition]
  simp [internalAction,FourCubeWilsonCubic.innerAction,FourCubeWilsonCubic.faceAction,
    hc,FourCubeWilsonCubic.trace_one,ribbonEnergy,defect_one]

theorem pinnedAction_zero_iff (y : PinnedState) : pinnedAction y=0 ↔ y=1 := by
  constructor
  · intro h
    funext e
    have hh := pinned_coordinate_bound y e
    rw [h,mul_zero] at hh
    exact (defect_zero_iff _).mp (le_antisymm hh (defect_nonneg _))
  · intro h
    subst y
    have hf : fillPole 1 (1 : PinnedState)=fun _ => 1 := by
      funext e
      simp [fillPole]
    rw [pinnedAction,hf,vacuum_one]

theorem pinnedAction_positive_iff (y : PinnedState) : 0<pinnedAction y ↔ y≠1 := by
  constructor
  · intro h he
    exact h.ne' ((pinnedAction_zero_iff y).mpr he)
  · intro h
    exact lt_of_le_of_ne (pinnedAction_nonneg y)
      (fun he => h ((pinnedAction_zero_iff y).mp he.symm))

theorem global_energy_barrier (y : PinnedState) (e : Free) (ε : ℝ)
    (he : ε ≤ defect (y e)) : ε/3 ≤ pinnedAction y := by
  linarith [pinned_coordinate_bound y e]


theorem pinnedAction_measurable : Measurable pinnedAction := by
  have hf : Measurable (fun y : PinnedState => fillPole 1 y) := by
    simpa only [Function.comp_def,id_eq] using
      fillPole_measurable.comp (measurable_const.prodMk measurable_id)
  exact (FourCubeHaarParity.fullAction_measurable.comp (fill_measurable (fun _ => 1))).comp hf

theorem boltzmann_integrable (β : ℝ) :
    Integrable (fun y => Real.exp (-β*pinnedAction y)) pinnedHaar := by
  have hm : Measurable (fun y => Real.exp (-β*pinnedAction y)) :=
    (measurable_const.mul pinnedAction_measurable).exp
  apply (integrable_const (Real.exp (144*|β|))).mono' hm.aestronglyMeasurable
  filter_upwards with y
  simpa only [weight,pinnedAction,vacuumAction,Real.norm_eq_abs] using
    weight_bound β (fun _ => 1) (fillPole 1 y)

theorem boltzmann_barrier (β ε : ℝ) (hβ : 0 ≤ β) (y : PinnedState) (e : Free)
    (he : ε ≤ defect (y e)) :
    Real.exp (-β*pinnedAction y) ≤ Real.exp (-β*(ε/3)) := by
  apply Real.exp_le_exp.mpr
  have hh := global_energy_barrier y e ε he
  nlinarith

theorem tail_event_measurable (e : Free) (ε : ℝ) :
    MeasurableSet {y : PinnedState | ε ≤ defect (y e)} :=
  measurableSet_le measurable_const
    (measurable_const.sub (halfTrace_measurable.comp (measurable_pi_apply e)))

/-- An actual unnormalized Haar-tail integral. Normalizing by the partition still requires
an appropriate LOWER partition bound; no normalized Gibbs concentration is asserted here. -/
theorem boltzmann_tail_bound (β ε : ℝ) (hβ : 0 ≤ β) (e : Free) :
    (∫ y in {y : PinnedState | ε ≤ defect (y e)},Real.exp (-β*pinnedAction y) ∂pinnedHaar)
      ≤ Real.exp (-β*(ε/3)) := by
  have hh := norm_setIntegral_le_of_norm_le_const
    (μ := pinnedHaar) (s := {y : PinnedState | ε ≤ defect (y e)})
    (f := fun y => Real.exp (-β*pinnedAction y))
    (measure_lt_top _ _) (fun y hy => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact boltzmann_barrier β ε hβ y e hy)
  have hm : pinnedHaar.real {y : PinnedState | ε ≤ defect (y e)} ≤ 1 := measureReal_le_one
  have ht := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-β*(ε/3))).le
  simp only [mul_one] at ht
  exact (le_abs_self _).trans (hh.trans ht)

end OperatorDerivativeRewrite.Foundation.FourCubePinnedCoercivity
