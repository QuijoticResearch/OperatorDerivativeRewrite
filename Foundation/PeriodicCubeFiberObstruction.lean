import Foundation.PeriodicPlaquetteSpanFrame
import Foundation.SU2JointPlaquetteCubic
import Foundation.SU2HemisphereChart

/-! A rough original spatial field where a nonzero six-face observable is
constant on every one-link fiber of its cube. This is a pointwise obstruction,
not an averaged frame or stationary spectral obstruction. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace OperatorDerivativeRewrite.Foundation.PeriodicCubeFiberObstruction
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicLinkStaples
open PeriodicCurvatureVariance
private abbrev vertexDecidableEq : DecidableEq SpatialVertex :=
  fun a b => Fintype.decidablePiFintype a b
attribute [local instance] vertexDecidableEq

def quarter : SU2 := SU2JointPlaquetteCubic.axis 0 (Real.pi/2)

def flux (e : SpatialEdge) : SU2 :=
  if e.2=0 then 1 else if e.2=1 then quarter^((e.1 0).val)
    else quarter^((e.1 0).val+(e.1 1).val)

def face : Fin 6 → SpatialFace := ![
  ⟨(![0,0,0],(1,2)),by decide⟩, ⟨(![1,0,0],(1,2)),by decide⟩,
  ⟨(![0,0,0],(0,2)),by decide⟩, ⟨(![0,1,0],(0,2)),by decide⟩,
  ⟨(![0,0,0],(0,1)),by decide⟩, ⟨(![0,0,1],(0,1)),by decide⟩]

def edge : Fin 12 → SpatialEdge := ![
  (![0,0,0],0),(![0,0,1],0),(![0,1,0],0),(![0,1,1],0),
  (![0,0,0],1),(![0,0,1],1),(![1,0,0],1),(![1,0,1],1),
  (![0,0,0],2),(![0,1,0],2),(![1,0,0],2),(![1,1,0],2)]

def observable (V : State) : ℝ :=
  -plaquette (face 0) V+plaquette (face 1) V+plaquette (face 2) V-
    plaquette (face 3) V-plaquette (face 4) V+plaquette (face 5) V

private def lift (A : SU2) : ℍ := (equiv.symm A : QuaternionAngularHaar.Group)
private theorem lift_mul (A B : SU2) : lift (A*B)=lift A*lift B :=
  congrArg (fun u : QuaternionAngularHaar.Group => (u : ℍ)) (equiv.symm.map_mul A B)
private theorem lift_one : lift 1=1 := by
  exact congrArg (fun u : QuaternionAngularHaar.Group => (u : ℍ)) equiv.symm.map_one
private theorem lift_inv (A : SU2) : lift A⁻¹=star (lift A) := by
  change ((equiv.symm A⁻¹ : QuaternionAngularHaar.Group) : ℍ)=_
  rw [equiv.symm.map_inv]
  rfl
private theorem lift_quarter : lift quarter=⟨0,1,0,0⟩ := by
  change ((equiv.symm (equiv _) : QuaternionAngularHaar.Group) : ℍ)=_
  rw [equiv.symm_apply_apply]
  norm_num [SU2JointPlaquetteCubic.axisRaw]
private theorem trace_lift (A : SU2) : halfTrace A=(lift A).re := by
  obtain ⟨u,rfl⟩ := hom_surjective A
  change SU2TraceHessianModel.traceReal (repr (u : ℍ))/2=_
  rw [repr_halfTrace]
  change _=(((equiv.symm (equiv u)) : QuaternionAngularHaar.Group) : ℍ).re
  rw [equiv.symm_apply_apply]

private theorem fiber0 (A : SU2) :
    observable (Function.update flux (edge 0) A)=0 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

private theorem fiber1 (A : SU2) :
    observable (Function.update flux (edge 1) A)=0 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

private theorem fiber2 (A : SU2) :
    observable (Function.update flux (edge 2) A)=0 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

private theorem fiber3 (A : SU2) :
    observable (Function.update flux (edge 3) A)=0 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

private theorem fiber4 (A : SU2) :
    observable (Function.update flux (edge 4) A)=0 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

private theorem fiber5 (A : SU2) :
    observable (Function.update flux (edge 5) A)=0 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

private theorem fiber6 (A : SU2) :
    observable (Function.update flux (edge 6) A)=0 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

private theorem fiber7 (A : SU2) :
    observable (Function.update flux (edge 7) A)=0 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

private theorem fiber8 (A : SU2) :
    observable (Function.update flux (edge 8) A)=0 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

private theorem fiber9 (A : SU2) :
    observable (Function.update flux (edge 9) A)=0 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

private theorem fiber10 (A : SU2) :
    observable (Function.update flux (edge 10) A)=0 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

private theorem fiber11 (A : SU2) :
    observable (Function.update flux (edge 11) A)=0 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  all_goals ring

theorem cube_fiber_zero (i : Fin 12) (A : SU2) :
    observable (Function.update flux (edge i) A)=0 := by
  fin_cases i
  · exact fiber0 A
  · exact fiber1 A
  · exact fiber2 A
  · exact fiber3 A
  · exact fiber4 A
  · exact fiber5 A
  · exact fiber6 A
  · exact fiber7 A
  · exact fiber8 A
  · exact fiber9 A
  · exact fiber10 A
  · exact fiber11 A

theorem face_injective : Function.Injective face := by
  change ∀ i j, face i=face j → i=j
  decide +kernel

theorem edge_injective : Function.Injective edge := by
  change ∀ i j, edge i=edge j → i=j
  decide +kernel

/-- The invisible one-link fibers do not make the true two-link section constant. -/
theorem two_link_response :
    observable (Function.update (Function.update flux (edge 6) 1) (edge 11) 1)= -2 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  have hv : (1 : ZMod 4).val=1 := by decide
  norm_num [h01,h10,hv,observable,plaquette,face,spatialWord,Function.update_apply,edge,
    shift,funext_iff,Fin.forall_fin_succ,flux,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]

theorem observable_flux : observable flux=0 := by
  simpa only [Function.update_eq_self] using cube_fiber_zero 0 (flux (edge 0))

theorem observable_one : observable (fun _ => 1)=0 := by
  norm_num [observable,plaquette,spatialWord,SU2OpenLinkGaugeObstruction.halfTrace_one]

def witness : State := Function.update (fun _ => 1) (edge 4) (quarter^2)

theorem observable_witness : observable witness=4 := by
  have h01 : (0 : ZMod 4)≠1 := by decide
  have h10 : (1 : ZMod 4)≠0 := by decide
  norm_num [h01,h10,observable,witness,plaquette,face,spatialWord,Function.update_apply,
    edge,shift,funext_iff,Fin.forall_fin_succ,pow_succ,trace_lift,lift_mul,lift_inv,
    lift_one,lift_quarter,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]

theorem observable_nonconstant : ¬∃ c : ℝ, ∀ V, observable V=c := by
  rintro ⟨c,hc⟩
  have h1 := hc (fun _ => 1)
  have h2 := hc witness
  rw [observable_one] at h1
  rw [observable_witness] at h2
  linarith

theorem edge_covers_faces (k : Fin 6) (j : Fin 4) :
    ∃ i : Fin 12, edge i=faceEdge (face k) j := by
  revert k j
  decide +kernel

theorem observable_measurable : Measurable observable :=
  (((((plaquette_measurable (face 0)).neg.add (plaquette_measurable (face 1))).add
    (plaquette_measurable (face 2))).sub (plaquette_measurable (face 3))).sub
    (plaquette_measurable (face 4))).add (plaquette_measurable (face 5))

theorem observable_bound (V : State) : |observable V|≤6 := by
  have h (i : Fin 6) := abs_le.mp (halfTrace_bound (spatialWord V (face i)))
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  have h3 := h 3; have h4 := h 4; have h5 := h 5
  unfold observable plaquette
  rw [abs_le]
  constructor <;> linarith

theorem observable_memLp (μ : Measure State) [IsFiniteMeasure μ] :
    MemLp observable 2 μ :=
  MemLp.of_bound observable_measurable.aestronglyMeasurable 6
    (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using observable_bound V))

theorem observable_gauge (g : Gauge) (V : State) :
    observable (PeriodicSlabGauge.gaugeAction g V)=observable V := by
  unfold observable plaquette
  simp only [PeriodicSlabGauge.spatial_word_covariant,halfTrace_conjugate]

theorem observable_center_even (i : Fin 3) (V : State) :
    observable (PeriodicCenterSeam.flip i V)=observable V := by
  unfold observable plaquette
  simp only [PeriodicCenterSeam.spatial_word]

def rest (i : Fin 12) (a b : Gauge) : PeriodicLinkDisintegration.Rest (edge i) :=
  ((PeriodicLinkDisintegration.split (edge i)) (flux,(a,b))).1

theorem assemble_flux (i : Fin 12) (a b : Gauge) (A : SU2) :
    (PeriodicLinkDisintegration.split (edge i)).symm (rest i a b,A)=
      (Function.update flux (edge i) A,(a,b)) := by
  apply (PeriodicLinkDisintegration.split (edge i)).injective
  rw [(PeriodicLinkDisintegration.split (edge i)).apply_symm_apply,
    PeriodicLinkDisintegration.split_apply]
  apply Prod.ext
  · apply Prod.ext
    · funext j
      change flux j = Function.update flux (edge i) A j
      exact (Function.update_of_ne j.property _ _).symm
    · rfl
  · change A = Function.update flux (edge i) A (edge i)
    simp only [Function.update_self]

theorem conditional_mean_zero (i : Fin 12) (β : ℝ) (U W : State) (a b : Gauge) :
    PeriodicNativeCompression.conditionalMean (edge i) β U W (fun q => observable q.1)
      (rest i a b)=0 := by
  simp only [PeriodicNativeCompression.conditionalMean,assemble_flux,cube_fiber_zero,
    integral_zero]

def fiberNoise (β : ℝ) (U W V : State) (a b : Gauge) : ℝ :=
  ∑ i : Fin 12, ∫ A,
    (observable ((PeriodicLinkDisintegration.split (edge i)).symm
      (((PeriodicLinkDisintegration.split (edge i)) (V,(a,b))).1,A)).1-
    PeriodicNativeCompression.conditionalMean (edge i) β U W (fun q => observable q.1)
      (((PeriodicLinkDisintegration.split (edge i)) (V,(a,b))).1))^2
    ∂PeriodicLinkDisintegration.conditionalKernel (edge i) β U W
      (((PeriodicLinkDisintegration.split (edge i)) (V,(a,b))).1)

theorem fiberNoise_flux (β : ℝ) (U W : State) (a b : Gauge) :
    fiberNoise β U W flux a b=0 := by
  change (∑ i : Fin 12, ∫ A,
    (observable ((PeriodicLinkDisintegration.split (edge i)).symm (rest i a b,A)).1-
    PeriodicNativeCompression.conditionalMean (edge i) β U W (fun q => observable q.1)
      (rest i a b))^2 ∂PeriodicLinkDisintegration.conditionalKernel (edge i) β U W
        (rest i a b))=0
  simp only [assemble_flux,cube_fiber_zero,conditional_mean_zero,sub_self,zero_pow
    (by decide : 2≠0),integral_zero,Finset.sum_const_zero]

/-- Even summing every cube-edge row cannot yield an everywhere positive
coefficient floor for this nonconstant gauge-invariant center-even observable. -/
theorem no_uniform_pointwise_floor (β : ℝ) (U W : State) (κ : ℝ) (hκ : 0 < κ) :
    ¬∀ (V : State) (a b : Gauge), 6*κ≤fiberNoise β U W V a b := by
  intro h
  have hx := h flux 1 1
  rw [fiberNoise_flux] at hx
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicCubeFiberObstruction
