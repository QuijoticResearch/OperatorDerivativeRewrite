import Foundation.CubeAxialSlice

/-! An explicit rooted gauge map for every actual cube boundary state and
nonlinear spatial confinement modulo that gauge. No measure quotient is assumed. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CubeAxialGauge
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab CubeSlabGauge
open CubeAxialSlice FourCubePinnedCoercivity

private def xEdge : SpatialEdge := ⟨(![0,0,0],0),rfl⟩
private def yEdge (x : Fin 2) : SpatialEdge := ⟨(![x,0,0],1),rfl⟩
private def zEdge (x y : Fin 2) : SpatialEdge := ⟨(![x,y,0],2),rfl⟩

/-- Ordered actual tree-path products, anchored to1 at the origin. -/
def rootedGauge (U : State) (v : SpatialVertex) : SU2 :=
  (if v 0=1 then U xEdge else 1)*
    (if v 1=1 then U (yEdge (v 0)) else 1)*
    (if v 2=1 then U (zEdge (v 0) (v 1)) else 1)

def reduced (U : State) (i : Fin 5) : SU2 :=
  gaugeAction (rootedGauge U) U (chordEdge i)

private theorem vertex_coordinates (v : SpatialVertex) :
    ∃ x y z : Fin 2, v=![x,y,z] := by
  refine ⟨v 0,v 1,v 2,?_⟩
  ext i
  fin_cases i <;> rfl

private theorem update0 (x y z : Fin 2) :
    Function.update (![x,y,z] : SpatialVertex) 0 1=![1,y,z] := by
  ext i
  fin_cases i <;> simp [Function.update_apply]

private theorem update1 (x y z : Fin 2) :
    Function.update (![x,y,z] : SpatialVertex) 1 1=![x,1,z] := by
  ext i
  fin_cases i <;> simp [Function.update_apply]

private theorem update2 (x y z : Fin 2) :
    Function.update (![x,y,z] : SpatialVertex) 2 1=![x,y,1] := by
  ext i
  fin_cases i <;> simp [Function.update_apply]

/-- The anchored tree gauge retains exactly the root conjugation under a gauge change. -/
theorem rooted_covariant (a : Gauge) (U : State) (v : SpatialVertex) :
    rootedGauge (gaugeAction a U) v=
      a (![0,0,0] : SpatialVertex)*rootedGauge U v*(a v)⁻¹ := by
  obtain ⟨x,y,z,hv⟩ := vertex_coordinates v
  subst v
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [rootedGauge,gaugeAction,xEdge,yEdge,zEdge,shift,update0,update1,update2] <;> group

/-- The rooted gauge sends EVERY state to the specified actual five-chord slice. -/
theorem reconstruction (U : State) :
    gaugeAction (rootedGauge U) U=axialState (reduced U) := by
  funext e
  rcases e with ⟨⟨v,a⟩,he⟩
  change v a=0 at he
  obtain ⟨x,y,z,hv⟩ := vertex_coordinates v
  subst v
  fin_cases a <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [axialState,chordLabel,reduced,chordEdge,gaugeAction,rootedGauge,
      xEdge,yEdge,zEdge,shift,Function.update] at *
  all_goals try group
  all_goals
    exfalso
    revert he
    decide +kernel

/-- Five chord coordinates are covariant, not falsely declared individually invariant. -/
theorem reduced_covariant (a : Gauge) (U : State) (i : Fin 5) :
    reduced (gaugeAction a U) i=
      a (![0,0,0] : SpatialVertex)*reduced U i*(a (![0,0,0] : SpatialVertex))⁻¹ := by
  change rootedGauge (gaugeAction a U) (chordEdge i).val.1*
      (a (chordEdge i).val.1*U (chordEdge i)*(a (shift (chordEdge i).val.1 (chordEdge i).val.2))⁻¹)*
      (rootedGauge (gaugeAction a U) (shift (chordEdge i).val.1 (chordEdge i).val.2))⁻¹=
    a (![0,0,0] : SpatialVertex)*
      (rootedGauge U (chordEdge i).val.1*U (chordEdge i)*
        (rootedGauge U (shift (chordEdge i).val.1 (chordEdge i).val.2))⁻¹)*
      (a (![0,0,0] : SpatialVertex))⁻¹
  simp_rw [rooted_covariant]
  group

/-- The canonical defect energy is an actual gauge-invariant observable. -/
theorem energy_invariant (a : Gauge) (U : State) :
    chordEnergy (reduced (gaugeAction a U))=chordEnergy (reduced U) := by
  unfold chordEnergy defect
  simp_rw [reduced_covariant,halfTrace_conjugate]

/-- Global nonlinear control of the canonical chord defects for every original state. -/
theorem coercive_mod_gauge (U : State) : chordEnergy (reduced U) ≤ 4*spatialAction U := by
  have h := axial_coercive (reduced U)
  rw [← reconstruction,spatial_action_invariant] at h
  exact h

private theorem axial_one : axialState (fun _ => (1 : SU2))=(1 : State) := by
  funext e
  unfold axialState
  cases chordLabel e <;> rfl

/-- Exact flatness characterization on this simply connected actual cube.
No extension to other topology, boundary gauges or infinite volume is assumed. -/
theorem flat_iff_gauge (U : State) :
    spatialAction U=0 ↔ ∃ a : Gauge, gaugeAction a U=(1 : State) := by
  constructor
  · intro hflat
    have hE : chordEnergy (reduced U)=0 := by
      have h := coercive_mod_gauge U
      rw [hflat,mul_zero] at h
      exact le_antisymm h (Finset.sum_nonneg (fun i _ => defect_nonneg _))
    have hq : reduced U=(fun _ => (1 : SU2)) := by
      funext i
      have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) =>
        defect_nonneg (reduced U j)) (Finset.mem_univ i)
      change defect (reduced U i) ≤ chordEnergy (reduced U) at h
      rw [hE] at h
      exact (defect_zero_iff _).mp (le_antisymm h (defect_nonneg _))
    refine ⟨rootedGauge U,?_⟩
    rw [reconstruction,hq,axial_one]
  · rintro ⟨a,ha⟩
    have h := spatial_action_invariant a U
    rw [ha] at h
    rw [← h]
    simp [spatialAction,spatialWord,SU2OpenLinkGaugeObstruction.halfTrace_one]

end OperatorDerivativeRewrite.Foundation.CubeAxialGauge
