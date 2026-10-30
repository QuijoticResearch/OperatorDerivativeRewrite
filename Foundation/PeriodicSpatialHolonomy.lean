import Foundation.PeriodicSlabGround
import Foundation.SU2HolonomyTraceObstruction

/-! Actual periodic spatial winding loops. Flat plaquettes imply commuting
based holonomies, rather than all flat fields being pure gauge. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicSpatialHolonomy
open PeriodicTemporalSlab QuaternionSU2Representation

def twice (v : SpatialVertex) (i : Fin 3) : SpatialVertex := shift (shift v i) i
def thrice (v : SpatialVertex) (i : Fin 3) : SpatialVertex := shift (twice v i) i

theorem shift_four (v : SpatialVertex) (i : Fin 3) : shift (thrice v i) i=v := by
  funext k
  unfold thrice twice shift
  by_cases h : k=i
  · simp only [h,ite_true]
    have h4 : (4 : ZMod 4)=0 := by decide
    calc
      v i+1+1+1+1=v i+4 := by ring
      _ = v i := by rw [h4,add_zero]
  · simp [h]

private theorem shift_commute (v : SpatialVertex) (i j : Fin 3) :
    shift (shift v i) j=shift (shift v j) i := by
  funext k
  simp only [shift]
  abel

private theorem twice_shift (v : SpatialVertex) (i j : Fin 3) :
    twice (shift v j) i=shift (twice v i) j := by
  unfold twice
  rw [shift_commute v j i,shift_commute (shift v i) j i]

private theorem thrice_shift (v : SpatialVertex) (i j : Fin 3) :
    thrice (shift v j) i=shift (thrice v i) j := by
  unfold thrice
  rw [twice_shift,shift_commute]

def winding (U : State) (v : SpatialVertex) (i : Fin 3) : SU2 :=
  U (v,i)*U (shift v i,i)*U (twice v i,i)*U (thrice v i,i)

theorem winding_gauge (a : Gauge) (U : State) (v : SpatialVertex) (i : Fin 3) :
    winding (PeriodicSlabGauge.gaugeAction a U) v i=a v*winding U v i*(a v)⁻¹ := by
  unfold winding PeriodicSlabGauge.gaugeAction
  rw [shift_four]
  unfold thrice twice
  group

theorem trace_gauge (a : Gauge) (U : State) (v : SpatialVertex) (i : Fin 3) :
    halfTrace (winding (PeriodicSlabGauge.gaugeAction a U) v i)=halfTrace (winding U v i) := by
  rw [winding_gauge,halfTrace_conjugate]

theorem product_trace_gauge (a : Gauge) (U : State) (v : SpatialVertex) (i j : Fin 3) :
    halfTrace (winding (PeriodicSlabGauge.gaugeAction a U) v i*
      winding (PeriodicSlabGauge.gaugeAction a U) v j)=halfTrace (winding U v i*winding U v j) := by
  rw [winding_gauge,winding_gauge]
  have h : (a v*winding U v i*(a v)⁻¹)*(a v*winding U v j*(a v)⁻¹)=
      a v*(winding U v i*winding U v j)*(a v)⁻¹ := by group
  rw [h,halfTrace_conjugate]

def flat (U : State) : Prop :=
  ∀ v : SpatialVertex,∀ i j : Fin 3,
    U (v,i)*U (shift v i,j)=U (v,j)*U (shift v j,i)

private theorem slide_four {G : Type*} [Group G]
    (a0 a1 a2 a3 b0 b1 b2 b3 g0 g1 g2 g3 : G)
    (h0 : a0*g1=g0*b0) (h1 : a1*g2=g1*b1)
    (h2 : a2*g3=g2*b2) (h3 : a3*g0=g3*b3) :
    (a0*a1*a2*a3)*g0=g0*(b0*b1*b2*b3) := by
  calc
    _ = a0*(a1*(a2*(a3*g0))) := by group
    _ = a0*(a1*(a2*(g3*b3))) := by rw [h3]
    _ = a0*(a1*((a2*g3)*b3)) := by group
    _ = a0*(a1*((g2*b2)*b3)) := by rw [h2]
    _ = a0*((a1*g2)*(b2*b3)) := by group
    _ = a0*((g1*b1)*(b2*b3)) := by rw [h1]
    _ = (a0*g1)*(b1*b2*b3) := by group
    _ = _ := by rw [h0]; group

theorem flat_row (U : State) (hf : flat U) (v : SpatialVertex) (i j : Fin 3) :
    winding U v i*U (v,j)=U (v,j)*winding U (shift v j) i := by
  have h0 := hf v i j
  have h1 := hf (shift v i) i j
  have h2 := hf (twice v i) i j
  have h3 := hf (thrice v i) i j
  change U (shift v i,i)*U (twice v i,j)=_ at h1
  change U (twice v i,i)*U (thrice v i,j)=_ at h2
  rw [shift_four] at h3
  have hs := slide_four
    (U (v,i)) (U (shift v i,i)) (U (twice v i,i)) (U (thrice v i,i))
    (U (shift v j,i)) (U (shift (shift v i) j,i))
    (U (shift (twice v i) j,i)) (U (shift (thrice v i) j,i))
    (U (v,j)) (U (shift v i,j)) (U (twice v i,j)) (U (thrice v i,j))
    h0 h1 h2 h3
  simpa only [winding,shift_commute v j i,twice_shift,thrice_shift] using hs

theorem flat_commute (U : State) (hf : flat U) (v : SpatialVertex) (i j : Fin 3) :
    winding U v i*winding U v j=winding U v j*winding U v i := by
  have h0 := flat_row U hf v i j
  have h1 := flat_row U hf (shift v j) i j
  have h2 := flat_row U hf (twice v j) i j
  have h3 := flat_row U hf (thrice v j) i j
  change _=U (shift v j,j)*winding U (twice v j) i at h1
  change _=U (twice v j,j)*winding U (thrice v j) i at h2
  rw [shift_four] at h3
  calc
    _ = (((winding U v i*U (v,j))*U (shift v j,j))*U (twice v j,j))*U (thrice v j,j) := by
      unfold winding; group
    _ = (((U (v,j)*winding U (shift v j) i)*U (shift v j,j))*U (twice v j,j))*U (thrice v j,j) := by rw [h0]
    _ = ((U (v,j)*(winding U (shift v j) i*U (shift v j,j)))*U (twice v j,j))*U (thrice v j,j) := by group
    _ = ((U (v,j)*(U (shift v j,j)*winding U (twice v j) i))*U (twice v j,j))*U (thrice v j,j) := by rw [h1]
    _ = ((U (v,j)*U (shift v j,j))*(winding U (twice v j) i*U (twice v j,j)))*U (thrice v j,j) := by group
    _ = ((U (v,j)*U (shift v j,j))*(U (twice v j,j)*winding U (thrice v j) i))*U (thrice v j,j) := by rw [h2]
    _ = (U (v,j)*U (shift v j,j)*U (twice v j,j))*(winding U (thrice v j) i*U (thrice v j,j)) := by group
    _ = (U (v,j)*U (shift v j,j)*U (twice v j,j))*(U (thrice v j,j)*winding U v i) := by rw [h3]
    _ = _ := by unfold winding; group

theorem action_zero_flat (U : State) (hz : PeriodicWilsonSlab.spatialAction U=0) : flat U := by
  have hp (p : SpatialFace) : spatialWord U p=1 := by
    apply (FourCubePinnedCoercivity.defect_zero_iff _).mp
    apply le_antisymm ?_ (FourCubePinnedCoercivity.defect_nonneg _)
    have h := Finset.single_le_sum
      (fun p (_ : p∈Finset.univ) => FourCubePinnedCoercivity.defect_nonneg (spatialWord U p))
      (Finset.mem_univ p)
    change FourCubePinnedCoercivity.defect (spatialWord U p) ≤ PeriodicWilsonSlab.spatialAction U at h
    exact h.trans_eq hz
  have hlt (v : SpatialVertex) (i j : Fin 3) (hij : i < j) :
      U (v,i)*U (shift v i,j)=U (v,j)*U (shift v j,i) := by
    have h := hp ⟨(v,(i,j)),hij⟩
    change U (v,i)*U (shift v i,j)*(U (shift v j,i))⁻¹*(U (v,j))⁻¹=1 at h
    calc
      _ = (U (v,i)*U (shift v i,j)*(U (shift v j,i))⁻¹*(U (v,j))⁻¹)*
          (U (v,j)*U (shift v j,i)) := by group
      _ = _ := by rw [h,one_mul]
  intro v i j
  rcases lt_trichotomy i j with h|h|h
  · exact hlt v i j h
  · subst j; rfl
  · exact (hlt v j i h).symm

theorem flat_joint_lower (U : State) (hf : flat U) (v : SpatialVertex) (i j : Fin 3) :
    (1/2 : ℝ) ≤ SU2HolonomyTraceObstruction.jointSquare (winding U v i) (winding U v j) :=
  SU2HolonomyTraceObstruction.commuting_joint_lower _ _ (flat_commute U hf v i j)

theorem action_zero_joint_lower (U : State) (hz : PeriodicWilsonSlab.spatialAction U=0)
    (v : SpatialVertex) (i j : Fin 3) :
    (1/2 : ℝ) ≤ SU2HolonomyTraceObstruction.jointSquare (winding U v i) (winding U v j) :=
  flat_joint_lower U (action_zero_flat U hz) v i j

end OperatorDerivativeRewrite.Foundation.PeriodicSpatialHolonomy
