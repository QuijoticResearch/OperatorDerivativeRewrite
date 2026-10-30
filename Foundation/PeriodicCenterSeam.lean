import Foundation.PeriodicHolonomyMass
import Foundation.SU2StrongCouplingCovariance

/-! A genuine central seam symmetry of the actual periodic spatial transfer.
This is not an independent endpoint gauge transformation. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicCenterSeam
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab

private theorem center_value :
    (SU2StapleExtremes.minusOne : SU2TraceHessianModel.M2)= -1 := by
  change QuaternionSU2Representation.repr (-1)= -1
  simpa using repr_real (-1)

theorem center_commute (A : SU2) : SU2StapleExtremes.minusOne*A=A*SU2StapleExtremes.minusOne := by
  apply Subtype.ext
  change (SU2StapleExtremes.minusOne : SU2TraceHessianModel.M2)*(A : SU2TraceHessianModel.M2)=
    (A : SU2TraceHessianModel.M2)*(SU2StapleExtremes.minusOne : SU2TraceHessianModel.M2)
  rw [center_value]
  simp

theorem center_square : SU2StapleExtremes.minusOne*SU2StapleExtremes.minusOne=(1 : SU2) := by
  apply Subtype.ext
  change (SU2StapleExtremes.minusOne : SU2TraceHessianModel.M2)*
    (SU2StapleExtremes.minusOne : SU2TraceHessianModel.M2)=1
  rw [center_value]
  simp

def seam (i : Fin 3) (e : SpatialEdge) : SU2 :=
  if e.2=i ∧ e.1 i=3 then SU2StapleExtremes.minusOne else 1

def flip (i : Fin 3) (U : State) : State := seam i*U

theorem seam_commute (i : Fin 3) (e : SpatialEdge) (A : SU2) : seam i e*A=A*seam i e := by
  unfold seam
  split_ifs
  · exact center_commute A
  · simp

theorem seam_square (i : Fin 3) (e : SpatialEdge) : seam i e*seam i e=1 := by
  unfold seam
  split_ifs
  · exact center_square
  · simp

theorem flip_involutive (i : Fin 3) : Function.Involutive (flip i) := by
  intro U
  funext e
  change seam i e*(seam i e*U e)=U e
  rw [← mul_assoc,seam_square,one_mul]

private theorem twist_first (c a b d e : SU2) (hc : ∀ X : SU2,c*X=X*c) :
    (c*a)*b*(c*d)⁻¹*e⁻¹=a*b*d⁻¹*e⁻¹ := by
  calc
    _ = (c*(a*b*d⁻¹))*c⁻¹*e⁻¹ := by group
    _ = ((a*b*d⁻¹)*c)*c⁻¹*e⁻¹ := by rw [hc]
    _ = _ := by group

private theorem twist_second (c a b d e : SU2) (hc : ∀ X : SU2,c*X=X*c) :
    a*(c*b)*d⁻¹*(c*e)⁻¹=a*b*d⁻¹*e⁻¹ := by
  calc
    _ = a*(c*(b*d⁻¹*e⁻¹))*c⁻¹ := by group
    _ = a*((b*d⁻¹*e⁻¹)*c)*c⁻¹ := by rw [hc]
    _ = _ := by group

theorem spatial_word (i : Fin 3) (U : State) (p : SpatialFace) :
    PeriodicTemporalSlab.spatialWord (flip i U) p=PeriodicTemporalSlab.spatialWord U p := by
  rcases p with ⟨⟨v,a,b⟩,hab⟩
  have hne : a≠b := ne_of_lt hab
  by_cases hai : a=i
  · subst a
    have hbi : b≠i := Ne.symm hne
    by_cases hv : v i=3
    · simpa [PeriodicTemporalSlab.spatialWord,flip,seam,shift,hbi,hne,hv] using
        twist_first SU2StapleExtremes.minusOne
          (U (v,i)) (U (shift v i,b)) (U (shift v b,i)) (U (v,b)) center_commute
    · simp [PeriodicTemporalSlab.spatialWord,flip,seam,shift,hbi,hne,hv]
  · by_cases hbi : b=i
    · subst b
      by_cases hv : v i=3
      · simpa [PeriodicTemporalSlab.spatialWord,flip,seam,shift,hai,Ne.symm hai,hv] using
          twist_second SU2StapleExtremes.minusOne
            (U (v,a)) (U (shift v a,i)) (U (shift v i,a)) (U (v,i)) center_commute
      · simp [PeriodicTemporalSlab.spatialWord,flip,seam,shift,hai,Ne.symm hai,hv]
    · simp [PeriodicTemporalSlab.spatialWord,flip,seam,hai,hbi]

theorem spatial_action (i : Fin 3) (U : State) : spatialAction (flip i U)=spatialAction U := by
  unfold spatialAction
  simp_rw [spatial_word]

theorem temporal_word (i : Fin 3) (U V : State) (g : Gauge) (e : SpatialEdge) :
    temporalWord (flip i U) (flip i V) g e=temporalWord U V g e := by
  exact twist_first (seam i e) (U e) (g (shift e.1 e.2)) (V e) (g e.1) (seam_commute i e)

theorem half_action (i : Fin 3) (U V : State) (g : Gauge) :
    halfAction (flip i U) (flip i V) g=halfAction U V g := by
  unfold halfAction temporalAction
  rw [spatial_action,spatial_action]
  simp_rw [temporal_word]

theorem kernel_simultaneous (beta : ℝ) (i : Fin 3) (U V : State) :
    kernel beta (flip i U) (flip i V)=kernel beta U V := by
  unfold kernel weight
  simp_rw [half_action]

theorem flip_measurable (i : Fin 3) : Measurable (flip i) := measurable_const_mul _

theorem flip_haar_preserving (i : Fin 3) : MeasurePreserving (flip i) boundaryHaar boundaryHaar := by
  unfold boundaryHaar
  exact measurePreserving_pi (fun _ => law) (fun _ => law)
    (fun e => measurePreserving_mul_left law (seam i e))

end OperatorDerivativeRewrite.Foundation.PeriodicCenterSeam
