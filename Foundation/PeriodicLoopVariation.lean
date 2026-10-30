import Foundation.PeriodicTemporalConcentration
import Foundation.PeriodicSpatialHolonomy
/-! Gauge-invariant loop variation controlled by the actual temporal plaquette action.
The constants are finite-volume bounds, with no continuum scaling assertion. -/
noncomputable section
open scoped Quaternion
namespace OperatorDerivativeRewrite.Foundation.PeriodicLoopVariation
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicSpatialHolonomy
open FourCubePinnedCoercivity

def lift (A : SU2) : ℍ := equiv.symm A

def distance (A B : SU2) : ℝ := ‖lift A-lift B‖

private theorem lift_mul (A B : SU2) : lift (A*B)=lift A*lift B := by
  exact congrArg (fun u : QuaternionAngularHaar.Group => (u : ℍ)) (equiv.symm.map_mul A B)

private theorem lift_norm (A : SU2) : ‖lift A‖=1 := CStarRing.norm_coe_unitary _

theorem distance_sq (A B : SU2) : distance A B^2=2*defect (A*B⁻¹) := by
  obtain ⟨a,rfl⟩ := hom_surjective A
  obtain ⟨b,rfl⟩ := hom_surjective B
  have hl (c : QuaternionAngularHaar.Group) : lift (hom c)=(c : ℍ) := by
    change ((equiv.symm (equiv c) : QuaternionAngularHaar.Group) : ℍ)=_
    rw [equiv.symm_apply_apply]
  have hn (c : QuaternionAngularHaar.Group) : Quaternion.normSq (c : ℍ)=1 := by
    rw [Quaternion.normSq_eq_norm_mul_self,CStarRing.norm_coe_unitary,one_mul]
  have he : ((a*b⁻¹ : QuaternionAngularHaar.Group) : ℍ)=(a : ℍ)*star (b : ℍ) := rfl
  simp only [distance,hl,pow_two]
  rw [← Quaternion.normSq_eq_norm_mul_self]
  rw [← hom.map_inv,← hom.map_mul,defect,halfTrace_map]
  change Quaternion.normSq ((a : ℍ)-(b : ℍ))=2*(1-((a*b⁻¹ : QuaternionAngularHaar.Group) : ℍ).re)
  rw [he]
  have ha := hn a
  have hb := hn b
  norm_num [Quaternion.normSq_def',Quaternion.re_mul] at ha hb ⊢
  nlinarith

theorem trace_distance (A B : SU2) : (halfTrace A-halfTrace B)^2 ≤ distance A B^2 := by
  obtain ⟨a,rfl⟩ := hom_surjective A
  obtain ⟨b,rfl⟩ := hom_surjective B
  have hl (c : QuaternionAngularHaar.Group) : lift (hom c)=(c : ℍ) := by
    change ((equiv.symm (equiv c) : QuaternionAngularHaar.Group) : ℍ)=_
    rw [equiv.symm_apply_apply]
  simp only [distance,hl,pow_two]
  rw [← Quaternion.normSq_eq_norm_mul_self]
  simp only [halfTrace_map,QuaternionAngularHaar.realCoordinate,Quaternion.normSq_def',
    Quaternion.re_sub,Quaternion.imI_sub,Quaternion.imJ_sub,Quaternion.imK_sub]
  nlinarith [sq_nonneg ((a : ℍ).imI-(b : ℍ).imI),
    sq_nonneg ((a : ℍ).imJ-(b : ℍ).imJ),sq_nonneg ((a : ℍ).imK-(b : ℍ).imK)]

theorem distance_mul (A B C D : SU2) : distance (A*B) (C*D) ≤ distance A C+distance B D := by
  have he : lift A*lift B-lift C*lift D=(lift A-lift C)*lift B+lift C*(lift B-lift D) := by noncomm_ring
  unfold distance
  rw [lift_mul,lift_mul,he]
  calc
    _ ≤ ‖(lift A-lift C)*lift B‖+‖lift C*(lift B-lift D)‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul,norm_mul,lift_norm,lift_norm,mul_one,one_mul]


theorem edge_distance (U V : State) (a : Gauge) (e : SpatialEdge) :
    distance (U e) (PeriodicSlabGauge.gaugeAction a V e) ≤ Real.sqrt (2*PeriodicWilsonSlab.temporalAction U V a) := by
  apply Real.le_sqrt_of_sq_le
  rw [distance_sq,← PeriodicTemporalConcentration.temporal_word_alignment]
  have h := Finset.single_le_sum (fun e (_ : e∈Finset.univ) =>
    defect_nonneg (temporalWord U V a e)) (Finset.mem_univ e)
  change defect (temporalWord U V a e) ≤ PeriodicWilsonSlab.temporalAction U V a at h
  linarith

theorem winding_distance (U V : State) (a : Gauge) (v : SpatialVertex) (i : Fin 3) :
    distance (winding U v i) (winding (PeriodicSlabGauge.gaugeAction a V) v i) ≤
      4*Real.sqrt (2*PeriodicWilsonSlab.temporalAction U V a) := by
  have h1 := distance_mul (U (v,i)) (U (shift v i,i))
    (PeriodicSlabGauge.gaugeAction a V (v,i)) (PeriodicSlabGauge.gaugeAction a V (shift v i,i))
  have h2 := distance_mul (U (v,i)*U (shift v i,i)) (U (twice v i,i))
    (PeriodicSlabGauge.gaugeAction a V (v,i)*PeriodicSlabGauge.gaugeAction a V (shift v i,i))
    (PeriodicSlabGauge.gaugeAction a V (twice v i,i))
  have h3 := distance_mul (U (v,i)*U (shift v i,i)*U (twice v i,i)) (U (thrice v i,i))
    (PeriodicSlabGauge.gaugeAction a V (v,i)*PeriodicSlabGauge.gaugeAction a V (shift v i,i)*
      PeriodicSlabGauge.gaugeAction a V (twice v i,i)) (PeriodicSlabGauge.gaugeAction a V (thrice v i,i))
  unfold winding
  linarith [edge_distance U V a (v,i),edge_distance U V a (shift v i,i),
    edge_distance U V a (twice v i,i),edge_distance U V a (thrice v i,i)]

theorem winding_trace_change (U V : State) (a : Gauge) (v : SpatialVertex) (i : Fin 3) :
    (halfTrace (winding U v i)-halfTrace (winding V v i))^2 ≤
      32*PeriodicWilsonSlab.temporalAction U V a := by
  rw [← trace_gauge a V v i]
  have ht := trace_distance (winding U v i) (winding (PeriodicSlabGauge.gaugeAction a V) v i)
  have hd := winding_distance U V a v i
  have hs := Real.sq_sqrt (by linarith [(PeriodicWilsonSlab.temporal_action_bounds U V a).1] :
    0 ≤ 2*PeriodicWilsonSlab.temporalAction U V a)
  have hsq := mul_self_le_mul_self (norm_nonneg (lift (winding U v i)-
    lift (winding (PeriodicSlabGauge.gaugeAction a V) v i))) hd
  change distance (winding U v i) (winding (PeriodicSlabGauge.gaugeAction a V) v i)*
    distance (winding U v i) (winding (PeriodicSlabGauge.gaugeAction a V) v i) ≤ _ at hsq
  nlinarith

theorem product_trace_change (U V : State) (a : Gauge) (v : SpatialVertex) (i j : Fin 3) :
    (halfTrace (winding U v i*winding U v j)-halfTrace (winding V v i*winding V v j))^2 ≤
      128*PeriodicWilsonSlab.temporalAction U V a := by
  rw [← product_trace_gauge a V v i j]
  have ht := trace_distance (winding U v i*winding U v j)
    (winding (PeriodicSlabGauge.gaugeAction a V) v i*winding (PeriodicSlabGauge.gaugeAction a V) v j)
  have hd := distance_mul (winding U v i) (winding U v j)
    (winding (PeriodicSlabGauge.gaugeAction a V) v i) (winding (PeriodicSlabGauge.gaugeAction a V) v j)
  have hd8 : distance (winding U v i*winding U v j)
      (winding (PeriodicSlabGauge.gaugeAction a V) v i*winding (PeriodicSlabGauge.gaugeAction a V) v j) ≤
      8*Real.sqrt (2*PeriodicWilsonSlab.temporalAction U V a) := by
    linarith [winding_distance U V a v i,winding_distance U V a v j]
  have hs := Real.sq_sqrt (by linarith [(PeriodicWilsonSlab.temporal_action_bounds U V a).1] :
    0 ≤ 2*PeriodicWilsonSlab.temporalAction U V a)
  have hsq := mul_self_le_mul_self (norm_nonneg (lift (winding U v i*winding U v j)-
    lift (winding (PeriodicSlabGauge.gaugeAction a V) v i*winding (PeriodicSlabGauge.gaugeAction a V) v j))) hd8
  change distance (winding U v i*winding U v j) _*distance (winding U v i*winding U v j) _ ≤ _ at hsq
  nlinarith
end OperatorDerivativeRewrite.Foundation.PeriodicLoopVariation
