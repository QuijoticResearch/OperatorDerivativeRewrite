import Foundation.SU2TwoAxisStabilizerHaar
/-! Positive-Haar translated neighborhoods and their actual periodic gauge
overlap. A fixed center is tree-framed without discarding any of the64 gauge
variables. The root and63 relative variables have their actual product Haar
law. Two orthogonal winding holonomies supply the additional root-volume
factor. No weighted stationary law, native slow mode or physical gap is proved. -/
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
namespace OperatorDerivativeRewrite.Foundation.PeriodicQuarticGaugeOverlap
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicLoopVariation SU2TwoAxisStabilizerHaar
open PeriodicGaugeSaturatedGround

def frame (U : State) (v : SpatialVertex) : SU2 :=
  if hv : v=root then 1 else frame U (parent v)*U (parent v,PeriodicGaugeSaturatedGround.axis v)
termination_by depth v
decreasing_by
  have h := parent_depth v hv
  omega

theorem frame_root (U : State) : frame U root=1 := by
  rw [frame]
  simp

theorem frame_tree (U : State) (v : SpatialVertex) (hv : v≠root) :
    gaugeAction (frame U) U (parent v,PeriodicGaugeSaturatedGround.axis v)=1 := by
  have hf : frame U v=frame U (parent v)*U (parent v,PeriodicGaugeSaturatedGround.axis v) := by
    rw [frame]
    simp only [dite_eq_right hv]
  change frame U (parent v)*U (parent v,PeriodicGaugeSaturatedGround.axis v)*
    (frame U (shift (parent v) (PeriodicGaugeSaturatedGround.axis v)))⁻¹=1
  rw [parent_shift v hv,hf]
  exact mul_inv_cancel _

theorem frame_winding (U : State) (i : Fin 3) :
    PeriodicSpatialHolonomy.winding (gaugeAction (frame U) U) root i=
      PeriodicSpatialHolonomy.winding U root i := by
  rw [PeriodicSpatialHolonomy.winding_gauge,frame_root]
  simp

theorem left_distance_isometry (A B C : SU2) : distance (C*A) (C*B)=distance A B := by
  have self (D : SU2) : distance D D=0 := by simp [distance]
  apply le_antisymm
  · simpa only [self,zero_add] using distance_mul C A C B
  · have h := distance_mul C⁻¹ (C*A) C⁻¹ (C*B)
    simpa only [inv_mul_cancel_left,self,zero_add] using h

theorem framed_distance (U C : State) (b : Gauge) (e : SpatialEdge) :
    distance (gaugeAction b U e) (gaugeAction b C e)=distance (U e) (C e) := by
  change distance (b e.1*U e*(b (shift e.1 e.2))⁻¹)
    (b e.1*C e*(b (shift e.1 e.2))⁻¹)=_
  rw [right_distance_isometry,left_distance_isometry]


theorem distance_symm (A B : SU2) : distance A B=distance B A := norm_sub_rev _ _

theorem distance_triangle (A B C : SU2) : distance A C≤distance A B+distance B C := by
  unfold distance
  calc
    ‖lift A-lift C‖=‖(lift A-lift B)+(lift B-lift C)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _

theorem conjugation_distance (A B c : SU2) :
    distance (c*A*c⁻¹) (c*B*c⁻¹)=distance A B := by
  rw [right_distance_isometry,left_distance_isometry]

theorem winding_close (U C : State) (r : ℝ)
    (h : ∀ e : SpatialEdge,distance (U e) (C e)≤r) (v : SpatialVertex) (i : Fin 3) :
    distance (PeriodicSpatialHolonomy.winding U v i) (PeriodicSpatialHolonomy.winding C v i)≤4*r := by
  have h1 := distance_mul (U (v,i)) (U (shift v i,i)) (C (v,i)) (C (shift v i,i))
  have h2 := distance_mul (U (v,i)*U (shift v i,i)) (U (PeriodicSpatialHolonomy.twice v i,i))
    (C (v,i)*C (shift v i,i)) (C (PeriodicSpatialHolonomy.twice v i,i))
  have h3 := distance_mul (U (v,i)*U (shift v i,i)*U (PeriodicSpatialHolonomy.twice v i,i))
    (U (PeriodicSpatialHolonomy.thrice v i,i))
    (C (v,i)*C (shift v i,i)*C (PeriodicSpatialHolonomy.twice v i,i)) (C (PeriodicSpatialHolonomy.thrice v i,i))
  unfold PeriodicSpatialHolonomy.winding
  linarith [h (v,i),h (shift v i,i),h (PeriodicSpatialHolonomy.twice v i,i),h (PeriodicSpatialHolonomy.thrice v i,i)]

theorem overlap_root (U C : State) (a : Gauge) (θ r : ℝ)
    (hU : ∀ e : SpatialEdge,distance (U e) (C e)≤r)
    (hV : ∀ e : SpatialEdge,distance (gaugeAction a U e) (C e)≤r)
    (hC0 : PeriodicSpatialHolonomy.winding C root 0=SU2JointPlaquetteCubic.axis 0 θ)
    (hC1 : PeriodicSpatialHolonomy.winding C root 1=SU2JointPlaquetteCubic.axis 1 θ) :
    a root∈nearStabilizer θ (8*r) := by
  have hturn (i : Fin 3)
      (hCi : PeriodicSpatialHolonomy.winding C root i=SU2JointPlaquetteCubic.axis i θ) :
      turn i θ (a root)≤8*r := by
    let A := SU2JointPlaquetteCubic.axis i θ
    let R := PeriodicSpatialHolonomy.winding U root i
    have hleft : distance (a root*A*(a root)⁻¹) (a root*R*(a root)⁻¹)≤4*r := by
      rw [conjugation_distance,distance_symm]
      simpa only [A,R,hCi] using winding_close U C r hU root i
    have hright : distance (a root*R*(a root)⁻¹) A≤4*r := by
      change distance (a root*PeriodicSpatialHolonomy.winding U root i*(a root)⁻¹) _≤_
      rw [← PeriodicSpatialHolonomy.winding_gauge]
      simpa only [A,hCi] using winding_close (gaugeAction a U) C r hV root i
    have h := distance_triangle (a root*A*(a root)⁻¹) (a root*R*(a root)⁻¹) A
    change distance (a root*A*(a root)⁻¹) A≤8*r
    linarith
  exact ⟨hturn 0 hC0,hturn 1 hC1⟩


theorem quartic_overlap_root (U : State) (a : Gauge) (t r : ℝ)
    (hU : ∀ e : SpatialEdge,distance (U e) (PeriodicQuarticCurvature.field t e)≤r)
    (hV : ∀ e : SpatialEdge,distance (gaugeAction a U e) (PeriodicQuarticCurvature.field t e)≤r) :
    a root∈nearStabilizer (4*t) (8*r) :=
  overlap_root U (PeriodicQuarticCurvature.field t) a (4*t) r hU hV
    (PeriodicFlatLocusQuarticObstruction.winding_field_zero t root)
    (PeriodicFlatLocusQuarticObstruction.winding_field_one t root)


theorem rooted_tree_distance (a : Gauge) (R : ℝ)
    (he : ∀ v : SpatialVertex,v≠root → distance (a v) (a (parent v))≤R) (v : SpatialVertex) :
    distance (a v) (a root)≤(depth v : ℝ)*R := by
  generalize hn : depth v=n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v=root
    · subst v
      have hz : n=0 := by simpa [depth,root] using hn.symm
      subst n
      simp [distance,depth,root]
    · have hd := parent_depth v hv
      have hp : depth (parent v)<n := by omega
      have hprev := ih (depth (parent v)) hp (parent v) rfl
      calc
        _ ≤ distance (a v) (a (parent v))+distance (a (parent v)) (a root) := distance_triangle _ _ _
        _ ≤ R+(depth (parent v) : ℝ)*R := add_le_add (he v hv) hprev
        _ = (n : ℝ)*R := by rw [← hd.trans hn]; push_cast; ring

theorem tree_edge_overlap (U C : State) (a : Gauge) (r : ℝ)
    (hU : ∀ e : SpatialEdge,distance (U e) (C e)≤r)
    (hV : ∀ e : SpatialEdge,distance (gaugeAction a U e) (C e)≤r)
    (hC : ∀ v : SpatialVertex,v≠root → C (parent v,PeriodicGaugeSaturatedGround.axis v)=1)
    (v : SpatialVertex) (hv : v≠root) : distance (a v) (a (parent v))≤2*r := by
  let e : SpatialEdge := (parent v,PeriodicGaugeSaturatedGround.axis v)
  have hu : distance (U e) 1≤r := by simpa only [e,hC v hv] using hU e
  have hw : distance (gaugeAction a U e) 1≤r := by simpa only [e,hC v hv] using hV e
  have hg : gaugeAction a U e=a (parent v)*U e*(a v)⁻¹ := by
    change a (parent v)*U e*(a (shift (parent v) (PeriodicGaugeSaturatedGround.axis v)))⁻¹=_
    rw [parent_shift v hv]
  have hfirst : distance (a (parent v)) (a (parent v)*U e)≤r := by
    have hh := left_distance_isometry 1 (U e) (a (parent v))
    simp only [mul_one] at hh
    rw [hh,distance_symm]
    exact hu
  have hsecond : distance (a (parent v)*U e) (a v)≤r := by
    have hh := right_distance_isometry (a (parent v)*U e) (a v) (a v)⁻¹
    rw [mul_inv_cancel,← hg] at hh
    rw [← hh]
    exact hw
  rw [distance_symm]
  linarith [distance_triangle (a (parent v)) (a (parent v)*U e) (a v)]

theorem tree_relative_cap (U C : State) (a : Gauge) (r : ℝ) (hr : 0≤r)
    (hU : ∀ e : SpatialEdge,distance (U e) (C e)≤r)
    (hV : ∀ e : SpatialEdge,distance (gaugeAction a U e) (C e)≤r)
    (hC : ∀ v : SpatialVertex,v≠root → C (parent v,PeriodicGaugeSaturatedGround.axis v)=1)
    (v : SpatialVertex) : a v*(a root)⁻¹∈SU2HaarSmallCap.cap (8*r) := by
  have h := rooted_tree_distance a (2*r) (tree_edge_overlap U C a r hU hV hC) v
  have hd : (depth v : ℝ)≤9 := by exact_mod_cast depth_le v
  have hh : distance (a v) (a root)≤18*r := by
    have hp := mul_le_mul_of_nonneg_right hd (show 0≤2*r by positivity)
    nlinarith
  have hsq := pow_le_pow_left₀ (show 0≤distance (a v) (a root) from norm_nonneg _) hh 2
  rw [distance_sq] at hsq
  change FourCubePinnedCoercivity.defect (a v*(a root)⁻¹)≤3*(8*r)^2
  nlinarith [sq_nonneg r]

def twist (b a : Gauge) (v : SpatialVertex) : SU2 := b v*a v*(b v)⁻¹

theorem twist_action (b a : Gauge) (U : State) :
    gaugeAction (twist b a) (gaugeAction b U)=gaugeAction b (gaugeAction a U) := by
  funext e
  unfold gaugeAction twist
  group

theorem framed_relative_cap (U C : State) (a : Gauge) (r : ℝ) (hr : 0≤r)
    (hU : ∀ e : SpatialEdge,distance (U e) (C e)≤r)
    (hV : ∀ e : SpatialEdge,distance (gaugeAction a U e) (C e)≤r)
    (v : SpatialVertex) :
    twist (frame C) a v*(twist (frame C) a root)⁻¹∈SU2HaarSmallCap.cap (8*r) := by
  apply tree_relative_cap (gaugeAction (frame C) U) (gaugeAction (frame C) C) _ r hr
  · intro e
    rw [framed_distance]
    exact hU e
  · intro e
    rw [twist_action,framed_distance]
    exact hV e
  · exact frame_tree C


theorem twist_preserving (b : Gauge) : MeasurePreserving (twist b) gaugeHaar gaugeHaar := by
  unfold gaugeHaar twist
  exact measurePreserving_pi (fun _ => law) (fun _ => law)
    (fun v : SpatialVertex => (measurePreserving_mul_right law (b v)⁻¹).comp
      (measurePreserving_mul_left law (b v)))

def coordinates (C : State) (a : Gauge) : SU2 × RelField :=
  (a root,relField (twist (frame C) a))

theorem coordinates_preserving (C : State) :
    MeasurePreserving (coordinates C) gaugeHaar (law.prod relFieldHaar) := by
  have h := joint_preserving.comp (twist_preserving (frame C))
  convert h using 1
  funext a
  apply Prod.ext
  · simp [coordinates,twist,frame_root]
  · rfl

def jointEvent (C : State) (θ r : ℝ) : Set Gauge :=
  coordinates C ⁻¹' (nearStabilizer θ (8*r) ×ˢ relBox (8*r))

theorem jointEvent_mass (C : State) (θ r : ℝ) :
    gaugeHaar.real (jointEvent C θ r)=
      law.real (nearStabilizer θ (8*r))*(law.real (SU2HaarSmallCap.cap (8*r)))^63 := by
  have hS := (nearStabilizer_measurable θ (8*r)).prod (relBox_measurable (8*r))
  change (gaugeHaar (coordinates C ⁻¹' _)).toReal=_
  rw [(coordinates_preserving C).measure_preimage hS.nullMeasurableSet,
    Measure.prod_prod,ENNReal.toReal_mul]
  change _*relFieldHaar.real (relBox (8*r))=_
  rw [relBox_mass]
  rfl

def packet (C : State) (r : ℝ) : Set State := {U | ∀ e : SpatialEdge,distance (U e) (C e)≤r}

theorem packet_measurable (C : State) (r : ℝ) : MeasurableSet (packet C r) := by
  have hl : Measurable lift := (continuous_subtype_val.comp homeomorph.symm.continuous).measurable
  have hd (e : SpatialEdge) : Measurable (fun U : State => distance (U e) (C e)) :=
    ((hl.comp (measurable_pi_apply e)).sub measurable_const).norm
  have he : packet C r=⋂ e : SpatialEdge,{U : State | distance (U e) (C e)≤r} := by
    ext U
    simp [packet]
  rw [he]
  exact MeasurableSet.iInter (fun e => measurableSet_le (hd e) measurable_const)

-- Prevent elaboration from expanding the192-coordinate action in measurability goals.
attribute [local irreducible] gaugeAction

theorem overlap_measurable (C U : State) (r : ℝ) :
    MeasurableSet {a : Gauge | gaugeAction a U∈packet C r} := by
  have hc : Measurable (fun a : Gauge => (U,a)) := measurable_const.prodMk measurable_id
  have hm : Measurable (fun a : Gauge => gaugeAction a U) := action_joint_measurable.comp hc
  exact (packet_measurable C r).preimage hm

theorem overlap_subset (U C : State) (θ r : ℝ) (hr : 0≤r) (hU : U∈packet C r)
    (hC0 : PeriodicSpatialHolonomy.winding C root 0=SU2JointPlaquetteCubic.axis 0 θ)
    (hC1 : PeriodicSpatialHolonomy.winding C root 1=SU2JointPlaquetteCubic.axis 1 θ) :
    {a : Gauge | gaugeAction a U∈packet C r} ⊆ jointEvent C θ r := by
  intro a ha
  change a root∈nearStabilizer θ (8*r) ∧ relField (twist (frame C) a)∈relBox (8*r)
  constructor
  · exact overlap_root U C a θ r hU ha hC0 hC1
  · intro v _
    exact framed_relative_cap U C a r hr hU ha v.val

theorem overlap_mass_bound (U C : State) (θ r : ℝ) (hr : 0≤r) (hU : U∈packet C r)
    (hC0 : PeriodicSpatialHolonomy.winding C root 0=SU2JointPlaquetteCubic.axis 0 θ)
    (hC1 : PeriodicSpatialHolonomy.winding C root 1=SU2JointPlaquetteCubic.axis 1 θ) :
    gaugeHaar.real {a : Gauge | gaugeAction a U∈packet C r}≤
      law.real (nearStabilizer θ (8*r))*(law.real (SU2HaarSmallCap.cap (8*r)))^63 := by
  rw [← jointEvent_mass C θ r]
  exact measureReal_mono (overlap_subset U C θ r hr hU hC0 hC1) (measure_ne_top _ _)


theorem overlap_polynomial_bound (U C : State) (θ r : ℝ)
    (hr : 0<r) (hr1 : 8*r≤1) (hsmall : 8*r≤|Real.sin θ|) (hθ : Real.sin θ≠0)
    (hU : U∈packet C r)
    (hC0 : PeriodicSpatialHolonomy.winding C root 0=SU2JointPlaquetteCubic.axis 0 θ)
    (hC1 : PeriodicSpatialHolonomy.winding C root 1=SU2JointPlaquetteCubic.axis 1 θ) :
    gaugeHaar.real {a : Gauge | gaugeAction a U∈packet C r}≤
      upperConstant*(8*r/|Real.sin θ|)^3*
        ((Real.exp 3*SU2HaarLaplaceUpper.upperConstant 1)*(8*r)^3)^63 := by
  have hroot := (stabilizer_mass_cubic θ (8*r) hθ (by positivity) hsmall).2
  have hcap := PeriodicGroundHaarScale.cap_polynomial_upper (8*r) (by positivity) hr1
  have hpow := pow_le_pow_left₀ (show 0≤law.real (SU2HaarSmallCap.cap (8*r)) from measureReal_nonneg) hcap 63
  have hs : 0 < |Real.sin θ| := abs_pos.mpr hθ
  have hu := upperConstant_pos
  exact (overlap_mass_bound U C θ r hr.le hU hC0 hC1).trans
    ((mul_le_mul_of_nonneg_right hroot (pow_nonneg measureReal_nonneg 63)).trans
      (mul_le_mul_of_nonneg_left hpow (by positivity)))

theorem quartic_overlap_mass_bound (U : State) (t r : ℝ) (hr : 0≤r)
    (hU : U∈packet (PeriodicQuarticCurvature.field t) r) :
    gaugeHaar.real {a : Gauge | gaugeAction a U∈packet (PeriodicQuarticCurvature.field t) r}≤
      law.real (nearStabilizer (4*t) (8*r))*(law.real (SU2HaarSmallCap.cap (8*r)))^63 :=
  overlap_mass_bound U (PeriodicQuarticCurvature.field t) (4*t) r hr hU
    (PeriodicFlatLocusQuarticObstruction.winding_field_zero t root)
    (PeriodicFlatLocusQuarticObstruction.winding_field_one t root)


def translated (C U : State) (e : SpatialEdge) : SU2 := U e*C e

theorem translated_preserving (C : State) :
    MeasurePreserving (translated C) boundaryHaar boundaryHaar := by
  unfold boundaryHaar translated
  exact measurePreserving_pi (fun _ => law) (fun _ => law)
    (fun e : SpatialEdge => measurePreserving_mul_right law (C e))

theorem translated_box_subset (C : State) (r : ℝ) (hr : 0≤r) :
    PeriodicPolynomialGround.boundaryBox (r/3) ⊆ translated C ⁻¹' packet C r := by
  intro U hU e
  have hc := hU e (Set.mem_univ e)
  change FourCubePinnedCoercivity.defect (U e)≤3*(r/3)^2 at hc
  have he : distance (translated C U e) (C e)=distance (U e) 1 := by
    have h := right_distance_isometry (U e) 1 (C e)
    simpa only [one_mul,translated] using h
  rw [he]
  have hsq := distance_sq (U e) 1
  simp only [inv_one,mul_one] at hsq
  have hn : 0≤distance (U e) 1 := norm_nonneg _
  nlinarith [sq_nonneg r]

theorem packet_mass_lower (C : State) (r : ℝ) (hr : 0≤r) :
    (law.real (SU2HaarSmallCap.cap (r/3)))^192≤boundaryHaar.real (packet C r) := by
  rw [← PeriodicPolynomialGround.boundary_mass]
  have h := measureReal_mono (translated_box_subset C r hr) (measure_ne_top boundaryHaar _)
  have he := congrArg ENNReal.toReal
    ((translated_preserving C).measure_preimage (packet_measurable C r).nullMeasurableSet)
  exact h.trans_eq he

theorem packet_mass_pos (C : State) (r : ℝ) (hr : 0<r) (hsmall : r≤3) :
    0<boundaryHaar.real (packet C r) := by
  have hd : 0<r/3 := by positivity
  have hd1 : r/3≤1 := by linarith
  have hl := SU2HaarSmallCap.mass_lower (r/3) hd.le hd1
  have hpos : 0<law.real (SU2HaarSmallCap.cap (r/3)) := lt_of_lt_of_le (by positivity) hl
  exact (pow_pos hpos 192).trans_le (packet_mass_lower C r hr.le)

end OperatorDerivativeRewrite.Foundation.PeriodicQuarticGaugeOverlap
