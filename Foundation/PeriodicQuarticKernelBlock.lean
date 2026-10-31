import Foundation.PeriodicQuarticGaugeOverlap
/-! A genuine lower Haar-integral block for the actual periodic Wilson kernel
on positive-measure quartic neighborhoods, retaining the constrained root and
all63 relative gauge variables. The spatial and temporal actions are both
controlled. The whole neighborhood also obeys a robust flat-locus separation
bound. Saturation and the native ground-normalized operator bridge remain
separate obligations; no spectral gap or continuum estimate is claimed. -/
noncomputable section
open scoped Quaternion
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
namespace OperatorDerivativeRewrite.Foundation.PeriodicQuarticKernelBlock
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicLoopVariation PeriodicGaugeSaturatedGround SU2TwoAxisStabilizerHaar
open PeriodicQuarticGaugeOverlap FourCubePinnedCoercivity

theorem distance_inverse (A B : SU2) : distance A⁻¹ B⁻¹=distance A B := by
  calc
    _ = distance (A*A⁻¹) (A*B⁻¹) := (left_distance_isometry A⁻¹ B⁻¹ A).symm
    _ = distance 1 (A*B⁻¹) := by rw [mul_inv_cancel]
    _ = distance (1*B) ((A*B⁻¹)*B) := (right_distance_isometry 1 (A*B⁻¹) B).symm
    _ = distance B A := by simp only [one_mul,mul_assoc,inv_mul_cancel,mul_one]
    _ = _ := distance_symm _ _

theorem distance_square_triangle (A B C : SU2) :
    distance A C^2≤2*distance A B^2+2*distance B C^2 := by
  have ht := distance_triangle A B C
  have ha : 0≤distance A C := norm_nonneg _
  have hb : 0≤distance A B := norm_nonneg _
  have hc : 0≤distance B C := norm_nonneg _
  have hs := pow_le_pow_left₀ ha ht 2
  nlinarith [sq_nonneg (distance A B-distance B C)]

theorem defect_distance_bound (A B : SU2) : defect A≤2*defect B+distance A B^2 := by
  have h := distance_square_triangle A B 1
  rw [distance_sq A 1,distance_sq B 1] at h
  simp only [inv_one,mul_one] at h
  linarith

theorem quartic_root_displacement (t r : ℝ) (hr : 0≤r) (c : SU2)
    (hc : c∈nearStabilizer t r) (e : SpatialEdge) :
    distance (c*PeriodicQuarticCurvature.field t e*c⁻¹) (PeriodicQuarticCurvature.field t e)≤r := by
  rcases e with ⟨v,i⟩
  fin_cases i
  · exact hc.1
  · exact hc.2
  · simpa [PeriodicQuarticCurvature.field,distance] using hr


attribute [local irreducible] temporalAction

theorem packet_temporal_triangle (C U V : State) (a : Gauge) (r : ℝ)
    (hU : U∈packet C r) : temporalAction C V a≤192*r^2+2*temporalAction U V a := by
  have hp (e : SpatialEdge) :
      distance (C e) (gaugeAction a V e)^2≤2*r^2+2*distance (U e) (gaugeAction a V e)^2 := by
    have he : distance (C e) (U e)≤r := by rw [distance_symm]; exact hU e
    have hsq := pow_le_pow_left₀ (show 0≤distance (C e) (U e) from norm_nonneg _) he 2
    nlinarith [distance_square_triangle (C e) (U e) (gaugeAction a V e)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hp e)
  have heq : (∑ e : SpatialEdge,(2*r^2+2*distance (U e) (gaugeAction a V e)^2))=
      384*r^2+2*∑ e : SpatialEdge,distance (U e) (gaugeAction a V e)^2 := by
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,edge_count,nsmul_eq_mul,← Finset.mul_sum]
    ring
  rw [heq,PeriodicFlatLocusQuarticObstruction.temporal_distance_identity,
    PeriodicFlatLocusQuarticObstruction.temporal_distance_identity] at hsum
  linarith

theorem packet_flat_separation (U V : State) (a : Gauge) (t r : ℝ) (hr : 0≤r)
    (hU : U∈packet (PeriodicQuarticCurvature.field t) r) (hV : spatialAction V=0)
    (hsmall : r≤|Real.sin (4*t)|/256) :
    Real.sin (4*t)^2≤256*temporalAction U V a := by
  have hcenter := PeriodicFlatLocusQuarticObstruction.flat_separation t V hV a root
  have hperturb := packet_temporal_triangle (PeriodicQuarticCurvature.field t) U V a r hU
  have hscale : r*256≤|Real.sin (4*t)| := (le_div_iff₀ (by norm_num : (0 : ℝ)<256)).mp hsmall
  have hnonneg : (0 : ℝ)≤r*256 := mul_nonneg hr (by norm_num)
  have hsquare : (r*256)^2≤|Real.sin (4*t)|^2 := pow_le_pow_left₀ hnonneg hscale 2
  rw [sq_abs] at hsquare
  nlinarith


theorem spatial_word_close (U C : State) (r : ℝ) (hU : U∈packet C r) (p : SpatialFace) :
    distance (spatialWord U p) (spatialWord C p)≤4*r := by
  let e1 : SpatialEdge := (p.val.1,p.val.2.1)
  let e2 : SpatialEdge := (shift p.val.1 p.val.2.1,p.val.2.2)
  let e3 : SpatialEdge := (shift p.val.1 p.val.2.2,p.val.2.1)
  let e4 : SpatialEdge := (p.val.1,p.val.2.2)
  have h1 := distance_mul (U e1) (U e2) (C e1) (C e2)
  have h2 := distance_mul (U e1*U e2) (U e3)⁻¹ (C e1*C e2) (C e3)⁻¹
  have h3 := distance_mul (U e1*U e2*(U e3)⁻¹) (U e4)⁻¹
    (C e1*C e2*(C e3)⁻¹) (C e4)⁻¹
  rw [distance_inverse] at h2 h3
  change distance (U e1*U e2*(U e3)⁻¹*(U e4)⁻¹) (C e1*C e2*(C e3)⁻¹*(C e4)⁻¹)≤_
  linarith [hU e1,hU e2,hU e3,hU e4]

attribute [local irreducible] spatialAction

theorem spatial_packet_upper (U C : State) (r : ℝ) (hU : U∈packet C r) :
    spatialAction U≤2*spatialAction C+3072*r^2 := by
  have hp (p : SpatialFace) : defect (spatialWord U p)≤2*defect (spatialWord C p)+16*r^2 := by
    have hd := spatial_word_close U C r hU p
    have hsq := pow_le_pow_left₀ (show 0≤distance (spatialWord U p) (spatialWord C p) from norm_nonneg _) hd 2
    nlinarith [defect_distance_bound (spatialWord U p) (spatialWord C p)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hp p)
  have heq : (∑ p : SpatialFace,(2*defect (spatialWord C p)+16*r^2))=
      2*(∑ p : SpatialFace,defect (spatialWord C p))+3072*r^2 := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,face_count,nsmul_eq_mul]
    norm_num
    ring
  have hs (A : State) : (∑ p : SpatialFace,defect (spatialWord A p))=spatialAction A := by
    unfold spatialAction
    rfl
  rw [heq,hs U,hs C] at hsum
  exact hsum

theorem cap_distance (r : ℝ) (hr : 0≤r) (c : SU2) (hc : c∈SU2HaarSmallCap.cap (r/3)) :
    distance c 1≤r := by
  change defect c≤3*(r/3)^2 at hc
  have hsq := distance_sq c 1
  simp only [inv_one,mul_one] at hsq
  have hn : 0≤distance c 1 := norm_nonneg _
  nlinarith [sq_nonneg r]

theorem anchored_close (r : ℝ) (hr : 0≤r) (h : RelField) (hh : h∈relBox (r/3))
    (v : SpatialVertex) : distance (anchored h v) 1≤r := by
  unfold anchored
  split_ifs with hv
  · simpa [distance] using hr
  · exact cap_distance r hr _ (hh ⟨v,hv⟩ (Set.mem_univ _))

theorem assembled_center_distance (C : State) (c : SU2) (h : RelField) (r : ℝ)
    (hh : ∀ v : SpatialVertex,distance (anchored h v) 1≤r) (e : SpatialEdge) :
    distance (gaugeAction (assemble c h) C e) (c*C e*c⁻¹)≤2*r := by
  let M : SU2 := c*C e*c⁻¹
  have hg : gaugeAction (assemble c h) C e=
      anchored h e.1*M*(anchored h (shift e.1 e.2))⁻¹ := by
    unfold gaugeAction assemble M
    group
  have hself : distance M M=0 := by simp [distance]
  have h1 := distance_mul (anchored h e.1) M 1 M
  have h2 := distance_mul (anchored h e.1*M) (anchored h (shift e.1 e.2))⁻¹ M 1
  have hinv : distance (anchored h (shift e.1 e.2))⁻¹ 1=distance (anchored h (shift e.1 e.2)) 1 := by
    simpa only [inv_one] using distance_inverse (anchored h (shift e.1 e.2)) 1
  simp only [one_mul,mul_one,hself,add_zero,hinv] at h1 h2
  rw [hg]
  change distance (anchored h e.1*M*(anchored h (shift e.1 e.2))⁻¹) M≤_
  linarith [hh e.1,hh (shift e.1 e.2)]

theorem packet_aligned_distance (U V : State) (t r : ℝ) (hr : 0≤r)
    (hU : U∈packet (PeriodicQuarticCurvature.field t) r)
    (hV : V∈packet (PeriodicQuarticCurvature.field t) r)
    (c : SU2) (hc : c∈nearStabilizer t r) (h : RelField) (hh : h∈relBox (r/3))
    (e : SpatialEdge) : distance (U e) (gaugeAction (assemble c h) V e)≤5*r := by
  let C := PeriodicQuarticCurvature.field t
  let a := assemble c h
  have hcenter : distance (gaugeAction a C e) (C e)≤3*r := by
    have h1 := assembled_center_distance C c h r (anchored_close r hr h hh) e
    have h2 := quartic_root_displacement t r hr c hc e
    linarith [distance_triangle (gaugeAction a C e) (c*C e*c⁻¹) (C e)]
  have hcov : distance (gaugeAction a C e) (gaugeAction a V e)≤r := by
    rw [framed_distance,distance_symm]
    exact hV e
  have hrcenter : distance (C e) (gaugeAction a C e)≤3*r := by rw [distance_symm]; exact hcenter
  have hu : distance (U e) (C e)≤r := hU e
  change distance (U e) (gaugeAction a V e)≤_
  linarith [distance_triangle (U e) (C e) (gaugeAction a V e),
    distance_triangle (C e) (gaugeAction a C e) (gaugeAction a V e)]

theorem temporal_packet_upper (U V : State) (t r : ℝ) (hr : 0≤r)
    (hU : U∈packet (PeriodicQuarticCurvature.field t) r)
    (hV : V∈packet (PeriodicQuarticCurvature.field t) r)
    (c : SU2) (hc : c∈nearStabilizer t r) (h : RelField) (hh : h∈relBox (r/3)) :
    temporalAction U V (assemble c h)≤2400*r^2 := by
  have hp (e : SpatialEdge) : distance (U e) (gaugeAction (assemble c h) V e)^2≤25*r^2 := by
    have hd := packet_aligned_distance U V t r hr hU hV c hc h hh e
    have hsq := pow_le_pow_left₀ (show 0≤distance (U e) (gaugeAction (assemble c h) V e) from norm_nonneg _) hd 2
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hp e)
  rw [Finset.sum_const,Finset.card_univ,edge_count,nsmul_eq_mul,
    PeriodicFlatLocusQuarticObstruction.temporal_distance_identity] at hsum
  norm_num at hsum
  nlinarith only [hsum]

theorem halfAction_packet_upper (U V : State) (t r : ℝ) (hr : 0≤r)
    (hU : U∈packet (PeriodicQuarticCurvature.field t) r)
    (hV : V∈packet (PeriodicQuarticCurvature.field t) r)
    (c : SU2) (hc : c∈nearStabilizer t r) (h : RelField) (hh : h∈relBox (r/3)) :
    halfAction U V (assemble c h)≤256*Real.sin t^4+5472*r^2 := by
  have h1 := spatial_packet_upper U (PeriodicQuarticCurvature.field t) r hU
  have h2 := spatial_packet_upper V (PeriodicQuarticCurvature.field t) r hV
  rw [PeriodicQuarticCurvature.spatial_action] at h1 h2
  have h3 := temporal_packet_upper U V t r hr hU hV c hc h hh
  unfold halfAction
  linarith


attribute [local irreducible] kernel weight halfAction gaugeHaar boundaryHaar

theorem kernel_packet_lower (β t r : ℝ) (hb : 0≤β) (hr : 0≤r) (ht : Real.sin t≠0)
    (U V : State) (hU : U∈packet (PeriodicQuarticCurvature.field t) r)
    (hV : V∈packet (PeriodicQuarticCurvature.field t) r) :
    law.real (SU2HaarSmallCap.cap (r/(5*|Real.sin t|)))*
      (law.real (SU2HaarSmallCap.cap (r/3)))^63*
        Real.exp (-β*(256*Real.sin t^4+5472*r^2))≤kernel β U V := by
  have hm0 : Measurable (fun a : Gauge => ((U,V),a)) := measurable_const.prodMk measurable_id
  have hm : Measurable (weight β U V) := (weight_joint_measurable β).comp hm0
  have hi := assemble_preserving.integrable_comp_of_integrable (weight_integrable β U V)
  let S : Set (SU2 × RelField) := SU2HaarSmallCap.cap (r/(5*|Real.sin t|)) ×ˢ relBox (r/3)
  have hS : MeasurableSet S := (SU2HaarSmallCap.cap_measurable _).prod (relBox_measurable _)
  have hp (p : SU2 × RelField) (hh : p∈S) :
      Real.exp (-β*(256*Real.sin t^4+5472*r^2))≤weight β U V (assemble p.1 p.2) := by
    have hc : p.1∈nearStabilizer t r := small_cap_stabilizes t r ht hr hh.1
    have ha := halfAction_packet_upper U V t r hr hU hV p.1 hc p.2 hh.2
    unfold weight
    apply Real.exp_le_exp.mpr
    have hprod := mul_le_mul_of_nonneg_left ha hb
    linarith
  have hmass : (law.prod relFieldHaar).real S=
      law.real (SU2HaarSmallCap.cap (r/(5*|Real.sin t|)))*(law.real (SU2HaarSmallCap.cap (r/3)))^63 := by
    change ((law.prod relFieldHaar) (_ ×ˢ _)).toReal=_
    rw [Measure.prod_prod,ENNReal.toReal_mul]
    change _*relFieldHaar.real (relBox (r/3))=_
    rw [relBox_mass]
    rfl
  have hlow := setIntegral_mono_on
    (integrable_const (Real.exp (-β*(256*Real.sin t^4+5472*r^2)))).integrableOn hi.integrableOn hS hp
  rw [setIntegral_const,smul_eq_mul,hmass] at hlow
  have hfull := setIntegral_le_integral (s := S) hi
    (ae_of_all _ (fun p => (Real.exp_pos _).le.trans (weight_bounds β U V (assemble p.1 p.2)).1))
  have he := integral_split (weight β U V) hm
  unfold kernel
  exact hlow.trans (hfull.trans_eq he.symm)

end OperatorDerivativeRewrite.Foundation.PeriodicQuarticKernelBlock
