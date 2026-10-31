import Foundation.PeriodicGaugeSaturatedGround
import Foundation.PeriodicFlatLocusQuarticObstruction
/-! Actual normalized SU(2) Haar bounds for simultaneous approximate
stabilizers of two orthogonal holonomies. The scale is epsilon / abs(sin theta).
These statements concern the unweighted Haar root law, not a ground-weighted
conditional law or a native transfer-operator quasimode. -/
noncomputable section
open scoped Quaternion Topology
open MeasureTheory ProbabilityTheory Set
open OperatorDerivativeRewrite.Foundation
namespace OperatorDerivativeRewrite.Foundation.SU2TwoAxisStabilizerHaar
open QuaternionSU2Representation SU2JointPlaquetteCubic PeriodicLoopVariation
open FourCubePinnedCoercivity SU2HaarSmallCap
attribute [local irreducible] defect

private theorem distance_self (A : SU2) : distance A A=0 := by simp [distance]

theorem right_distance_isometry (A B C : SU2) : distance (A*C) (B*C)=distance A B := by
  apply le_antisymm
  · simpa only [distance_self,add_zero] using distance_mul A C B C
  · have h := distance_mul (A*C) C⁻¹ (B*C) C⁻¹
    simpa only [mul_inv_cancel_right,distance_self,add_zero] using h

def turn (i : Fin 3) (θ : ℝ) (c : SU2) : ℝ := distance (c*axis i θ*c⁻¹) (axis i θ)

theorem turn_commutator (i : Fin 3) (θ : ℝ) (c : SU2) :
    turn i θ c=distance (c*axis i θ) (axis i θ*c) := by
  unfold turn
  calc
    _ = distance ((c*axis i θ*c⁻¹)*c) (axis i θ*c) := (right_distance_isometry _ _ c).symm
    _ = _ := by congr 1; group

private theorem lift_mul (A B : SU2) : lift (A*B)=lift A*lift B :=
  congrArg (fun u : QuaternionAngularHaar.Group => (u : ℍ)) (equiv.symm.map_mul A B)

private theorem lift_hom (c : QuaternionAngularHaar.Group) : lift (hom c)=(c : ℍ) := by
  change ((equiv.symm (equiv c) : QuaternionAngularHaar.Group) : ℍ)=_
  rw [equiv.symm_apply_apply]

private theorem lift_axis (i : Fin 3) (θ : ℝ) : lift (axis i θ)=axisRaw i θ := by
  unfold axis
  exact lift_hom _

theorem turn_zero_square (θ : ℝ) (c : SU2) :
    turn 0 θ c^2=4*Real.sin θ^2*((lift c).imJ^2+(lift c).imK^2) := by
  rw [turn_commutator]
  unfold distance
  rw [pow_two,← Quaternion.normSq_eq_norm_mul_self,lift_mul,lift_mul,lift_axis]
  norm_num [axisRaw,Quaternion.normSq_def',Quaternion.re_sub,Quaternion.imI_sub,
    Quaternion.imJ_sub,Quaternion.imK_sub,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  ring

theorem turn_one_square (θ : ℝ) (c : SU2) :
    turn 1 θ c^2=4*Real.sin θ^2*((lift c).imI^2+(lift c).imK^2) := by
  rw [turn_commutator]
  unfold distance
  rw [pow_two,← Quaternion.normSq_eq_norm_mul_self,lift_mul,lift_mul,lift_axis]
  norm_num [axisRaw,Quaternion.normSq_def',Quaternion.re_sub,Quaternion.imI_sub,
    Quaternion.imJ_sub,Quaternion.imK_sub,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul]
  ring

def rootImagSq (c : SU2) : ℝ := (lift c).imI^2+(lift c).imJ^2+(lift c).imK^2

theorem rootImagSq_nonneg (c : SU2) : 0≤rootImagSq c := by unfold rootImagSq; positivity

theorem rootImagSq_trace (c : SU2) : rootImagSq c=1-halfTrace c^2 := by
  have hr : (lift c).re=halfTrace c := by
    obtain ⟨u,rfl⟩ := hom_surjective c
    rw [lift_hom,halfTrace_map]
    rfl
  have hn : Quaternion.normSq (lift c)=1 := by
    rw [Quaternion.normSq_eq_norm_mul_self]
    have h : ‖lift c‖=1 := CStarRing.norm_coe_unitary _
    rw [h,one_mul]
  unfold rootImagSq
  norm_num [Quaternion.normSq_def'] at hn
  rw [← hr]
  nlinarith

theorem two_axis_control (θ : ℝ) (c : SU2) :
    4*Real.sin θ^2*rootImagSq c≤turn 0 θ c^2+turn 1 θ c^2 := by
  rw [turn_zero_square,turn_one_square]
  unfold rootImagSq
  nlinarith [mul_nonneg (sq_nonneg (Real.sin θ)) (sq_nonneg (lift c).imK)]

theorem turn_zero_upper (θ : ℝ) (c : SU2) : turn 0 θ c^2≤4*Real.sin θ^2*rootImagSq c := by
  rw [turn_zero_square]
  unfold rootImagSq
  nlinarith [mul_nonneg (sq_nonneg (Real.sin θ)) (sq_nonneg (lift c).imI)]

theorem turn_one_upper (θ : ℝ) (c : SU2) : turn 1 θ c^2≤4*Real.sin θ^2*rootImagSq c := by
  rw [turn_one_square]
  unfold rootImagSq
  nlinarith [mul_nonneg (sq_nonneg (Real.sin θ)) (sq_nonneg (lift c).imJ)]


theorem turn_nonneg (i : Fin 3) (θ : ℝ) (c : SU2) : 0≤turn i θ c := norm_nonneg _

theorem turn_measurable (i : Fin 3) (θ : ℝ) : Measurable (turn i θ) := by
  have hl : Continuous lift := continuous_subtype_val.comp homeomorph.symm.continuous
  change Measurable (fun c : SU2 => ‖lift (c*axis i θ*c⁻¹)-lift (axis i θ)‖)
  exact ((hl.comp ((continuous_id.mul continuous_const).mul continuous_inv)).sub continuous_const).norm.measurable

def nearStabilizer (θ ε : ℝ) : Set SU2 := {c | turn 0 θ c≤ε ∧ turn 1 θ c≤ε}

theorem nearStabilizer_measurable (θ ε : ℝ) : MeasurableSet (nearStabilizer θ ε) :=
  (measurableSet_le (turn_measurable 0 θ) measurable_const).inter
    (measurableSet_le (turn_measurable 1 θ) measurable_const)

theorem rootImagSq_cap (c : SU2) (δ : ℝ) (hc : c∈cap δ) : rootImagSq c≤6*δ^2 := by
  have hq := abs_le.mp (halfTrace_bound c)
  change defect c≤3*δ^2 at hc
  unfold defect at hc
  rw [rootImagSq_trace]
  have h := mul_nonneg (show 0≤1-halfTrace c by linarith) (show 0≤1-halfTrace c by linarith)
  nlinarith

theorem rootImagSq_cover (c : SU2) (δ : ℝ) (hc : rootImagSq c≤δ^2) :
    c∈cap δ ∪ ((fun x : SU2 => SU2StapleExtremes.minusOne*x) ⁻¹' cap δ) := by
  have hq := abs_le.mp (halfTrace_bound c)
  rw [rootImagSq_trace] at hc
  by_cases hs : 0≤halfTrace c
  · left
    change defect c≤3*δ^2
    unfold defect
    have h := mul_nonneg hs (show 0≤1-halfTrace c by linarith)
    nlinarith [sq_nonneg δ]
  · right
    change defect (SU2StapleExtremes.minusOne*c)≤3*δ^2
    unfold defect
    rw [SU2StrongCouplingCovariance.halfTrace_center_neg]
    have h := mul_nonneg (show 0≤-halfTrace c by linarith) (show 0≤1+halfTrace c by linarith)
    nlinarith [sq_nonneg δ]

theorem stabilizer_imag_upper (θ ε : ℝ) (hθ : Real.sin θ≠0) (c : SU2)
    (hc : c∈nearStabilizer θ ε) : rootImagSq c≤(ε/|Real.sin θ|)^2 := by
  have h0 := pow_le_pow_left₀ (turn_nonneg 0 θ c) hc.1 2
  have h1 := pow_le_pow_left₀ (turn_nonneg 1 θ c) hc.2 2
  have hs := sq_pos_of_ne_zero hθ
  have h : rootImagSq c≤ε^2/(Real.sin θ)^2 := by
    apply (le_div_iff₀ hs).mpr
    nlinarith [two_axis_control θ c,sq_nonneg ε]
  simpa only [div_pow,sq_abs] using h

theorem stabilizer_cap_cover (θ ε : ℝ) (hθ : Real.sin θ≠0) :
    nearStabilizer θ ε ⊆ cap (ε/|Real.sin θ|) ∪
      ((fun x : SU2 => SU2StapleExtremes.minusOne*x) ⁻¹' cap (ε/|Real.sin θ|)) := by
  intro c hc
  exact rootImagSq_cover c _ (stabilizer_imag_upper θ ε hθ c hc)

theorem negative_cap_mass (δ : ℝ) :
    law.real ((fun x : SU2 => SU2StapleExtremes.minusOne*x) ⁻¹' cap δ)=law.real (cap δ) := by
  exact congrArg ENNReal.toReal ((measurePreserving_mul_left law SU2StapleExtremes.minusOne).measure_preimage (cap_measurable δ).nullMeasurableSet)

theorem stabilizer_mass_cap_upper (θ ε : ℝ) (hθ : Real.sin θ≠0) :
    law.real (nearStabilizer θ ε)≤2*law.real (cap (ε/|Real.sin θ|)) := by
  have h := measureReal_mono (stabilizer_cap_cover θ ε hθ) (measure_ne_top law _)
  have hu := measureReal_union_le (μ := law) (cap (ε/|Real.sin θ|))
    ((fun x : SU2 => SU2StapleExtremes.minusOne*x) ⁻¹' cap (ε/|Real.sin θ|))
  rw [negative_cap_mass] at hu
  linarith

theorem small_cap_stabilizes (θ ε : ℝ) (hθ : Real.sin θ≠0) (hε : 0≤ε) :
    cap (ε/(5*|Real.sin θ|)) ⊆ nearStabilizer θ ε := by
  intro c hc
  have hi := rootImagSq_cap c (ε/(5*|Real.sin θ|)) hc
  have hs : 0≤4*Real.sin θ^2 := by positivity
  have h0 := (turn_zero_upper θ c).trans (mul_le_mul_of_nonneg_left hi hs)
  have h1 := (turn_one_upper θ c).trans (mul_le_mul_of_nonneg_left hi hs)
  have ha : |Real.sin θ|≠0 := abs_ne_zero.mpr hθ
  have he : (4*Real.sin θ^2)*(6*(ε/(5*|Real.sin θ|))^2)=(24/25 : ℝ)*ε^2 := by
    rw [← sq_abs (Real.sin θ)]
    field_simp [ha]
    ring
  rw [he] at h0 h1
  constructor <;> nlinarith [sq_nonneg ε]

def lowerConstant : ℝ := 1/(500*Real.pi^2)
def upperConstant : ℝ := 2*(Real.exp 3*SU2HaarLaplaceUpper.upperConstant 1)

theorem lowerConstant_pos : 0<lowerConstant := by unfold lowerConstant; positivity

theorem upperConstant_pos : 0<upperConstant := by
  unfold upperConstant
  exact mul_pos (by norm_num) (mul_pos (Real.exp_pos _) (SU2HaarLaplaceUpper.upperConstant_pos 1 (by norm_num)))

theorem stabilizer_mass_cubic (θ ε : ℝ) (hθ : Real.sin θ≠0) (hε : 0<ε) (hsmall : ε≤|Real.sin θ|) :
    lowerConstant*(ε/|Real.sin θ|)^3≤law.real (nearStabilizer θ ε) ∧
    law.real (nearStabilizer θ ε)≤upperConstant*(ε/|Real.sin θ|)^3 := by
  have hs : 0 < |Real.sin θ| := abs_pos.mpr hθ
  have hd : 0<ε/(5*|Real.sin θ|) := by positivity
  have hd1 : ε/(5*|Real.sin θ|)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  have hlow := (mass_lower _ hd.le hd1).trans
    (measureReal_mono (small_cap_stabilizes θ ε hθ hε.le) (measure_ne_top law _))
  have hu := (stabilizer_mass_cap_upper θ ε hθ).trans
    (mul_le_mul_of_nonneg_left (PeriodicGroundHaarScale.cap_polynomial_upper (ε/|Real.sin θ|)
      (div_pos hε hs) ((div_le_one hs).mpr hsmall)) (by norm_num : (0 : ℝ)≤2))
  constructor
  · convert hlow using 1 <;> (unfold lowerConstant; ring)
  · simpa only [upperConstant,mul_assoc] using hu


private theorem scalar_scaled_iff (d A s δ : ℝ) (hd : 0≤d) (hs : s≠0) (hδ : 0≤δ)
    (he : d^2=4*s^2*A) : d≤δ*|s| ↔ A≤δ^2/4 := by
  constructor
  · intro h
    have hsq := pow_le_pow_left₀ hd h 2
    rw [he,mul_pow,sq_abs] at hsq
    have hlin := (mul_le_mul_iff_right₀ (sq_pos_of_ne_zero hs)).mp
      (show s^2*(4*A)≤s^2*δ^2 by nlinarith [hsq])
    linarith
  · intro h
    have hm := mul_nonneg (sq_nonneg s) (show 0≤δ^2-4*A by linarith)
    have hsq : d^2≤(δ*|s|)^2 := by rw [he,mul_pow,sq_abs]; nlinarith
    have hb : 0≤δ*|s| := mul_nonneg hδ (abs_nonneg _)
    nlinarith

theorem scaled_stabilizer_iff (θ δ : ℝ) (hθ : Real.sin θ≠0) (hδ : 0≤δ) (c : SU2) :
    c∈nearStabilizer θ (δ*|Real.sin θ|) ↔
      (lift c).imJ^2+(lift c).imK^2≤δ^2/4 ∧ (lift c).imI^2+(lift c).imK^2≤δ^2/4 := by
  exact and_congr
    (scalar_scaled_iff _ _ _ _ (turn_nonneg 0 θ c) hθ hδ (turn_zero_square θ c))
    (scalar_scaled_iff _ _ _ _ (turn_nonneg 1 θ c) hθ hδ (turn_one_square θ c))


/-- Resonant holonomies impose no constraint on a temporal root. -/
theorem resonant_stabilizer (θ ε : ℝ) (hθ : Real.sin θ=0) (hε : 0≤ε) :
    nearStabilizer θ ε=Set.univ := by
  ext c
  simp only [Set.mem_univ,iff_true]
  have h0 := turn_zero_square θ c
  have h1 := turn_one_square θ c
  rw [hθ] at h0 h1
  constructor <;> nlinarith [turn_nonneg 0 θ c,turn_nonneg 1 θ c]

theorem resonant_mass (θ ε : ℝ) (hθ : Real.sin θ=0) (hε : 0≤ε) :
    law.real (nearStabilizer θ ε)=1 := by
  rw [resonant_stabilizer θ ε hθ hε]
  simp

end OperatorDerivativeRewrite.Foundation.SU2TwoAxisStabilizerHaar
