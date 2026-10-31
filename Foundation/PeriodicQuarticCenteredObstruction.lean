import Foundation.PeriodicQuarticCenterEven
/-! Centered, center-even native quartic-tail obstructions for the actual Wilson
transfer. Two separated positive inverse-ground packets have an exponentially
small normalized cross-form. Balancing their actual stationary means yields
nonzero mean-zero probes, with a fixed positive Rayleigh lower bound, outside
every fixed flat kinetic tube along an unbounded coupling family. An operator
annihilating these probes has a uniform norm error. This is not a quasimode
with Rayleigh ratio tending to one, a gap-closing rate or a continuum theorem.
All objects are the existing genuine finite-lattice ground/operator calculus. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
namespace OperatorDerivativeRewrite.Foundation.PeriodicQuarticCenteredObstruction
open QuaternionSU2Representation PeriodicLoopVariation PeriodicCenterSeam
open SU2TwoAxisStabilizerHaar PeriodicQuarticGaugeOverlap PeriodicQuarticKernelBlock

def centralDistance (A : SU2) : ℝ := min (distance A 1) (distance A SU2StapleExtremes.minusOne)

theorem centralDistance_nonneg (A : SU2) : 0≤centralDistance A := le_min (norm_nonneg _) (norm_nonneg _)

theorem centralDistance_lipschitz (A B : SU2) : centralDistance A≤distance A B+centralDistance B := by
  unfold centralDistance
  by_cases h : distance B 1≤distance B SU2StapleExtremes.minusOne
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (distance_triangle A B 1)
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right _ _).trans (distance_triangle A B SU2StapleExtremes.minusOne)

theorem conjugate_distance (A B c : SU2) : distance (c*A*c⁻¹) (c*B*c⁻¹)=distance A B := by
  rw [right_distance_isometry,left_distance_isometry]

theorem centralDistance_conjugate (A c : SU2) : centralDistance (c*A*c⁻¹)=centralDistance A := by
  have h1 : c*(1 : SU2)*c⁻¹=1 := by group
  have hm : c*SU2StapleExtremes.minusOne*c⁻¹=SU2StapleExtremes.minusOne := by
    rw [← center_commute c]
    group
  have hd1 : distance (c*A*c⁻¹) 1=distance A 1 := by
    calc
      _ = distance (c*A*c⁻¹) (c*1*c⁻¹) := by rw [h1]
      _ = _ := conjugate_distance A 1 c
  have hdm : distance (c*A*c⁻¹) SU2StapleExtremes.minusOne=distance A SU2StapleExtremes.minusOne := by
    calc
      _ = distance (c*A*c⁻¹) (c*SU2StapleExtremes.minusOne*c⁻¹) := by rw [hm]
      _ = _ := conjugate_distance A SU2StapleExtremes.minusOne c
  unfold centralDistance
  rw [hd1,hdm]

theorem centralDistance_center (A : SU2) : centralDistance (SU2StapleExtremes.minusOne*A)=centralDistance A := by
  have h0 : distance (SU2StapleExtremes.minusOne*A) 1=distance A SU2StapleExtremes.minusOne := by
    rw [← center_square,left_distance_isometry]
  have h1 : distance (SU2StapleExtremes.minusOne*A) SU2StapleExtremes.minusOne=distance A 1 := by
    simpa only [mul_one] using left_distance_isometry A 1 SU2StapleExtremes.minusOne
  unfold centralDistance
  rw [h0,h1,min_comm]


open SU2JointPlaquetteCubic FourCubePinnedCoercivity
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSpatialHolonomy
open PeriodicQuarticNativeObstruction PeriodicQuarticCenterEven
attribute [local irreducible] temporalAction kernel boundaryHaar

theorem axis_central_distance (i : Fin 3) (u : ℝ) (hc : 0≤Real.cos (2*u)) :
    centralDistance (axis i (2*u))=2*|Real.sin u| := by
  let A := axis i (2*u)
  have h0 : distance A 1^2=2*(1-Real.cos (2*u)) := by
    rw [distance_sq]
    simp [A,defect,FourCubeWilsonCubic.axis_trace]
  have hm : distance A SU2StapleExtremes.minusOne^2=2*(1+Real.cos (2*u)) := by
    have he : distance (SU2StapleExtremes.minusOne*A) 1=distance A SU2StapleExtremes.minusOne := by
      rw [← center_square,left_distance_isometry]
    rw [← he,distance_sq]
    simp [A,defect,SU2StrongCouplingCovariance.halfTrace_center_neg,FourCubeWilsonCubic.axis_trace]
  have ha : 0≤distance A 1 := norm_nonneg _
  have hb : 0≤distance A SU2StapleExtremes.minusOne := norm_nonneg _
  have hle : distance A 1≤distance A SU2StapleExtremes.minusOne := by nlinarith
  change min (distance A 1) (distance A SU2StapleExtremes.minusOne)=_
  rw [min_eq_left hle]
  have hs := Real.sin_sq_add_cos_sq u
  have hd := Real.cos_two_mul u
  have hab := abs_nonneg (Real.sin u)
  nlinarith [sq_abs (Real.sin u)]

theorem small_angle_gap (t : ℝ) (ht : 0<t) (hsmall : t≤1/16) :
    2*t≤centralDistance (axis 0 (8*t))-centralDistance (axis 0 (4*t)) := by
  have ht2 : t^2≤1/256 := by nlinarith
  have ht3 : t^3≤t/256 := by
    have h := mul_le_mul_of_nonneg_right ht2 ht.le
    nlinarith
  have hc4 : 0≤Real.cos (4*t) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := 4*t)
    nlinarith
  have hc8 : 0≤Real.cos (8*t) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := 8*t)
    nlinarith
  have h4 := axis_central_distance 0 (2*t) (by simpa only [show (2*(2*t) : ℝ)=4*t by ring] using hc4)
  have h8 := axis_central_distance 0 (4*t) (by simpa only [show (2*(4*t) : ℝ)=8*t by ring] using hc8)
  rw [show (2*(2*t) : ℝ)=4*t by ring] at h4
  rw [show (2*(4*t) : ℝ)=8*t by ring] at h8
  rw [h4,h8]
  have hs4 := Real.sin_gt_sub_cube (show (0 : ℝ)<4*t by linarith)
  have hs2 := Real.abs_sin_le_abs (x := 2*t)
  rw [abs_of_pos (show (0 : ℝ)<2*t by linarith)] at hs2
  nlinarith [le_abs_self (Real.sin (4*t))]

def level (U : State) : ℝ := centralDistance (winding U PeriodicCenteredHolonomy.origin 0)

theorem level_gauge (a : Gauge) (U : State) : level (PeriodicSlabGauge.gaugeAction a U)=level U := by
  unfold level
  rw [winding_gauge,centralDistance_conjugate]

theorem level_seam (i : Fin 3) (U : State) : level (flip i U)=level U := by
  unfold level
  by_cases hi : i=0
  · subst i
    rw [PeriodicCenteredHolonomy.winding_flip_same,centralDistance_center]
  · rw [PeriodicCenteredHolonomy.winding_flip_other i 0 (Ne.symm hi)]

theorem packet_winding_distance (C U : State) (r : ℝ) (hU : U∈packet C r) (v : SpatialVertex) :
    distance (winding U v 0) (winding C v 0)≤4*r := by
  have h1 := distance_mul (U (v,0)) (U (shift v 0,0)) (C (v,0)) (C (shift v 0,0))
  have h2 := distance_mul (U (v,0)*U (shift v 0,0)) (U (twice v 0,0))
    (C (v,0)*C (shift v 0,0)) (C (twice v 0,0))
  have h3 := distance_mul (U (v,0)*U (shift v 0,0)*U (twice v 0,0)) (U (thrice v 0,0))
    (C (v,0)*C (shift v 0,0)*C (twice v 0,0)) (C (thrice v 0,0))
  unfold winding
  linarith [hU (v,0),hU (shift v 0,0),hU (twice v 0,0),hU (thrice v 0,0)]

theorem packet_level (t r : ℝ) (U : State) (hU : U∈packet (PeriodicQuarticCurvature.field t) r) :
    centralDistance (axis 0 (4*t))-4*r≤level U ∧ level U≤centralDistance (axis 0 (4*t))+4*r := by
  have hd := packet_winding_distance _ U r hU PeriodicCenteredHolonomy.origin
  have hl := centralDistance_lipschitz (winding U PeriodicCenteredHolonomy.origin 0)
    (winding (PeriodicQuarticCurvature.field t) PeriodicCenteredHolonomy.origin 0)
  have hr := centralDistance_lipschitz (winding (PeriodicQuarticCurvature.field t) PeriodicCenteredHolonomy.origin 0)
    (winding U PeriodicCenteredHolonomy.origin 0)
  rw [distance_symm] at hr
  rw [PeriodicFlatLocusQuarticObstruction.winding_field_zero] at hl hr hd
  change _≤_+level U at hr
  change level U≤_ at hl
  constructor <;> linarith

theorem region_level (t r : ℝ) (U : State) (hU : U∈packetRegion t r) :
    centralDistance (axis 0 (4*t))-4*r≤level U ∧ level U≤centralDistance (axis 0 (4*t))+4*r := by
  obtain ⟨a,ha⟩ := packetRegion_witness t r U hU
  have h := packet_level t r _ ha
  rw [level_gauge] at h
  exact h


def InBand (t r : ℝ) (U : State) : Prop :=
  centralDistance (axis 0 (4*t))-4*r≤level U ∧ level U≤centralDistance (axis 0 (4*t))+4*r

theorem trial_band {β : ℝ} (g : PeriodicSlabGround.GroundData β) (t r : ℝ) (U : State)
    (hf : trial g (packetRegion t r) U≠0) : InBand t r U := by
  have hu : U∈packetRegion t r := by
    by_contra hn
    apply hf
    simp [trial,chi,hn]
  exact region_level t r U hu

theorem average_band (i : Fin 3) (f : State → ℝ) (t r : ℝ)
    (hf : ∀ U,f U≠0 → InBand t r U) (U : State)
    (ha : PeriodicQuarticCenterEven.average i f U≠0) : InBand t r U := by
  by_cases h0 : f U=0
  · have h1 : f (flip i U)≠0 := by
      intro h
      apply ha
      simp [PeriodicQuarticCenterEven.average,h0,h]
    have hb := hf (flip i U) h1
    simpa only [InBand,level_seam] using hb
  · exact hf U h0

theorem centerTrial_band {β : ℝ} (g : PeriodicSlabGround.GroundData β) (t r : ℝ) (U : State)
    (hf : centerTrial g t r U≠0) : InBand t r U :=
  average_band 2 _ t r (average_band 1 _ t r (average_band 0 _ t r (trial_band g t r))) U hf

theorem band_gap (t r : ℝ) (ht : 0<t) (hsmall : t≤1/16) (hr : 8*r≤t)
    (U V : State) (hU : InBand t r U) (hV : InBand (2*t) r V) : t≤level V-level U := by
  have hg := small_angle_gap t ht hsmall
  have hv := hV.1
  rw [show (4*(2*t) : ℝ)=8*t by ring] at hv
  linarith [hU.2]

theorem band_disjoint (t r : ℝ) (ht : 0<t) (hsmall : t≤1/16) (hr : 8*r≤t)
    (U : State) : ¬(InBand t r U ∧ InBand (2*t) r U) := by
  rintro ⟨h0,h1⟩
  have h := band_gap t r ht hsmall hr U U h0 h1
  linarith

theorem temporal_level_lower (d : ℝ) (hd : 0≤d) (U V : State) (hv : d≤level V-level U)
    (a : Gauge) : d^2≤32*temporalAction U V a := by
  have hl := centralDistance_lipschitz (winding (PeriodicSlabGauge.gaugeAction a V) PeriodicCenteredHolonomy.origin 0)
    (winding U PeriodicCenteredHolonomy.origin 0)
  rw [distance_symm] at hl
  change level (PeriodicSlabGauge.gaugeAction a V)≤_+level U at hl
  rw [level_gauge] at hl
  have ht := PeriodicFlatLocusQuarticObstruction.winding_square_temporal U V a PeriodicCenteredHolonomy.origin 0
  have hh : d≤distance (winding U PeriodicCenteredHolonomy.origin 0)
      (winding (PeriodicSlabGauge.gaugeAction a V) PeriodicCenteredHolonomy.origin 0) := by linarith
  exact (pow_le_pow_left₀ hd hh 2).trans ht

theorem kernel_level_upper (β d : ℝ) (hb : 0≤β) (hd : 0≤d)
    (U V : State) (hv : d≤level V-level U) : kernel β U V≤Real.exp (-β*d^2/32) := by
  have hw (a : Gauge) : weight β U V a≤Real.exp (-β*d^2/32) := by
    have ht := temporal_level_lower d hd U V hv a
    have hsU := (spatial_action_bounds U).1
    have hsV := (spatial_action_bounds V).1
    have ha : d^2/32≤halfAction U V a := by unfold halfAction; linarith
    have hp := mul_le_mul_of_nonneg_left ha hb
    unfold weight
    apply Real.exp_le_exp.mpr
    linarith
  have hi := integral_mono (weight_integrable β U V) (integrable_const (Real.exp (-β*d^2/32))) hw
  simpa only [kernel,integral_const,probReal_univ,one_smul] using hi

theorem centerTrial_cross_kernel {β : ℝ} (g : PeriodicSlabGround.GroundData β)
    (t r : ℝ) (hb : 0≤β) (ht : 0<t) (hsmall : t≤1/16) (hr : 8*r≤t)
    (U V : State) (hU : centerTrial g t r U≠0) (hV : centerTrial g (2*t) r V≠0) :
    kernel β U V≤Real.exp (-β*t^2/32) :=
  kernel_level_upper β t hb ht.le U V (band_gap t r ht hsmall hr U V
    (centerTrial_band g t r U hU) (centerTrial_band g (2*t) r V hV))


open PeriodicSlabGround PeriodicSlabL2
variable {β : ℝ} (g : GroundData β)
private instance stationary_probability : IsProbabilityMeasure g.stationary := g.stationary_probability

def weightTrial (t r : ℝ) (U : State) : ℝ := g.function U*centerTrial g t r U

theorem ground_evenPart (f : State → ℝ) (U : State) :
    g.function U*evenPart f U=evenPart (fun V => g.function V*f V) U := by
  simp only [evenPart,PeriodicQuarticCenterEven.average]
  simp_rw [PeriodicGroundSeamParity.ground_invariant]
  ring

theorem weightTrial_cancel (t r : ℝ) (U : State) :
    weightTrial g t r U=evenPart (chi (packetRegion t r)) U := by
  unfold weightTrial centerTrial
  rw [ground_evenPart]
  have he : (fun V => g.function V*trial g (packetRegion t r) V)=chi (packetRegion t r) :=
    funext (cancel_trial g _)
  rw [he]

theorem weightTrial_bounds (t r : ℝ) (U : State) : 0≤weightTrial g t r U ∧ weightTrial g t r U≤1 := by
  rw [weightTrial_cancel]
  have hn (V : State) : 0≤chi (packetRegion t r) V := by
    by_cases hv : V∈packetRegion t r <;> simp [chi,hv]
  exact ⟨evenPart_nonneg _ hn U,(le_abs_self _).trans (evenPart_bound _ 1 (chi_abs _) U)⟩

theorem weightTrial_measurable (t r : ℝ) : Measurable (weightTrial g t r) :=
  g.measurable.mul (centerTrial_measurable g t r)

attribute [local irreducible] pairing

theorem pairing_unit_bound (β : ℝ) (f h : State → ℝ) (hf : Measurable f) (hh : Measurable h)
    (hfB : ∀ U,0≤f U ∧ f U≤1) (hhB : ∀ U,0≤h U ∧ h U≤1) (e : ℝ) (he : 0≤e)
    (hK : ∀ U,f U≠0 → ∀ V,h V≠0 → kernel β U V≤e) : pairing β f h≤e := by
  have hb (p : State × State) : 0≤f p.1*(kernel β p.1 p.2*h p.2) ∧
      f p.1*(kernel β p.1 p.2*h p.2)≤Real.exp (768*|β|) := by
    have hk := (kernel_positive β p.1 p.2).le
    have h1 := mul_le_mul_of_nonneg_left (hhB p.2).2 hk
    have h2 := mul_le_mul_of_nonneg_right (hfB p.1).2 (mul_nonneg hk (hhB p.2).1)
    simp only [mul_one,one_mul] at h1 h2
    exact ⟨mul_nonneg (hfB p.1).1 (mul_nonneg hk (hhB p.2).1),
      h2.trans (h1.trans (kernel_bounds β p.1 p.2).2)⟩
  have hi : Integrable (fun p : State × State => f p.1*(kernel β p.1 p.2*h p.2))
      (boundaryHaar.prod boundaryHaar) := by
    apply Integrable.of_bound ((hf.comp measurable_fst).mul
      ((kernel_joint_measurable β).mul (hh.comp measurable_snd))).aestronglyMeasurable (Real.exp (768*|β|))
    filter_upwards with p
    change ‖f p.1*(kernel β p.1 p.2*h p.2)‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (hb p).1]
    exact (hb p).2
  have hp (p : State × State) : f p.1*(kernel β p.1 p.2*h p.2)≤e := by
    by_cases h0 : f p.1=0
    · simp [h0,he]
    by_cases h1 : h p.2=0
    · simp [h1,he]
    have hk := (kernel_positive β p.1 p.2).le
    have ha := mul_le_mul_of_nonneg_left (hhB p.2).2 hk
    have hb' := mul_le_mul_of_nonneg_right (hfB p.1).2 (mul_nonneg hk (hhB p.2).1)
    simp only [mul_one,one_mul] at ha hb'
    exact hb'.trans (ha.trans (hK p.1 h0 p.2 h1))
  have hInt := integral_mono hi (integrable_const e) hp
  have hpEq : pairing β f h=∫ p : State × State,f p.1*(kernel β p.1 p.2*h p.2) ∂boundaryHaar.prod boundaryHaar := by
    unfold pairing
    simp_rw [← integral_const_mul]
    exact (integral_prod _ hi).symm
  rw [hpEq]
  simpa only [integral_const,probReal_univ,one_smul] using hInt

theorem native_cross (f h : State → ℝ) (hf : Measurable f) (hh : Measurable h)
    (B C : ℝ) (hb : ∀ U,|f U|≤B) (hc : ∀ U,|h U|≤C)
    (hmf : MemLp f 2 g.stationary) (hmh : MemLp h 2 g.stationary) :
    inner ℝ (operator g (hmh.toLp h)) (hmf.toLp f)=
      pairing β (fun U => g.function U*f U) (fun U => g.function U*h U)/(g.value*g.normalizer) := by
  rw [operator_toLp g h hmh hh C hc,L2.inner_def]
  have he : (fun U => inner ℝ ((transfer_memLp g h hh C hc).toLp (transfer g h) U) (hmf.toLp f U))
      =ᵐ[g.stationary] (fun U => f U*transfer g h U) := by
    filter_upwards [MemLp.coeFn_toLp (transfer_memLp g h hh C hc),MemLp.coeFn_toLp hmf] with U hP hF
    rw [hP,hF]
    rfl
  rw [integral_congr_ae he]
  exact g.stationary_pairing f h

theorem native_cross_upper (t r : ℝ) (hb : 0≤β) (ht : 0<t) (hsmall : t≤1/16) (hr : 8*r≤t) :
    inner ℝ (operator g (nativeCenter g (2*t) r)) (nativeCenter g t r)≤
      Real.exp (-β*t^2/32)/(g.value*g.normalizer) := by
  unfold nativeCenter
  rw [native_cross g _ _ (centerTrial_measurable g t r) (centerTrial_measurable g (2*t) r)
    _ _ (centerTrial_bound g t r) (centerTrial_bound g (2*t) r)]
  apply div_le_div_of_nonneg_right _ (mul_pos g.value_pos g.normalizer_pos).le
  apply pairing_unit_bound β _ _ (weightTrial_measurable g t r) (weightTrial_measurable g (2*t) r)
    (weightTrial_bounds g t r) (weightTrial_bounds g (2*t) r) _ (Real.exp_pos _).le
  intro U hU V hV
  have hu : centerTrial g t r U≠0 := fun h => hU (by simp [weightTrial,h])
  have hv : centerTrial g (2*t) r V≠0 := fun h => hV (by simp [weightTrial,h])
  exact centerTrial_cross_kernel g t r hb ht hsmall hr U V hu hv


theorem region_mass_simple (t r : ℝ) :
    boundaryHaar.real (packet (PeriodicQuarticCurvature.field t) r)≤boundaryHaar.real (packetRegion t r) := by
  have hp (U : State) : packetAverage t r U≤(packetRegion t r).indicator (fun _ => (1 : ℝ)) U := by
    by_cases hu : U∈packetRegion t r
    · rw [Set.indicator_of_mem hu]
      exact (packetAverage_bounds t r U).2
    · rw [Set.indicator_of_notMem hu]
      exact le_of_not_gt hu
  have hi := integral_mono_of_nonneg (ae_of_all _ (fun U => (packetAverage_bounds t r U).1))
    ((integrable_const (μ := boundaryHaar) (1 : ℝ)).indicator (packetRegion_measurable t r)) (ae_of_all _ hp)
  rw [packetAverage_mass] at hi
  have he : (∫ U,(packetRegion t r).indicator (fun _ => (1 : ℝ)) U ∂boundaryHaar)=boundaryHaar.real (packetRegion t r) := integral_indicator_one (packetRegion_measurable t r)
  exact hi.trans_eq he

theorem center_norm_floor (t r : ℝ) (hr : 0<r) (h1 : r≤1/8) :
    relativeLower^192*r^576/(64*g.normalizer)≤‖nativeCenter g t r‖^2 := by
  have hs := evenPart_square_lower g _ (trial_measurable g _ (packetRegion_measurable t r))
    _ (trial_bound g _) (trial_nonneg g _)
  have h0 := native_square g _ (trial_memLp g _ (packetRegion_measurable t r))
  have h1n := native_square g _ (centerTrial_memLp g t r)
  change ‖nativeTrial g t r‖^2=_ at h0
  change ‖nativeCenter g t r‖^2=square g (evenPart (trial g (packetRegion t r))) at h1n
  rw [← h0,← h1n,nativeTrial_norm_square] at hs
  have hm := (packet_scaled_lower t r hr h1).trans (region_mass_simple t r)
  have hh := div_le_div_of_nonneg_right hm (mul_pos (by norm_num : (0 : ℝ)<64) g.normalizer_pos).le
  have he : boundaryHaar.real (packetRegion t r)/(64*g.normalizer)=
      (boundaryHaar.real (packetRegion t r)/g.normalizer)/64 := by ring
  rw [he] at hh
  exact hh.trans hs

def crossCoefficient (β t : ℝ) : ℝ :=
  (64/(relativeLower^192*PeriodicGaugeSaturatedGround.eigenLowerConstant))*β^576*Real.exp (-β*t^2/32)

theorem crossCoefficient_nonneg (β t : ℝ) : 0≤crossCoefficient β t := by
  unfold crossCoefficient
  exact mul_nonneg (mul_nonneg (div_pos (by norm_num)
    (mul_pos (pow_pos relativeLower_pos _) PeriodicGaugeSaturatedGround.eigenLowerConstant_pos)).le
    (by positivity : (0 : ℝ)≤β^576)) (Real.exp_pos _).le

theorem native_cross_relative (t r : ℝ) (hb : 16777216≤β) (ht : 0<t) (hsmall : t≤1/16)
    (hr : 0<r) (h1 : r≤1/8) (hnarrow : 8*r≤t) (hheat : β*r^2=1) :
    inner ℝ (operator g (nativeCenter g (2*t) r)) (nativeCenter g t r)≤
      crossCoefficient β t*(‖nativeCenter g t r‖*‖nativeCenter g (2*t) r‖) := by
  have hbpos : 0<β := by linarith
  let D := relativeLower^192/(64*g.normalizer*β^288)
  have hD : 0≤D := (div_pos (pow_pos relativeLower_pos _)
    (mul_pos (mul_pos (by norm_num : (0 : ℝ)<64) g.normalizer_pos) (pow_pos hbpos _))).le
  have h0 := center_norm_floor g t r hr h1
  have h2 := center_norm_floor g (2*t) r hr h1
  rw [beta_radius_power β r hheat] at h0 h2
  have he : relativeLower^192*(1/β^288)/(64*g.normalizer)=D := by dsimp [D]; ring
  rw [he] at h0 h2
  have hprod : D≤‖nativeCenter g t r‖*‖nativeCenter g (2*t) r‖ := by
    by_cases hn : ‖nativeCenter g t r‖≤‖nativeCenter g (2*t) r‖
    · exact h0.trans (by nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (nativeCenter g t r))])
    · exact h2.trans (by nlinarith [mul_le_mul_of_nonneg_right (le_of_not_ge hn) (norm_nonneg (nativeCenter g (2*t) r))])
  have hLam := PeriodicGaugeSaturatedGround.eigenvalue_matching_lower β hb g
  have hden := mul_le_mul_of_nonneg_right hLam g.normalizer_pos.le
  have hdenpos : 0<(PeriodicGaugeSaturatedGround.eigenLowerConstant/β^288)*g.normalizer :=
    mul_pos (div_pos PeriodicGaugeSaturatedGround.eigenLowerConstant_pos (pow_pos hbpos _)) g.normalizer_pos
  have hdiv := div_le_div_of_nonneg_left (Real.exp_pos (-β*t^2/32)).le hdenpos hden
  have hid : Real.exp (-β*t^2/32)/((PeriodicGaugeSaturatedGround.eigenLowerConstant/β^288)*g.normalizer)=crossCoefficient β t*D := by
    unfold crossCoefficient
    dsimp [D]
    field_simp [hbpos.ne',g.normalizer_pos.ne',relativeLower_pos.ne',PeriodicGaugeSaturatedGround.eigenLowerConstant_pos.ne']
    <;> ring
  exact (native_cross_upper g t r hbpos.le ht hsmall hnarrow).trans
    (hdiv.trans (hid.le.trans (mul_le_mul_of_nonneg_left hprod (crossCoefficient_nonneg β t))))

open Filter
open scoped Topology

theorem crossCoefficient_tendsto : Tendsto (fun x : ℝ => crossCoefficient (1/x^6) (x^2)) (𝓝[>] 0) (𝓝 0) := by
  let y := fun x : ℝ => 1/(32*x^2)
  have hy : Tendsto y (𝓝[>] 0) atTop := by
    have h := Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ)<8) flat_distance_diverges
    convert h using 1
    funext x
    dsimp [y]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1728).comp hy
  let C : ℝ := (64/(relativeLower^192*PeriodicGaugeSaturatedGround.eigenLowerConstant))*32^1728
  have hC := hp.const_mul C
  have he : (fun x : ℝ => crossCoefficient (1/x^6) (x^2)) =ᶠ[𝓝[>] 0]
      (fun x => C*((y x)^1728*Real.exp (-(y x)))) := by
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[>] 0,0<x)] with x hx
    change 0<x at hx
    have harg : (1/x^6)*(x^2)^2/32=y x := by
      dsimp [y]
      field_simp [hx.ne']
      <;> ring
    have hpow : (1/x^6)^576=32^1728*(y x)^1728 := by
      calc
        _ = ((1/x^2)^3)^576 := by congr 1; simp only [div_pow,one_pow,← pow_mul]
        _ = (1/x^2)^1728 := by rw [← pow_mul]
        _ = (32*(y x))^1728 := by congr 1; dsimp [y]; field_simp
        _ = _ := mul_pow _ _ _
    unfold crossCoefficient
    have hargN : -(1/x^6)*(x^2)^2/32= -(y x) := by linarith [harg]
    rw [hargN,hpow]
    dsimp [C]
    ring
  exact (tendsto_congr' he).mpr (by simpa only [mul_zero,Function.comp_def] using hC)


theorem centerTrial_disjoint (t r : ℝ) (ht : 0<t) (hsmall : t≤1/16) (hr : 8*r≤t) (U : State) :
    centerTrial g t r U*centerTrial g (2*t) r U=0 := by
  by_cases h0 : centerTrial g t r U=0
  · rw [h0,zero_mul]
  by_cases h1 : centerTrial g (2*t) r U=0
  · rw [h1,mul_zero]
  exact False.elim (band_disjoint t r ht hsmall hr U ⟨centerTrial_band g t r U h0,centerTrial_band g (2*t) r U h1⟩)

theorem nativeCenter_orthogonal (t r : ℝ) (ht : 0<t) (hsmall : t≤1/16) (hr : 8*r≤t) :
    inner ℝ (nativeCenter g t r) (nativeCenter g (2*t) r)=0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ _ : State,(0 : ℝ) ∂g.stationary := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (centerTrial_memLp g t r),MemLp.coeFn_toLp (centerTrial_memLp g (2*t) r)] with U h0 h1
      change nativeCenter g t r U=centerTrial g t r U at h0
      change nativeCenter g (2*t) r U=centerTrial g (2*t) r U at h1
      rw [h0,h1]
      change centerTrial g (2*t) r U*centerTrial g t r U=0
      rw [mul_comm]
      exact centerTrial_disjoint g t r ht hsmall hr U
    _ = 0 := integral_zero _ _

def trialMean (t r : ℝ) : ℝ := ∫ U,centerTrial g t r U ∂g.stationary

def balancedRaw (t r : ℝ) (U : State) : ℝ :=
  trialMean g (2*t) r*centerTrial g t r U-trialMean g t r*centerTrial g (2*t) r U

def nativeBalanced (t r : ℝ) : StateL2 g :=
  trialMean g (2*t) r • nativeCenter g t r-trialMean g t r • nativeCenter g (2*t) r

theorem nativeBalanced_repr (t r : ℝ) : ∀ᵐ U ∂g.stationary,nativeBalanced g t r U=balancedRaw g t r U := by
  filter_upwards [Lp.coeFn_sub (trialMean g (2*t) r • nativeCenter g t r) (trialMean g t r • nativeCenter g (2*t) r),
    Lp.coeFn_smul (trialMean g (2*t) r) (nativeCenter g t r),
    Lp.coeFn_smul (trialMean g t r) (nativeCenter g (2*t) r),
    MemLp.coeFn_toLp (centerTrial_memLp g t r),MemLp.coeFn_toLp (centerTrial_memLp g (2*t) r)] with U hsub h0 h1 hF hG
  change nativeBalanced g t r U= (trialMean g (2*t) r • nativeCenter g t r) U-(trialMean g t r • nativeCenter g (2*t) r) U at hsub
  change (trialMean g (2*t) r • nativeCenter g t r) U=trialMean g (2*t) r*nativeCenter g t r U at h0
  change (trialMean g t r • nativeCenter g (2*t) r) U=trialMean g t r*nativeCenter g (2*t) r U at h1
  change nativeCenter g t r U=centerTrial g t r U at hF
  change nativeCenter g (2*t) r U=centerTrial g (2*t) r U at hG
  rw [hsub,h0,h1,hF,hG]
  rfl

theorem centerTrial_integrable (t r : ℝ) : Integrable (centerTrial g t r) g.stationary :=
  (centerTrial_memLp g t r).integrable (by norm_num)

theorem nativeBalanced_mean_zero (t r : ℝ) : (∫ U,nativeBalanced g t r U ∂g.stationary)=0 := by
  rw [integral_congr_ae (nativeBalanced_repr g t r)]
  unfold balancedRaw
  rw [integral_sub ((centerTrial_integrable g t r).const_mul _) ((centerTrial_integrable g (2*t) r).const_mul _),
    integral_const_mul,integral_const_mul]
  change trialMean g (2*t) r*trialMean g t r-trialMean g t r*trialMean g (2*t) r=0
  ring

theorem balancedRaw_even (t r : ℝ) (i : Fin 3) (U : State) : balancedRaw g t r (flip i U)=balancedRaw g t r U := by
  unfold balancedRaw
  rw [centerTrial_even,centerTrial_even]

theorem balancedRaw_invariant (t r : ℝ) (a : Gauge) (U : State) :
    balancedRaw g t r (PeriodicSlabGauge.gaugeAction a U)=balancedRaw g t r U := by
  unfold balancedRaw
  rw [centerTrial_invariant,centerTrial_invariant]

theorem nativeBalanced_even (t r : ℝ) (i : Fin 3) :
    ∀ᵐ U ∂g.stationary,nativeBalanced g t r (flip i U)=nativeBalanced g t r U := by
  have hf := nativeBalanced_repr g t r
  have hi := (PeriodicGroundSeamParity.stationary_preserving g i).quasiMeasurePreserving.ae_eq_comp hf
  filter_upwards [hf,hi] with U h0 h1
  change nativeBalanced g t r (flip i U)=balancedRaw g t r (flip i U) at h1
  rw [h0,h1,balancedRaw_even]

theorem balance_norm_identity (F G : StateL2 g) (a b : ℝ) (hFG : inner ℝ F G=0) :
    ‖b • F-a • G‖^2=b^2*‖F‖^2+a^2*‖G‖^2 := by
  have hGF : inner ℝ G F=0 := by rw [real_inner_comm]; exact hFG
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    hFG,hGF,real_inner_self_eq_norm_sq,mul_zero,sub_zero,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem balance_form_identity (F G : StateL2 g) (a b : ℝ) :
    inner ℝ (operator g (b • F-a • G)) (b • F-a • G)=
      b^2*inner ℝ (operator g F) F+a^2*inner ℝ (operator g G) G-2*a*b*inner ℝ (operator g G) F := by
  have hsym : inner ℝ (operator g F) G=inner ℝ (operator g G) F := by
    rw [operator_symmetric,real_inner_comm]
  simp only [map_sub,map_smul,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,hsym]
  ring

theorem balance_rayleigh (F G : StateL2 g) (a b c e : ℝ) (ha : 0≤a) (hb : 0≤b) (he : 0≤e)
    (hFG : inner ℝ F G=0) (hF : c*‖F‖^2≤ inner ℝ (operator g F) F)
    (hG : c*‖G‖^2≤ inner ℝ (operator g G) G)
    (hcross : inner ℝ (operator g G) F≤e*(‖F‖*‖G‖)) :
    (c-e)*‖b • F-a • G‖^2≤ inner ℝ (operator g (b • F-a • G)) (b • F-a • G) := by
  rw [balance_norm_identity g F G a b hFG,balance_form_identity]
  have hf := mul_le_mul_of_nonneg_left hF (sq_nonneg b)
  have hg := mul_le_mul_of_nonneg_left hG (sq_nonneg a)
  have hc := mul_le_mul_of_nonneg_left hcross (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ)≤2) ha) hb)
  have hsq := mul_nonneg he (sq_nonneg (b*‖F‖-a*‖G‖))
  nlinarith



theorem nativeBalanced_norm_pos (t r : ℝ) (ht : 0<t) (hsmall : t≤1/16) (hr : 8*r≤t)
    (hF : 0<‖nativeCenter g t r‖) (hG : 0<‖nativeCenter g (2*t) r‖) : 0<‖nativeBalanced g t r‖ := by
  have hmA : 0<trialMean g t r := centerTrial_mean_pos g t r hF
  have hmB : 0<trialMean g (2*t) r := centerTrial_mean_pos g (2*t) r hG
  have hn := balance_norm_identity g (nativeCenter g t r) (nativeCenter g (2*t) r)
    (trialMean g t r) (trialMean g (2*t) r) (nativeCenter_orthogonal g t r ht hsmall hr)
  change ‖nativeBalanced g t r‖^2=_ at hn
  have hp := mul_pos (sq_pos_of_pos hmB) (sq_pos_of_pos hF)
  have hq := mul_nonneg (sq_nonneg (trialMean g t r)) (sq_nonneg ‖nativeCenter g (2*t) r‖)
  nlinarith [norm_nonneg (nativeBalanced g t r)]

theorem avoids_mono (f : State → ℝ) (A B : ℝ) (hf : AvoidsFlat β B f) (hAB : A≤B) : AvoidsFlat β A f :=
  fun U V hV a hclose => hf U V hV a (hclose.trans_le hAB)

theorem nativeBalanced_avoids (t r M : ℝ)
    (hF : AvoidsFlat β M (centerTrial g t r)) (hG : AvoidsFlat β M (centerTrial g (2*t) r)) :
    ∀ᵐ U ∂g.stationary,∀ V : State,spatialAction V=0 → ∀ a : Gauge,
      β*temporalAction U V a<M → nativeBalanced g t r U=0 := by
  filter_upwards [nativeBalanced_repr g t r] with U hU
  intro V hV a hclose
  rw [hU]
  unfold balancedRaw
  rw [hF U V hV a hclose,hG U V hV a hclose]
  ring

theorem centerTrial_flat_budget (t r : ℝ) (hb : 0≤β) (ht : 0≤t) (hr : 0≤r)
    (hnarrow : 256*r≤t) (hsin : t≤|Real.sin (4*t)|) :
    AvoidsFlat β (β*t^2/256) (centerTrial g t r) := by
  apply centerTrial_avoids
  intro U hU V hV a
  have hsmall : r≤|Real.sin (4*t)|/256 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<256)).mpr
    linarith
  have hg := packetRegion_flat_separation t r hr hsmall U V hU hV a
  have hs := pow_le_pow_left₀ ht hsin 2
  rw [sq_abs] at hs
  have hp := mul_le_mul_of_nonneg_left (hs.trans hg) (div_nonneg hb (by norm_num : (0 : ℝ)≤256))
  nlinarith

theorem nativeBalanced_lower (t r : ℝ) (ht : 0<t) (hsmall : t≤1/16) (hr : 8*r≤t)
    (hF : 0<‖nativeCenter g t r‖) (hG : 0<‖nativeCenter g (2*t) r‖)
    (hf : (nativeConstant/8)*‖nativeCenter g t r‖^2≤ inner ℝ (operator g (nativeCenter g t r)) (nativeCenter g t r))
    (hg : (nativeConstant/8)*‖nativeCenter g (2*t) r‖^2≤ inner ℝ (operator g (nativeCenter g (2*t) r)) (nativeCenter g (2*t) r))
    (hc : inner ℝ (operator g (nativeCenter g (2*t) r)) (nativeCenter g t r)≤
      crossCoefficient β t*(‖nativeCenter g t r‖*‖nativeCenter g (2*t) r‖))
    (he : crossCoefficient β t≤nativeConstant/16) :
    (nativeConstant/16)*‖nativeBalanced g t r‖^2≤ inner ℝ (operator g (nativeBalanced g t r)) (nativeBalanced g t r) := by
  have hmA : 0<trialMean g t r := centerTrial_mean_pos g t r hF
  have hmB : 0<trialMean g (2*t) r := centerTrial_mean_pos g (2*t) r hG
  have h := balance_rayleigh g (nativeCenter g t r) (nativeCenter g (2*t) r)
    (trialMean g t r) (trialMean g (2*t) r) (nativeConstant/8) (crossCoefficient β t)
    hmA.le hmB.le (crossCoefficient_nonneg β t) (nativeCenter_orthogonal g t r ht hsmall hr) hf hg hc
  change (nativeConstant/8-crossCoefficient β t)*‖nativeBalanced g t r‖^2≤_ at h
  have he' : nativeConstant/16≤nativeConstant/8-crossCoefficient β t := by linarith
  exact (mul_le_mul_of_nonneg_right he' (sq_nonneg _)).trans h

theorem eventual_centered_family : ∀ᶠ x : ℝ in 𝓝[>] 0,∀ q : GroundData (1/x^6),
    0<‖nativeBalanced q (x^2) (x^3)‖ ∧
      (nativeConstant/16)*‖nativeBalanced q (x^2) (x^3)‖^2≤ inner ℝ
        (operator q (nativeBalanced q (x^2) (x^3))) (nativeBalanced q (x^2) (x^3)) ∧
      (∀ᵐ U ∂q.stationary,∀ V : State,spatialAction V=0 → ∀ a : Gauge,
        (1/x^6)*temporalAction U V a<1/(256*x^2) → nativeBalanced q (x^2) (x^3) U=0) := by
  have htend : Tendsto (fun x : ℝ => 2*x^2) (𝓝 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).pow 2).const_mul 2
  have hs2 := htend.eventually eventual_sine_conditions
  have hlarge := coupling_diverges.eventually (eventually_ge_atTop (16777216 : ℝ))
  have hcross := crossCoefficient_tendsto.eventually (Iio_mem_nhds (div_pos nativeConstant_pos (by norm_num) : (0 : ℝ)<nativeConstant/16))
  have hsmall : ∀ᶠ x : ℝ in 𝓝 0,x<(1/256 : ℝ) := Iio_mem_nhds (by norm_num)
  filter_upwards [eventual_native_family,hs2.filter_mono nhdsWithin_le_nhds,hlarge,hcross,
    hsmall.filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[>] 0,0<x)] with x hbase hs2 hlarge hcross hsmall hx q
  change 0<x at hx
  have hx2 : x^2≤1/65536 := by
    have h := pow_le_pow_left₀ hx.le hsmall.le 2
    norm_num at h
    exact h
  have hr : 0<x^3 := pow_pos hx 3
  have ht : 0<x^2 := pow_pos hx 2
  have hr1 : x^3≤1/8 := by
    have h := pow_le_pow_left₀ hx.le hsmall.le 3
    norm_num at h
    linarith
  have ht1 : x^2≤1/16 := by linarith
  have hnarrow : 256*x^3≤x^2 := by
    have h := mul_le_mul_of_nonneg_right (show (256 : ℝ)*x≤1 by linarith) (sq_nonneg x)
    nlinarith
  have h8 : 8*x^3≤x^2 := by linarith
  have hb : 0≤1/x^6 := (one_div_pos.mpr (pow_pos hx 6)).le
  have hheat : (1/x^6)*(x^3)^2=1 := by field_simp [hx.ne']
  have hpot : (1/x^6)*(2*x^2)^4≤1 := by
    have he : (1/x^6)*(2*x^2)^4=16*x^2 := by field_simp [hx.ne']; ring
    rw [he]
    linarith
  obtain ⟨hnF,hformF,_,hsep⟩ := hbase q
  have hnG := nativeTrial_norm_pos q (2*x^2) (x^3) hr (by linarith)
  have hformG := uniform_native_lower q (2*x^2) (x^3) hb (by linarith) hr hr1 (by linarith)
    hs2.1 hs2.2 hheat hpot
  have hF := nativeCenter_norm_pos q _ _ hnF
  have hG := nativeCenter_norm_pos q _ _ hnG
  have hf := nativeCenter_lower q _ _ hformF
  have hg := nativeCenter_lower q _ _ hformG
  have hc := native_cross_relative q (x^2) (x^3) hlarge ht ht1 hr hr1 h8 hheat
  have haF := centerTrial_avoids q (x^2) (x^3) (1/(256*x^2)) hsep
  have haG := centerTrial_flat_budget q (2*x^2) (x^3) hb (by positivity) hr.le (by linarith) hs2.2
  have hbudget : 1/(256*x^2)≤(1/x^6)*(2*x^2)^2/256 := by
    have he : (1/x^6)*(2*x^2)^2/256=4*(1/(256*x^2)) := by field_simp [hx.ne']; ring
    rw [he]
    have hp : (0 : ℝ)≤1/(256*x^2) := by positivity
    linarith
  exact ⟨nativeBalanced_norm_pos q _ _ ht ht1 h8 hF hG,
    nativeBalanced_lower q _ _ ht ht1 h8 hF hG hf hg hc hcross.le,
    nativeBalanced_avoids q _ _ _ haF (avoids_mono _ _ _ haG hbudget)⟩



theorem balanced_error_lower (t r : ℝ) (hF : 0<‖nativeBalanced g t r‖)
    (hform : (nativeConstant/16)*‖nativeBalanced g t r‖^2≤ inner ℝ (operator g (nativeBalanced g t r)) (nativeBalanced g t r))
    (Q : StateL2 g →L[ℝ] StateL2 g) (hQ : Q (nativeBalanced g t r)=0) : nativeConstant/16≤‖operator g-Q‖ := by
  have he : (operator g-Q) (nativeBalanced g t r)=operator g (nativeBalanced g t r) := by
    rw [sub_apply,hQ,sub_zero]
  have hc := real_inner_le_norm ((operator g-Q) (nativeBalanced g t r)) (nativeBalanced g t r)
  have ho := ContinuousLinearMap.le_opNorm (operator g-Q) (nativeBalanced g t r)
  rw [he] at hc ho
  have hh := hform.trans (hc.trans (mul_le_mul_of_nonneg_right ho (norm_nonneg _)))
  have h : (nativeConstant/16)*‖nativeBalanced g t r‖^2≤‖operator g-Q‖*‖nativeBalanced g t r‖^2 := by
    convert hh using 1 <;> ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hF)).mp h

theorem arbitrarily_large_centered_native (M : ℝ) : ∃ β : ℝ,1≤β ∧ M≤β ∧
    ∃ q : GroundData β,∃ t r : ℝ,0<‖nativeBalanced q t r‖ ∧
      (∫ U,nativeBalanced q t r U ∂q.stationary)=0 ∧
      (∀ i : Fin 3,∀ᵐ U ∂q.stationary,nativeBalanced q t r (flip i U)=nativeBalanced q t r U) ∧
      (nativeConstant/16)*‖nativeBalanced q t r‖^2≤ inner ℝ
        (operator q (nativeBalanced q t r)) (nativeBalanced q t r) ∧
      (∀ᵐ U ∂q.stationary,∀ V : State,spatialAction V=0 → ∀ a : Gauge,
        β*temporalAction U V a<M → nativeBalanced q t r U=0) := by
  have hb := coupling_diverges.eventually (eventually_ge_atTop (max M 1))
  have he := flat_distance_diverges.eventually (eventually_ge_atTop M)
  obtain ⟨x,hfamily,hbeta,hescape⟩ := (eventual_centered_family.and (hb.and he)).exists
  let q := ground (1/x^6)
  obtain ⟨hn,hf,ha⟩ := hfamily q
  refine ⟨1/x^6,(le_max_right M 1).trans hbeta,(le_max_left M 1).trans hbeta,q,x^2,x^3,hn,
    nativeBalanced_mean_zero q _ _,nativeBalanced_even q _ _,hf,?_⟩
  filter_upwards [ha] with U hU
  intro V hV a hclose
  exact hU V hV a (hclose.trans_le hescape)

theorem arbitrarily_large_centered_obstruction (M : ℝ) : ∃ β : ℝ,1≤β ∧ M≤β ∧
    ∃ q : GroundData β,∃ t r : ℝ,0<‖nativeBalanced q t r‖ ∧
      (∫ U,nativeBalanced q t r U ∂q.stationary)=0 ∧
      (∀ i : Fin 3,∀ᵐ U ∂q.stationary,nativeBalanced q t r (flip i U)=nativeBalanced q t r U) ∧
      (∀ Q : StateL2 q →L[ℝ] StateL2 q,Q (nativeBalanced q t r)=0 → nativeConstant/16≤‖operator q-Q‖) ∧
      (∀ᵐ U ∂q.stationary,∀ V : State,spatialAction V=0 → ∀ a : Gauge,
        β*temporalAction U V a<M → nativeBalanced q t r U=0) := by
  obtain ⟨β,hb,hM,q,t,r,hn,hm,he,hf,ha⟩ := arbitrarily_large_centered_native M
  exact ⟨β,hb,hM,q,t,r,hn,hm,he,fun Q hQ => balanced_error_lower q t r hn hf Q hQ,ha⟩


end OperatorDerivativeRewrite.Foundation.PeriodicQuarticCenteredObstruction
