import Foundation.PeriodicTemporalLaplaceContrast
/-! Actual two-sided conditional temporal phase and the original physical score.
Single-kernel cumulants are identified only through exact conditional masses. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicConditionalCurvatureIdentification
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicEndpointScore PeriodicPhysicalBridgeScore PeriodicTemporalLaplaceContrast
attribute [local irreducible] kernel gaugeHaar boundaryHaar spatialAction temporalAction temporalReference
attribute [local irreducible] PeriodicEndpointScore.traceSum

theorem left_right_spatial (h : ℝ) (U : State) :
    spatialAction (left h U)=spatialAction (right (-h) U) := by
  have he : left h U=gaugeAction (fun _ => SU2JointPlaquetteCubic.axis 0 h) (right (-h) U) := by
    funext e
    simp only [left,right,gaugeAction,neg_neg]
    group
  rw [he,spatial_action_invariant]

theorem partition_symmetric (β : ℝ) (U V : State) : partition β U V=partition β V U := by
  have hh := kernel_symmetric β U V
  rw [kernel_factor,kernel_factor] at hh
  have he : prefactor β U V=prefactor β V U := by unfold prefactor; congr 1; ring
  rw [he] at hh
  exact mul_left_cancel₀ (prefactor_pos β V U).ne' hh

theorem partition_left_right (β h : ℝ) (U V : State) :
    partition β (left h U) V=partition β (right (-h) U) V := by
  have hh := kernel_left_right β h U V
  rw [kernel_factor,kernel_factor] at hh
  have he : prefactor β (left h U) V=prefactor β (right (-h) U) V := by
    unfold prefactor
    rw [left_right_spatial]
  rw [he] at hh
  exact mul_left_cancel₀ (prefactor_pos β _ V).ne' hh

def centralMass (β : ℝ) (U W V : State) : ℝ :=
  ∫ ab, Real.exp (-β*PeriodicAugmentedBridge.centralAction U W (V,ab)) ∂temporalReference

theorem central_mass_factor (β : ℝ) (U W V : State) : centralMass β U W V =
    Real.exp (-β*(spatialAction V+384))*partition β U V*partition β V W := by
  have ht (ab : Gauge × Gauge) : PeriodicEndpointScore.traceSum U W (V,ab) =
      PeriodicTemporalParity.traceSum U V ab.1+PeriodicTemporalParity.traceSum V W ab.2 := by
    unfold PeriodicEndpointScore.traceSum PeriodicTemporalParity.traceSum
    rw [Finset.sum_add_distrib]
  have he (ab : Gauge × Gauge) :
      Real.exp (-β*PeriodicAugmentedBridge.centralAction U W (V,ab)) =
      Real.exp (-β*(spatialAction V+384))*
        (Real.exp (β*PeriodicTemporalParity.traceSum U V ab.1)*
          Real.exp (β*PeriodicTemporalParity.traceSum V W ab.2)) := by
    rw [PeriodicEndpointScore.central_trace,ht,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  unfold centralMass temporalReference
  simp_rw [he]
  rw [integral_const_mul]
  have hp := integral_prod_mul (μ := gaugeHaar) (ν := gaugeHaar)
    (fun a : Gauge => Real.exp (β*PeriodicTemporalParity.traceSum U V a))
    (fun b : Gauge => Real.exp (β*PeriodicTemporalParity.traceSum V W b))
  rw [hp]
  simp only [partition,PeriodicTemporalLaplaceContrast.weighted,one_mul]
  ring

theorem central_mass_pos (β : ℝ) (U W V : State) : 0 < centralMass β U W V := by
  rw [central_mass_factor]
  exact mul_pos (mul_pos (Real.exp_pos _) (partition_pos β U V)) (partition_pos β V W)

theorem bridge_central_mass (β : ℝ) (U W V : State) :
    PeriodicGroundBridge.bridgeWeight β U W V =
      Real.exp (-β*(spatialAction U/2+spatialAction W/2))*centralMass β U W V := by
  rw [← PeriodicAugmentedBridge.gauge_pair_integral]
  simp_rw [PeriodicAugmentedBridge.density_phase]
  rw [integral_const_mul]
  simpa only [centralMass,temporalReference]

theorem auxiliary_central_integral (β : ℝ) (U W V : State) (f : Gauge × Gauge → ℝ) :
    (∫ ab, f ab ∂auxiliaryLaw β U W V) =
      (∫ ab, Real.exp (-β*PeriodicAugmentedBridge.centralAction U W (V,ab))*f ab
        ∂temporalReference)/centralMass β U W V := by
  rw [auxiliary_integral,bridge_central_mass]
  simp_rw [PeriodicAugmentedBridge.density_phase,mul_assoc]
  rw [integral_const_mul]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

def conditionalMass (β : ℝ) (U V : State) (h : ℝ) : ℝ :=
  ∫ ab, Real.exp (phase β U U h (V,ab)) ∂auxiliaryLaw β U U V

theorem conditional_mass_rotated (β : ℝ) (U V : State) (h : ℝ) :
    conditionalMass β U V h=centralMass β (left h U) (right h U) V/centralMass β U U V := by
  unfold conditionalMass
  rw [auxiliary_central_integral]
  simp_rw [← central_weight_rotation]
  rfl

theorem conditional_mass_product (β : ℝ) (U V : State) (h : ℝ) :
    conditionalMass β U V h = partition β (left h U) V*partition β (left (-h) U) V/
      (partition β U V)^2 := by
  rw [conditional_mass_rotated,central_mass_factor,central_mass_factor]
  have hp : partition β (right h U) V=partition β (left (-h) U) V := by
    simpa only [neg_neg] using (partition_left_right β (-h) U V).symm
  rw [partition_symmetric β V (right h U),hp,partition_symmetric β V U]
  field_simp [Real.exp_ne_zero,(partition_pos β U V).ne']
  <;> ring

private theorem restricted_phase_measurable (β : ℝ) (U W V : State) (h : ℝ) :
    Measurable (fun ab : Gauge × Gauge => phase β U W h (V,ab)) :=
  (phase_measurable β U W h).comp (measurable_const.prodMk measurable_id)

private theorem restricted_trace_measurable (U W V : State) :
    Measurable (fun ab : Gauge × Gauge => PeriodicEndpointScore.traceSum U W (V,ab)) :=
  by
  have hc : Measurable (fun ab : Gauge × Gauge => ((V,ab) : Space)) :=
    measurable_const.prodMk measurable_id
  exact (PeriodicEndpointScore.traceSum_measurable U W).comp hc

private theorem restricted_slope_measurable (β : ℝ) (U W V : State) (h : ℝ) :
    Measurable (fun ab : Gauge × Gauge => phaseSlope β U W h (V,ab)) := by
  unfold phaseSlope
  exact (((restricted_trace_measurable U W V).const_mul _).add
    ((restricted_trace_measurable _ _ V).const_mul _)).const_mul _

private def conditionalAcceleration (β : ℝ) (U W V : State) (h : ℝ) (ab : Gauge × Gauge) : ℝ :=
  -β*PeriodicEndpointScore.traceSum (left h U) (right h W) (V,ab)

private theorem restricted_acceleration_measurable (β : ℝ) (U W V : State) (h : ℝ) :
    Measurable (conditionalAcceleration β U W V h) := (restricted_trace_measurable _ _ V).const_mul _

private theorem restricted_acceleration_bound (β : ℝ) (U W V : State) (h : ℝ) (ab : Gauge × Gauge) :
    |conditionalAcceleration β U W V h ab| ≤ 384*|β| := by
  unfold conditionalAcceleration
  rw [abs_mul,abs_neg]
  exact (mul_le_mul_of_nonneg_left (PeriodicEndpointScore.traceSum_bound _ _ (V,ab))
    (abs_nonneg β)).trans_eq (by ring)

private theorem restricted_slope_derivative (β : ℝ) (U W V : State) (h : ℝ) (ab : Gauge × Gauge) :
    HasDerivAt (fun t => phaseSlope β U W t (V,ab)) (conditionalAcceleration β U W V h ab) h := by
  have hd := ((((Real.hasDerivAt_sin h).neg).mul_const (PeriodicEndpointScore.traceSum U W (V,ab))).add
    ((Real.hasDerivAt_cos h).mul_const
      (PeriodicEndpointScore.traceSum (left (Real.pi/2) U) (right (Real.pi/2) W) (V,ab)))).const_mul β
  unfold conditionalAcceleration
  rw [PeriodicEndpointScore.traceSum_rotation]
  unfold phaseSlope
  convert hd using 1 <;> ring

private def conditionalWeighted (β : ℝ) (U W V : State) (f : Gauge × Gauge → ℝ) (h : ℝ) : ℝ :=
  ∫ ab, f ab*Real.exp (phase β U W h (V,ab)) ∂auxiliaryLaw β U W V

private def conditionalFirstWeighted (β : ℝ) (U W V : State) (f : Gauge × Gauge → ℝ) (h : ℝ) : ℝ :=
  ∫ ab, f ab*Real.exp (phase β U W h (V,ab))*phaseSlope β U W h (V,ab) ∂auxiliaryLaw β U W V

private theorem conditional_weighted_derivative (β : ℝ) (U W V : State) (f : Gauge × Gauge → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q, |f q| ≤ M) (t : ℝ) :
    HasDerivAt (conditionalWeighted β U W V f) (conditionalFirstWeighted β U W V f t) t := by
  let μ := auxiliaryLaw β U W V
  letI : IsProbabilityMeasure μ := auxiliary_probability β U W V
  let F := fun h q => f q * Real.exp (phase β U W h (V,q))
  let G := fun h q => f q * Real.exp (phase β U W h (V,q)) * phaseSlope β U W h (V,q)
  let E := Real.exp (1152 * |β|)
  have he (h : ℝ) (q : Gauge × Gauge) : Real.exp (phase β U W h (V,q)) ≤ E :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (phase_bound β U W h (V,q)))
  have hm (h : ℝ) : AEStronglyMeasurable (F h) μ :=
    (hf.mul (restricted_phase_measurable β U W V h).exp).aestronglyMeasurable
  have hi : Integrable (F t) μ := by
    apply Integrable.of_bound (hm t) (M*E)
    filter_upwards with q
    change ‖f q * Real.exp (phase β U W t (V,q))‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hb q) (he t q) (Real.exp_pos _).le hM
  have hg : AEStronglyMeasurable (G t) μ :=
    ((hf.mul (restricted_phase_measurable β U W V t).exp).mul (restricted_slope_measurable β U W V t)).aestronglyMeasurable
  have hbG : ∀ᵐ q ∂μ, ∀ h ∈ Set.Ioo (t-1) (t+1), ‖G h q‖ ≤ M*E*(768*|β|) := by
    filter_upwards with q h _
    change ‖f q * Real.exp (phase β U W h (V,q)) * phaseSlope β U W h (V,q)‖ ≤ _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul (hb q) (he h q) (Real.exp_pos _).le hM)
      (phaseSlope_bound β U W h (V,q)) (abs_nonneg _)
      (mul_nonneg hM (Real.exp_pos _).le)
  have hd : ∀ᵐ q ∂μ, ∀ h ∈ Set.Ioo (t-1) (t+1), HasDerivAt (F · q) (G h q) h := by
    filter_upwards with q h _
    simpa only [F, G, Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      (phase_hasDerivAt β U W h (V,q)).exp.const_mul (f q)
  obtain ⟨_, hh⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith) (by linarith)) (Eventually.of_forall hm) hi hg hbG
    (integrable_const _) hd
  exact hh

private theorem conditional_first_derivative (β : ℝ) (U W V : State) (f : Gauge × Gauge → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q, |f q| ≤ M) (t : ℝ) :
    HasDerivAt (conditionalFirstWeighted β U W V f)
      (∫ q, f q * Real.exp (phase β U W t (V,q)) *
        ((phaseSlope β U W t (V,q))^2 + conditionalAcceleration β U W V t q)
        ∂auxiliaryLaw β U W V) t := by
  let μ := auxiliaryLaw β U W V
  letI : IsProbabilityMeasure μ := auxiliary_probability β U W V
  let F := fun h q => f q * Real.exp (phase β U W h (V,q)) * phaseSlope β U W h (V,q)
  let G := fun h q => f q * Real.exp (phase β U W h (V,q)) *
    ((phaseSlope β U W h (V,q))^2 + conditionalAcceleration β U W V h q)
  let E := Real.exp (1152 * |β|)
  let B := 768 * |β|
  have he (h : ℝ) (q : Gauge × Gauge) : Real.exp (phase β U W h (V,q)) ≤ E :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (phase_bound β U W h (V,q)))
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (abs_nonneg _)
  have hm (h : ℝ) : AEStronglyMeasurable (F h) μ :=
    ((hf.mul (restricted_phase_measurable β U W V h).exp).mul (restricted_slope_measurable β U W V h)).aestronglyMeasurable
  have hi : Integrable (F t) μ := by
    apply Integrable.of_bound (hm t) (M*E*B)
    filter_upwards with q
    change ‖f q * Real.exp (phase β U W t (V,q)) * phaseSlope β U W t (V,q)‖ ≤ _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul (hb q) (he t q) (Real.exp_pos _).le hM)
      (phaseSlope_bound β U W t (V,q)) (abs_nonneg _) (mul_nonneg hM (Real.exp_pos _).le)
  have hg : AEStronglyMeasurable (G t) μ :=
    ((hf.mul (restricted_phase_measurable β U W V t).exp).mul
      (((restricted_slope_measurable β U W V t).pow_const 2).add
        (restricted_acceleration_measurable β U W V t))).aestronglyMeasurable
  have hq (h : ℝ) (q : Gauge × Gauge) :
      |(phaseSlope β U W h (V,q))^2 + conditionalAcceleration β U W V h q| ≤ B^2+B := by
    have hs := phaseSlope_bound β U W h (V,q)
    have ha := restricted_acceleration_bound β U W V h q
    have hp : (phaseSlope β U W h (V,q))^2 ≤ B^2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hB).2 (show |phaseSlope β U W h (V,q)| ≤ B from hs)
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (sq_nonneg _)]
    dsimp only [B] at *
    linarith [abs_nonneg β]
  have hbG : ∀ᵐ q ∂μ, ∀ h ∈ Set.Ioo (t-1) (t+1), ‖G h q‖ ≤ M*E*(B^2+B) := by
    filter_upwards with q h _
    change ‖f q * Real.exp (phase β U W h (V,q)) * _‖ ≤ _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul (hb q) (he h q) (Real.exp_pos _).le hM)
      (hq h q) (abs_nonneg _) (mul_nonneg hM (Real.exp_pos _).le)
  have hd : ∀ᵐ q ∂μ, ∀ h ∈ Set.Ioo (t-1) (t+1), HasDerivAt (F · q) (G h q) h := by
    filter_upwards with q h _
    have hh := ((phase_hasDerivAt β U W h (V,q)).exp.const_mul (f q)).mul
      (restricted_slope_derivative β U W V h q)
    convert hh using 1 <;> dsimp [F, G] <;> ring
  obtain ⟨_, hh⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith) (by linarith)) (Eventually.of_forall hm) hi hg hbG
    (integrable_const _) hd
  exact hh


private theorem conditional_mass_first (β : ℝ) (U V : State) (h : ℝ) :
    HasDerivAt (conditionalMass β U V) (conditionalFirstWeighted β U U V (fun _ => 1) h) h := by
  have hh := conditional_weighted_derivative β U U V (fun _ => 1) measurable_const 1
    (by norm_num) (fun _ => by norm_num) h
  have he : conditionalWeighted β U U V (fun _ => 1)=conditionalMass β U V := by
    funext t
    simp only [conditionalWeighted,conditionalMass,one_mul]
  rw [he] at hh
  exact hh

theorem conditional_mass_even (β : ℝ) (U V : State) (h : ℝ) :
    conditionalMass β U V (-h)=conditionalMass β U V h := by
  rw [conditional_mass_product,conditional_mass_product]
  simp only [neg_neg]
  ring

theorem conditional_linear_zero (β : ℝ) (U V : State) :
    (∫ ab, β*direction U U (V,ab) ∂auxiliaryLaw β U U V)=0 := by
  have hd := conditional_mass_first β U V 0
  have hv : conditionalFirstWeighted β U U V (fun _ => 1) 0 =
      ∫ ab, β*direction U U (V,ab) ∂auxiliaryLaw β U U V := by
    simp [conditionalFirstWeighted,phase,phaseSlope,direction]
  rw [hv] at hd
  have hd0 : HasDerivAt (conditionalMass β U V)
      (∫ ab, β*direction U U (V,ab) ∂auxiliaryLaw β U U V) (-(0 : ℝ)) := by
    simpa only [neg_zero] using hd
  have hn := hd0.comp 0 (hasDerivAt_neg (0 : ℝ))
  have he : (fun h => conditionalMass β U V (-h))=conditionalMass β U V :=
    funext (conditional_mass_even β U V)
  change HasDerivAt (fun h => conditionalMass β U V (-h)) _ 0 at hn
  rw [he] at hn
  have hu := hd.unique hn
  nlinarith

theorem conditional_mass_second (β : ℝ) (U V : State) :
    HasDerivAt (deriv (conditionalMass β U V))
      (∫ ab, PeriodicEndpointSecondResponse.rawCurvature β U U (V,ab) ∂auxiliaryLaw β U U V) 0 := by
  have he : deriv (conditionalMass β U V)=conditionalFirstWeighted β U U V (fun _ => 1) :=
    funext (fun h => (conditional_mass_first β U V h).deriv)
  rw [he]
  have hh := conditional_first_derivative β U U V (fun _ => 1) measurable_const 1
    (by norm_num) (fun _ => by norm_num) 0
  have hp (ab : Gauge × Gauge) : phase β U U 0 (V,ab)=0 := by simp [phase]
  have hs (ab : Gauge × Gauge) : phaseSlope β U U 0 (V,ab)=β*direction U U (V,ab) := by
    simp [phaseSlope,direction]
  have ha (ab : Gauge × Gauge) : conditionalAcceleration β U U V 0 ab =
      -β*PeriodicEndpointScore.traceSum U U (V,ab) := by
    unfold conditionalAcceleration
    rw [PeriodicEndpointScore.traceSum_rotation]
    simp
  simpa only [one_mul,hp,hs,ha,Real.exp_zero,mul_one,
    PeriodicEndpointSecondResponse.rawCurvature,sub_eq_add_neg,neg_mul] using hh

private theorem axis_zero : SU2JointPlaquetteCubic.axis 0 0=1 := by
  apply Subtype.ext
  change (SU2JointPlaquetteCubic.axis 0 0 : SU2TraceHessianModel.M2)=1
  simp [SU2AxisMatrixJets.axis_matrix_formula]

private theorem left_zero (U : State) : left 0 U=U := by
  funext e
  simp only [left,axis_zero,one_mul]

private theorem opposite_product_second (A B C : ℝ → ℝ)
    (hA : ∀ t, HasDerivAt A (B t) t) (hB : ∀ t, HasDerivAt B (C t) t)
    (h0 : A 0 ≠ 0) : HasDerivAt (deriv (fun h => A h*A (-h)/(A 0)^2))
      (2*(C 0/A 0-(B 0/A 0)^2)) 0 := by
  let G := fun h => (B h*A (-h)-A h*B (-h))/(A 0)^2
  have hg (t : ℝ) : HasDerivAt (fun h => A h*A (-h)/(A 0)^2) (G t) t := by
    have hh := ((hA t).mul ((hA (-t)).scomp t (hasDerivAt_neg t))).div_const ((A 0)^2)
    have hv : G t=(B t*A (-t)+A t*((-1 : ℝ) • B (-t)))/(A 0)^2 := by
      dsimp only [G]
      simp only [smul_eq_mul]
      ring
    rw [hv]
    exact hh
  have he : deriv (fun h => A h*A (-h)/(A 0)^2)=G := funext (fun t => (hg t).deriv)
  rw [he]
  have ha : HasDerivAt (fun h => A (-h)) (-B 0) 0 := by
    simpa only [Function.comp_def,neg_zero,neg_one_smul] using
      (hA (-(0 : ℝ))).scomp 0 (hasDerivAt_neg (0 : ℝ))
  have hb : HasDerivAt (fun h => B (-h)) (-C 0) 0 := by
    simpa only [Function.comp_def,neg_zero,neg_one_smul] using
      (hB (-(0 : ℝ))).scomp 0 (hasDerivAt_neg (0 : ℝ))
  have hn := (((hB 0).mul ha).sub ((hA 0).mul hb)).div_const ((A 0)^2)
  have hv : 2*(C 0/A 0-(B 0/A 0)^2) =
      ((C 0*A (-0)+B 0*(-B 0))-(B 0*B (-0)+A 0*(-C 0)))/(A 0)^2 := by
    simp only [neg_zero]
    field_simp [h0]
    <;> ring
  rw [hv]
  exact hn

theorem conditional_mass_second_kernel (β : ℝ) (U V : State) :
    HasDerivAt (deriv (conditionalMass β U V)) (2*logCurvature β U V 0) 0 := by
  let A := fun h => partition β (left h U) V
  have he : conditionalMass β U V=(fun h => A h*A (-h)/(A 0)^2) := by
    funext h
    rw [conditional_mass_product]
    dsimp only [A]
    rw [left_zero]
  rw [he]
  have hh := opposite_product_second A (firstJet β U V) (secondJet β U V)
    (partition_derivative β U V) (firstJet_derivative β U V)
    (by simpa only [A,left_zero] using (partition_pos β U V).ne')
  exact hh

theorem conditional_rawCurvature (β : ℝ) (U V : State) :
    (∫ ab, PeriodicEndpointSecondResponse.rawCurvature β U U (V,ab) ∂auxiliaryLaw β U U V) =
      2*logCurvature β U V 0 :=
  (conditional_mass_second β U V).unique (conditional_mass_second_kernel β U V)

private theorem physical_second_diagonal_expansion (β : ℝ) (U V : State) :
    PeriodicEndpointSecondResponse.physicalSecond β U U V = 2*logCurvature β U V 0+
      2*(∫ q, β*direction U U q ∂PeriodicAugmentedBridge.law β U U)^2-
      ∫ q, PeriodicEndpointSecondResponse.rawCurvature β U U q ∂PeriodicAugmentedBridge.law β U U := by
  let μ := auxiliaryLaw β U U V
  letI : IsProbabilityMeasure μ := auxiliary_probability β U U V
  let m := ∫ q, β*direction U U q ∂PeriodicAugmentedBridge.law β U U
  let n := ∫ q, PeriodicEndpointSecondResponse.rawCurvature β U U q ∂PeriodicAugmentedBridge.law β U U
  let R := fun ab : Gauge × Gauge => β*direction U U (V,ab)
  let Q := fun ab : Gauge × Gauge => PeriodicEndpointSecondResponse.rawCurvature β U U (V,ab)
  have hR : Integrable R μ := by
    apply Integrable.of_bound (((restricted_trace_measurable (left (Real.pi/2) U)
      (right (Real.pi/2) U) V).const_mul β).aestronglyMeasurable) (384*|β|)
    filter_upwards with ab
    change ‖β*direction U U (V,ab)‖ ≤ _
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_left (PeriodicEndpointScore.traceSum_bound _ _ (V,ab))
      (abs_nonneg β)).trans_eq (by ring)
  have hQ : Integrable Q μ := by
    have hm : Measurable Q :=
      (PeriodicEndpointSecondResponse.rawCurvature_measurable β U U).comp
        (measurable_const.prodMk measurable_id)
    apply Integrable.of_bound hm.aestronglyMeasurable ((384*|β|)^2+384*|β|)
    filter_upwards with ab
    simpa only [Real.norm_eq_abs,Q] using PeriodicEndpointSecondResponse.rawCurvature_bound β U U (V,ab)
  have he (ab : Gauge × Gauge) : PeriodicEndpointSecondResponse.secondScore β U U (V,ab) =
      (Q ab-2*m*R ab)+(2*m^2-n) := by
    unfold PeriodicEndpointSecondResponse.secondScore
    dsimp only [Q,R,m,n]
    ring
  unfold PeriodicEndpointSecondResponse.physicalSecond
  simp_rw [he]
  change (∫ ab, (Q ab-2*m*R ab)+(2*m^2-n) ∂μ)=2*logCurvature β U V 0+2*m^2-n
  have hmul : Integrable (fun ab => (2*m)*R ab) μ := hR.const_mul (2*m)
  have hsub : Integrable (fun ab => Q ab-(2*m)*R ab) μ := hQ.sub hmul
  rw [integral_add hsub (integrable_const (2*m^2-n)),
    integral_sub hQ hmul,integral_const_mul,integral_const]
  have hz : (∫ ab, R ab ∂μ)=0 := conditional_linear_zero β U V
  have hq : (∫ ab, Q ab ∂μ)=2*logCurvature β U V 0 := conditional_rawCurvature β U V
  rw [hz,hq]
  simp only [mul_zero,sub_zero,probReal_univ,one_smul]
  ring

/-- Exact identification with the ORIGINAL two-sided physical second score.
Both global normalization terms are retained in the expansion and cancel only
in this pointwise contrast. This is not an auxiliary-energy promotion. -/
theorem physical_second_contrast (β : ℝ) (U V W : State) :
    PeriodicEndpointSecondResponse.physicalSecond β U U V-
      PeriodicEndpointSecondResponse.physicalSecond β U U W =
        2*(logCurvature β U V 0-logCurvature β U W 0) := by
  rw [physical_second_diagonal_expansion,physical_second_diagonal_expansion]
  ring

theorem left_add (s t : ℝ) (U : State) : left s (left t U)=left (s+t) U := by
  funext e
  simp only [left]
  rw [← mul_assoc,PeriodicWindingEndpointResponse.axis_add]

theorem cTrace_translate (s t : ℝ) (U V : State) (a : Gauge) :
    cTrace s (left t U) V a=cTrace (s+t) U V a := by rw [cTrace,cTrace,left_add]

theorem dTrace_translate (s t : ℝ) (U V : State) (a : Gauge) :
    dTrace s (left t U) V a=dTrace (s+t) U V a := by
  rw [dTrace_shift,dTrace_shift,left_add]
  congr 2
  ring

theorem firstJet_translate (β s t : ℝ) (U V : State) :
    firstJet β (left t U) V s=firstJet β U V (s+t) := by
  unfold firstJet
  simp_rw [cTrace_translate,dTrace_translate]

theorem secondJet_translate (β s t : ℝ) (U V : State) :
    secondJet β (left t U) V s=secondJet β U V (s+t) := by
  unfold secondJet
  simp_rw [cTrace_translate,dTrace_translate]

theorem logCurvature_translate (β s t : ℝ) (U V : State) :
    logCurvature β (left t U) V s=logCurvature β U V (s+t) := by
  unfold logCurvature
  rw [firstJet_translate,secondJet_translate,left_add]

/-- Strict separation of the ORIGINAL physical second score at a translated
point of the original quarter-turn orbit. This is not yet native L2 positivity. -/
theorem eventual_physical_second_separation : ∀ᶠ β : ℝ in 𝓝[≠] 0,
    ∃ t ∈ Set.Ioo (-Real.pi/4) (Real.pi/4),
      PeriodicEndpointSecondResponse.physicalSecond β (PeriodicTemporalCycleMoment.orbit t)
        (PeriodicTemporalCycleMoment.orbit t) 1-
      PeriodicEndpointSecondResponse.physicalSecond β (PeriodicTemporalCycleMoment.orbit t)
        (PeriodicTemporalCycleMoment.orbit t) (PeriodicCenterSeam.flip 1 1) < 0 := by
  filter_upwards [eventual_negative_log_curvature] with β hh
  obtain ⟨t,ht,hneg⟩ := hh
  refine ⟨t,ht,?_⟩
  rw [physical_second_contrast]
  change 2*(logCurvature β (left t PeriodicEndpointFibreWitness.leftEndpoint) 1 0-
    logCurvature β (left t PeriodicEndpointFibreWitness.leftEndpoint) (PeriodicCenterSeam.flip 1 1) 0)<0
  rw [logCurvature_translate,logCurvature_translate,zero_add]
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicConditionalCurvatureIdentification
