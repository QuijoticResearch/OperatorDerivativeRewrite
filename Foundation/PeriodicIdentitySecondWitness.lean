import Foundation.PeriodicEndpointSecondResponse
/-! A centered winding test for the actual second Wilson response.
An identity left endpoint and pure-gauge right compensator give a different
tangent family from the earlier non-gauge exchange-null test. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicIdentitySecondWitness
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicEndpointScore PeriodicWindingEndpointResponse PeriodicPhysicalFisherWitness
attribute [local irreducible] kernel boundaryHaar gaugeHaar spatialAction temporalAction

def flatPath (h : ℝ) : State := left h 1
def H (β h : ℝ) (V : State) : ℝ := kernel β (flatPath h) V

theorem flat_action (h : ℝ) : spatialAction (flatPath h) = 0 := by
  have hw (p : SpatialFace) : spatialWord (flatPath h) p = 1 := by
    simp only [spatialWord, flatPath, left, Pi.one_apply, mul_one]
    group
  unfold spatialAction
  simp only [hw, SU2OpenLinkGaugeObstruction.halfTrace_one, sub_self, Finset.sum_const_zero]

theorem flat_flip (h : ℝ) : PeriodicEndpointWard.field PeriodicEndpointWard.flip (flatPath h) =
    flatPath (-h) := by
  funext e
  simp only [PeriodicEndpointWard.field, gaugeAction, flatPath, left, Pi.one_apply, mul_one]
  exact PeriodicEndpointWard.flip_axis h

theorem H_even (β h : ℝ) (V : State) : H β h V = H β (-h) V := by
  unfold H
  rw [← flat_flip]
  exact (kernel_left_invariant β (fun _ => PeriodicEndpointWard.flip) (flatPath h) V).symm

theorem bridge_square (β h : ℝ) (V : State) :
    PeriodicGroundBridge.bridgeWeight β (left h 1) (right h 1) V = (H β h V)^2 := by
  have hr : right h (1 : State) = flatPath (-h) := by
    funext e
    simp only [right, flatPath, left, Pi.one_apply, one_mul, mul_one]
  unfold PeriodicGroundBridge.bridgeWeight
  rw [hr, kernel_symmetric β V (flatPath (-h))]
  change H β h V * H β (-h) V = (H β h V)^2
  rw [← H_even, pow_two]

theorem flat_winding (h : ℝ) : PeriodicCenteredHolonomy.first (flatPath h) = Real.cos (4*h) := by
  unfold PeriodicCenteredHolonomy.first PeriodicSpatialHolonomy.winding flatPath left
  simp only [Pi.one_apply, mul_one, axis_add]
  rw [show h+h+h+h=4*h by ring, FourCubeWilsonCubic.axis_trace]

def counterweight (β : ℝ) (V : State) : ℝ := Real.exp (β*spatialAction V/2)

theorem counterweight_measurable (β : ℝ) : Measurable (counterweight β) :=
  ((spatial_action_measurable.const_mul β).div_const 2).exp

theorem counterweight_bound (β : ℝ) (V : State) : |counterweight β V| ≤ Real.exp (192*|β|) := by
  rw [counterweight, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_right (le_abs_self β) (spatial_action_bounds V).1
  have h2 := mul_le_mul_of_nonneg_left (spatial_action_bounds V).2 (abs_nonneg β)
  linarith

theorem counterweight_gauge (β : ℝ) (a : Gauge) (V : State) :
    counterweight β (gaugeAction a V) = counterweight β V := by
  unfold counterweight
  rw [spatial_action_invariant]

theorem mass_moment (β : ℝ) (hb : 0 ≤ β) (U : State) :
    (∫ V, kernel β U V * counterweight β V ∂boundaryHaar) =
      CubeHaarUpper.laplace β^192 * PeriodicPhysicalKineticReduction.multiplier β U := by
  have hi : Integrable (counterweight β) boundaryHaar :=
    Integrable.of_bound (counterweight_measurable β).aestronglyMeasurable _
      (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using counterweight_bound β V))
  rw [PeriodicPhysicalKineticReduction.invariant_factorization β hb U _
    (counterweight_measurable β) hi (counterweight_gauge β)]
  have he (V : State) : PeriodicPhysicalKineticReduction.multiplier β V * counterweight β V = 1 := by
    unfold PeriodicPhysicalKineticReduction.multiplier counterweight
    rw [← Real.exp_add, show -β*spatialAction V/2+β*spatialAction V/2=0 by ring, Real.exp_zero]
  simp_rw [he]
  unfold PeriodicPhysicalKineticReduction.kinetic
  simp only [mul_one]
  rw [PeriodicPhysicalKineticReduction.kinetic_mass β hb U, mul_one]

def centered (β : ℝ) (V : State) : ℝ := counterweight β V *
  (PeriodicCenteredHolonomy.first V - SU2WilsonConvolution.coefficient β^4)

private theorem coefficient_bound (β : ℝ) : |SU2WilsonConvolution.coefficient β| ≤ 1 := by
  letI := SU2WilsonConvolution.increment_probability β
  simpa only [SU2WilsonConvolution.coefficient, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := SU2WilsonConvolution.increment β)
      (f := halfTrace) (C := 1) (ae_of_all _ (fun A => by
        simpa only [Real.norm_eq_abs] using halfTrace_bound A))

theorem centered_measurable (β : ℝ) : Measurable (centered β) :=
  (counterweight_measurable β).mul (PeriodicCenteredHolonomy.first_measurable.sub measurable_const)

theorem centered_bound (β : ℝ) (V : State) : |centered β V| ≤ 2*Real.exp (192*|β|) := by
  have ha : |SU2WilsonConvolution.coefficient β^4| ≤ 1 := by
    simpa only [abs_pow, one_pow] using pow_le_pow_left₀ (abs_nonneg _)
      (coefficient_bound β) 4
  have hw := halfTrace_bound (PeriodicSpatialHolonomy.winding V PeriodicCenteredHolonomy.origin 0)
  change |PeriodicCenteredHolonomy.first V| ≤ 1 at hw
  have hs : |PeriodicCenteredHolonomy.first V-SU2WilsonConvolution.coefficient β^4| ≤ 2 := by
    apply (abs_sub _ _).trans
    change |PeriodicCenteredHolonomy.first V|+|SU2WilsonConvolution.coefficient β^4| ≤ 2
    linarith
  unfold centered
  rw [abs_mul]
  have hh := mul_le_mul (counterweight_bound β V) hs (abs_nonneg _) (Real.exp_pos _).le
  linarith

theorem centered_gauge (β : ℝ) (a : Gauge) (V : State) :
    centered β (gaugeAction a V) = centered β V := by
  unfold centered PeriodicCenteredHolonomy.first
  rw [counterweight_gauge, PeriodicSpatialHolonomy.trace_gauge]

theorem centered_moment (β : ℝ) (hb : 0 ≤ β) (h : ℝ) :
    (∫ V, H β h V * centered β V ∂boundaryHaar) =
      CubeHaarUpper.laplace β^192 * SU2WilsonConvolution.coefficient β^4 *
        (Real.cos (4*h)-1) := by
  have hw : Integrable (fun V => kernel β (flatPath h) V * weightedWinding β V) boundaryHaar := by
    apply Integrable.of_bound ((kernel_joint_measurable β).comp
      (measurable_const.prodMk measurable_id) |>.mul (weightedWinding_measurable β)).aestronglyMeasurable
      (Real.exp (768*|β|)*Real.exp (192*|β|))
    filter_upwards with V
    change ‖kernel β (flatPath h) V * weightedWinding β V‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (kernel_positive β _ _)]
    exact mul_le_mul (kernel_bounds β _ _).2 (weightedWinding_bound β V)
      (abs_nonneg _) (Real.exp_pos _).le
  have hm : Integrable (fun V => kernel β (flatPath h) V * counterweight β V) boundaryHaar := by
    apply Integrable.of_bound ((kernel_joint_measurable β).comp
      (measurable_const.prodMk measurable_id) |>.mul (counterweight_measurable β)).aestronglyMeasurable
      (Real.exp (768*|β|)*Real.exp (192*|β|))
    filter_upwards with V
    change ‖kernel β (flatPath h) V * counterweight β V‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (kernel_positive β _ _)]
    exact mul_le_mul (kernel_bounds β _ _).2 (counterweight_bound β V)
      (abs_nonneg _) (Real.exp_pos _).le
  have he : (fun V => H β h V * centered β V) =
      (fun V => kernel β (flatPath h) V * weightedWinding β V -
        SU2WilsonConvolution.coefficient β^4 * (kernel β (flatPath h) V * counterweight β V)) := by
    funext V
    dsimp only [H, centered, weightedWinding, counterweight]
    ring
  rw [he, integral_sub hw (hm.const_mul _), integral_const_mul,
    kernel_winding β hb, mass_moment β hb]
  rw [flat_winding, PeriodicPhysicalKineticReduction.multiplier, flat_action]
  simp only [mul_zero, zero_div, Real.exp_zero, mul_one]
  ring

def compensator : State := fun _ => PeriodicEndpointWard.flip

private theorem flip_commute (h : ℝ) :
    PeriodicEndpointWard.flip * SU2JointPlaquetteCubic.axis 0 h =
      SU2JointPlaquetteCubic.axis 0 (-h) * PeriodicEndpointWard.flip := by
  have hh := congrArg (fun A => A * PeriodicEndpointWard.flip) (PeriodicEndpointWard.flip_axis h)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

/-- The prescribed right endpoint motion is entirely a gauge orbit for this
explicit compensator. It is not frozen by ignoring its derivative. -/
theorem right_compensator (h : ℝ) :
    right h compensator = gaugeAction (fun _ => SU2JointPlaquetteCubic.axis 0 (h/2)) compensator := by
  funext e
  change PeriodicEndpointWard.flip * SU2JointPlaquetteCubic.axis 0 (-h) =
    SU2JointPlaquetteCubic.axis 0 (h/2) * PeriodicEndpointWard.flip *
      (SU2JointPlaquetteCubic.axis 0 (h/2))⁻¹
  symm
  rw [SU2AxisMatrixJets.axis_inv, mul_assoc, flip_commute, neg_neg, ← mul_assoc, axis_add]
  rw [show h/2+h/2=h by ring]
  simpa only [neg_neg] using (flip_commute (-h)).symm

theorem right_kernel (β h : ℝ) (V : State) :
    kernel β V (right h compensator) = kernel β V compensator := by
  rw [right_compensator, kernel_right_invariant]

def massProbe (β : ℝ) (V : State) : ℝ := counterweight β V / kernel β V compensator
def probe (β : ℝ) (V : State) : ℝ := centered β V / kernel β V compensator

theorem massProbe_measurable (β : ℝ) : Measurable (massProbe β) :=
  (counterweight_measurable β).div ((kernel_joint_measurable β).comp
    (measurable_id.prodMk measurable_const))

theorem probe_measurable (β : ℝ) : Measurable (probe β) :=
  (centered_measurable β).div ((kernel_joint_measurable β).comp
    (measurable_id.prodMk measurable_const))

private theorem quotient_bound (β : ℝ) (V : State) (x M : ℝ) (hx : |x| ≤ M) :
    |x / kernel β V compensator| ≤ M / Real.exp (-768*|β|) := by
  rw [abs_div, abs_of_pos (kernel_positive β V compensator)]
  exact (div_le_div_of_nonneg_right hx (kernel_positive β V compensator).le).trans
    (div_le_div_of_nonneg_left (abs_nonneg _ |>.trans hx) (Real.exp_pos _)
      (kernel_bounds β V compensator).1)

theorem massProbe_bound (β : ℝ) (V : State) : |massProbe β V| ≤ Real.exp (960*|β|) := by
  have hh := quotient_bound β V _ _ (counterweight_bound β V)
  change |massProbe β V| ≤ _ at hh
  have he : Real.exp (192*|β|) / Real.exp (-768*|β|) = Real.exp (960*|β|) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  exact hh.trans_eq he

theorem probe_bound (β : ℝ) (V : State) : |probe β V| ≤ 2*Real.exp (960*|β|) := by
  have hh := quotient_bound β V _ _ (centered_bound β V)
  change |probe β V| ≤ _ at hh
  have he : (2*Real.exp (192*|β|)) / Real.exp (-768*|β|) = 2*Real.exp (960*|β|) := by
    rw [mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring
  exact hh.trans_eq he

theorem massProbe_gauge (β : ℝ) (a : Gauge) (V : State) :
    massProbe β (gaugeAction a V) = massProbe β V := by
  unfold massProbe
  rw [counterweight_gauge, kernel_left_invariant]

theorem probe_gauge (β : ℝ) (a : Gauge) (V : State) :
    probe β (gaugeAction a V) = probe β V := by
  unfold probe
  rw [centered_gauge, kernel_left_invariant]

theorem massProbe_expectation (β : ℝ) (hb : 0 ≤ β) (h : ℝ) :
    (∫ V, massProbe β V ∂PeriodicGroundBridge.law β (left h 1) (right h compensator)) =
      CubeHaarUpper.laplace β^192 /
        PeriodicGroundBridge.normalizer β (left h 1) (right h compensator) := by
  rw [PeriodicGroundBridge.integral_formula]
  have he : (fun V => PeriodicGroundBridge.bridgeWeight β (left h 1) (right h compensator) V *
      massProbe β V) = (fun V => H β h V * counterweight β V) := by
    funext V
    rw [PeriodicGroundBridge.bridgeWeight, right_kernel]
    dsimp only [massProbe, H, flatPath]
    field_simp [(kernel_positive β V compensator).ne']
  rw [he]
  simp only [H]
  rw [mass_moment β hb, PeriodicPhysicalKineticReduction.multiplier, flat_action]
  simp only [mul_zero, zero_div, Real.exp_zero, mul_one]

theorem probe_expectation (β : ℝ) (hb : 0 ≤ β) (h : ℝ) :
    (∫ V, probe β V ∂PeriodicGroundBridge.law β (left h 1) (right h compensator)) =
      (CubeHaarUpper.laplace β^192 * SU2WilsonConvolution.coefficient β^4 *
        (Real.cos (4*h)-1)) /
          PeriodicGroundBridge.normalizer β (left h 1) (right h compensator) := by
  rw [PeriodicGroundBridge.integral_formula]
  have he : (fun V => PeriodicGroundBridge.bridgeWeight β (left h 1) (right h compensator) V *
      probe β V) = (fun V => H β h V * centered β V) := by
    funext V
    rw [PeriodicGroundBridge.bridgeWeight, right_kernel]
    dsimp only [probe, H, flatPath]
    field_simp [(kernel_positive β V compensator).ne']
  rw [he, centered_moment β hb]

/-- Exact factorization through an ACTUAL normalized expectation. The moving
partition function has not been replaced, canceled incorrectly or differentiated away. -/
theorem expectation_relation (β : ℝ) (hb : 0 ≤ β) :
    (fun h => ∫ V, probe β V ∂PeriodicGroundBridge.law β (left h 1) (right h compensator)) =
      (fun h => (∫ V, massProbe β V ∂PeriodicGroundBridge.law β (left h 1) (right h compensator)) *
        (SU2WilsonConvolution.coefficient β^4 * (Real.cos (4*h)-1))) := by
  funext h
  rw [probe_expectation β hb, massProbe_expectation β hb]
  ring

private theorem axis_zero : SU2JointPlaquetteCubic.axis 0 0 = 1 := by
  apply Subtype.ext
  change (SU2JointPlaquetteCubic.axis 0 0 : SU2TraceHessianModel.M2) = 1
  simp [SU2AxisMatrixJets.axis_matrix_formula]

private theorem left_zero (U : State) : left 0 U = U := by
  funext e
  simp only [left, axis_zero, one_mul]

private theorem right_zero (U : State) : right 0 U = U := by
  funext e
  simp only [right, neg_zero, axis_zero, mul_one]

theorem probe_mean_zero (β : ℝ) (hb : 0 ≤ β) :
    (∫ V, probe β V ∂PeriodicGroundBridge.law β 1 compensator) = 0 := by
  have hh := probe_expectation β hb 0
  simpa only [left_zero, right_zero, mul_zero, Real.cos_zero, sub_self, zero_div] using hh

private theorem left_add (t h : ℝ) (U : State) : left t (left h U) = left (t+h) U := by
  funext e
  unfold left
  rw [← mul_assoc, axis_add]

private theorem right_add (t h : ℝ) (U : State) : right t (right h U) = right (t+h) U := by
  funext e
  unfold right
  rw [mul_assoc, axis_add]
  congr 2
  ring

private theorem expectation_differentiable (β : ℝ) (U W : State) (f : State → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) :
    Differentiable ℝ (fun h => ∫ V, f V ∂PeriodicGroundBridge.law β (left h U) (right h W)) := by
  intro h
  let F := fun s => ∫ V, f V ∂PeriodicGroundBridge.law β (left s U) (right s W)
  let c := ∫ V, f V * PeriodicPhysicalBridgeScore.physicalScore β (left h U) (right h W) V
    ∂PeriodicGroundBridge.law β (left h U) (right h W)
  have h0 : HasDerivAt (fun t => F (t+h)) c 0 := by
    have hd := PeriodicPhysicalBridgeScore.physical_derivative β (left h U) (right h W) f hf M hM hb
    convert hd using 1
    funext t
    dsimp only [F]
    rw [left_add, right_add]
  have h0' : HasDerivAt (fun t => F (t+h)) c (h-h) := by simpa only [sub_self] using h0
  have hh := h0'.comp h (h := fun x : ℝ => x-h) ((hasDerivAt_id h).sub_const h)
  have hh' : HasDerivAt F c h := by simpa only [Function.comp_def, sub_add_cancel, mul_one] using hh
  exact hh'.differentiableAt

private def trig (β h : ℝ) : ℝ := SU2WilsonConvolution.coefficient β^4 * (Real.cos (4*h)-1)

private theorem trig_derivative (β h : ℝ) :
    HasDerivAt (trig β) (-4*SU2WilsonConvolution.coefficient β^4*Real.sin (4*h)) h := by
  unfold trig
  have hd := (((hasDerivAt_id h).const_mul 4).cos.sub_const 1).const_mul
    (SU2WilsonConvolution.coefficient β^4)
  simp only [id_eq] at hd
  convert hd using 1 <;> ring

private theorem trig_second (β : ℝ) :
    HasDerivAt (fun h => -4*SU2WilsonConvolution.coefficient β^4*Real.sin (4*h))
      (-16*SU2WilsonConvolution.coefficient β^4) 0 := by
  convert (((hasDerivAt_id (0 : ℝ)).const_mul 4).sin).const_mul
    (-4*SU2WilsonConvolution.coefficient β^4) using 1 <;> norm_num <;> ring

/-- Exact, non-surrogate second response for the fixed admissible winding
probe and pure-gauge right compensator. The original normalizer remains. -/
theorem probe_second_derivative (β : ℝ) (hb : 0 ≤ β) :
    HasDerivAt (deriv (fun h => ∫ V, probe β V
      ∂PeriodicGroundBridge.law β (left h 1) (right h compensator)))
      (-16*CubeHaarUpper.laplace β^192*SU2WilsonConvolution.coefficient β^4 /
        PeriodicGroundBridge.normalizer β 1 compensator) 0 := by
  let G := fun h => ∫ V, massProbe β V ∂PeriodicGroundBridge.law β (left h 1) (right h compensator)
  let F := fun h => ∫ V, probe β V ∂PeriodicGroundBridge.law β (left h 1) (right h compensator)
  have hG := PeriodicPhysicalBridgeScore.physical_derivative β 1 compensator (massProbe β)
    (massProbe_measurable β) (Real.exp (960*|β|)) (Real.exp_pos _).le (massProbe_bound β)
  have hG2 := PeriodicEndpointSecondResponse.physical_second_derivative β 1 compensator (massProbe β)
    (massProbe_measurable β) (Real.exp (960*|β|)) (Real.exp_pos _).le (massProbe_bound β)
  have hGD : Differentiable ℝ G := expectation_differentiable β 1 compensator (massProbe β)
    (massProbe_measurable β) (Real.exp (960*|β|)) (Real.exp_pos _).le (massProbe_bound β)
  have hEF : F = (fun h => G h * trig β h) := expectation_relation β hb
  have hD : deriv F = (fun h => deriv G h * trig β h +
      G h * (-4*SU2WilsonConvolution.coefficient β^4*Real.sin (4*h))) := by
    funext h
    rw [hEF]
    exact ((hGD h).hasDerivAt.mul (trig_derivative β h)).deriv
  have hG0 : G 0 = CubeHaarUpper.laplace β^192 / PeriodicGroundBridge.normalizer β 1 compensator := by
    simpa only [G, left_zero, right_zero] using massProbe_expectation β hb 0
  have hh := (hG2.mul (trig_derivative β 0)).add (hG.mul (trig_second β))
  change HasDerivAt (deriv F) _ 0
  rw [hD]
  convert hh using 1
  simp only [trig, Real.cos_zero, Real.sin_zero, mul_zero, sub_self, add_zero, zero_add]
  change -16*CubeHaarUpper.laplace β^192*SU2WilsonConvolution.coefficient β^4 /
    PeriodicGroundBridge.normalizer β 1 compensator = G 0 * (-16*SU2WilsonConvolution.coefficient β^4)
  rw [hG0]
  ring

theorem second_pairing (β : ℝ) (hb : 0 ≤ β) :
    (∫ V, probe β V * PeriodicEndpointSecondResponse.physicalSecond β 1 compensator V
      ∂PeriodicGroundBridge.law β 1 compensator) =
      -16*CubeHaarUpper.laplace β^192*SU2WilsonConvolution.coefficient β^4 /
        PeriodicGroundBridge.normalizer β 1 compensator := by
  have hh := PeriodicEndpointSecondResponse.physical_second_derivative β 1 compensator (probe β)
    (probe_measurable β) (2*Real.exp (960*|β|)) (by positivity) (probe_bound β)
  exact hh.unique (probe_second_derivative β hb)

/-- Nonzero physical second channel in its ORIGINAL middle L2 norm, not only
an auxiliary second moment. No frame or reconstruction completeness follows. -/
theorem physical_energy_positive (β : ℝ) (hb : 0 ≤ β)
    (ha : SU2WilsonConvolution.coefficient β ≠ 0) :
    0 < ∫ V, (PeriodicEndpointSecondResponse.physicalSecond β 1 compensator V)^2
      ∂PeriodicGroundBridge.law β 1 compensator := by
  let φ := PeriodicEndpointSecondResponse.physicalSecond β 1 compensator
  let μ := PeriodicGroundBridge.law β 1 compensator
  have hp : 0 < 16*CubeHaarUpper.laplace β^192*SU2WilsonConvolution.coefficient β^4 /
      PeriodicGroundBridge.normalizer β 1 compensator := by
    have ha4 : 0 < SU2WilsonConvolution.coefficient β^4 := by
      have hh := sq_pos_of_pos (sq_pos_of_ne_zero ha)
      nlinarith only [hh]
    exact div_pos (mul_pos (mul_pos (by norm_num) (pow_pos (CubeHaarUpper.laplace_pos β hb) _)) ha4)
      (PeriodicGroundBridge.normalizer_pos β 1 compensator)
  by_contra hn
  have hz : (∫ V, (φ V)^2 ∂μ) = 0 :=
    le_antisymm (not_lt.mp hn) (integral_nonneg (fun V => sq_nonneg _))
  have hAE := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun V => sq_nonneg (φ V)))
    (PeriodicEndpointSecondResponse.physicalSecond_memLp β 1 compensator).integrable_sq).mp hz
  have hzero : (∫ V, probe β V * φ V ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hAE] with V hV
    change (φ V)^2 = 0 at hV
    have hv : φ V = 0 := by nlinarith
    change probe β V * φ V = 0
    rw [hv, mul_zero]
  have hh := second_pairing β hb
  change (∫ V, probe β V * φ V ∂μ) = _ at hh
  rw [hzero] at hh
  have hneg : -16*CubeHaarUpper.laplace β^192*SU2WilsonConvolution.coefficient β^4 /
      PeriodicGroundBridge.normalizer β 1 compensator =
      -(16*CubeHaarUpper.laplace β^192*SU2WilsonConvolution.coefficient β^4 /
        PeriodicGroundBridge.normalizer β 1 compensator) := by ring
  rw [hneg] at hh
  linarith only [hh, hp]

theorem eventual_physical_energy : ∀ᶠ β : ℝ in atTop,
    0 < ∫ V, (PeriodicEndpointSecondResponse.physicalSecond β 1 compensator V)^2
      ∂PeriodicGroundBridge.law β 1 compensator := by
  have hc := (tendsto_order.mp SU2WilsonConvolution.coefficient_tendsto_one).1
    (1/2 : ℝ) (by norm_num)
  filter_upwards [hc, eventually_ge_atTop (0 : ℝ)] with β hα hb
  exact physical_energy_positive β hb (ne_of_gt (by linarith))

theorem law_even (β h : ℝ) :
    PeriodicGroundBridge.law β (left h 1) (right h compensator) =
      PeriodicGroundBridge.law β (left (-h) 1) (right (-h) compensator) := by
  have he : PeriodicGroundBridge.bridgeWeight β (left h 1) (right h compensator) =
      PeriodicGroundBridge.bridgeWeight β (left (-h) 1) (right (-h) compensator) := by
    funext V
    unfold PeriodicGroundBridge.bridgeWeight
    rw [right_kernel, right_kernel]
    change H β h V * kernel β V compensator = H β (-h) V * kernel β V compensator
    rw [H_even]
  unfold PeriodicGroundBridge.law
  rw [he]

/-- The physical FIRST score has zero native energy on this SAME curve.
The positive SECOND energy above is therefore an actual higher-channel effect. -/
theorem first_energy_zero (β : ℝ) :
    (∫ V, (PeriodicPhysicalBridgeScore.physicalScore β 1 compensator V)^2
      ∂PeriodicGroundBridge.law β 1 compensator) = 0 := by
  let f := PeriodicPhysicalBridgeScore.physicalScore β 1 compensator
  let F := fun h => ∫ V, f V ∂PeriodicGroundBridge.law β (left h 1) (right h compensator)
  let c := ∫ V, (f V)^2 ∂PeriodicGroundBridge.law β 1 compensator
  have hd : HasDerivAt F c 0 := by
    simpa only [F, c, f, pow_two] using PeriodicPhysicalBridgeScore.physical_derivative β 1 compensator f
      (PeriodicPhysicalBridgeScore.physicalScore_measurable β 1 compensator)
      (768*|β|) (by positivity) (PeriodicPhysicalBridgeScore.physicalScore_bound β 1 compensator)
  have he : (fun h => F (-h)) = F := by
    funext h
    dsimp only [F]
    rw [← law_even β h]
  have hd0 : HasDerivAt F c (-(0 : ℝ)) := by simpa only [neg_zero] using hd
  have hn := hd0.comp 0 (hasDerivAt_neg (0 : ℝ))
  change HasDerivAt (fun h => F (-h)) _ 0 at hn
  rw [he] at hn
  have hu := hd.unique hn
  change c = 0
  nlinarith only [hu]

end OperatorDerivativeRewrite.Foundation.PeriodicIdentitySecondWitness
