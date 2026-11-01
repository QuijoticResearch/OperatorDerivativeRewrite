import Foundation.PeriodicWindingEndpointResponse
/-! Actual off-diagonal physical response, with both Haar integrations and the
moving square normalizer retained. No native frame or mass gap is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix
namespace OperatorDerivativeRewrite.Foundation.PeriodicPhysicalFisherWitness
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicEndpointScore PeriodicEndpointFibreWitness PeriodicWindingEndpointResponse
open SU2TraceHessianModel
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar kernel

def temporalTrace (U V : State) (a : Gauge) : ℝ :=
  ∑ e : SpatialEdge, halfTrace (temporalWord U V a e)

private theorem trace_bound (U V : State) (a : Gauge) : |temporalTrace U V a| ≤ 192 := by
  unfold temporalTrace
  calc
    _ ≤ ∑ e : SpatialEdge, |halfTrace (temporalWord U V a e)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : SpatialEdge, (1:ℝ) := Finset.sum_le_sum (fun e _ => halfTrace_bound _)
    _ = 192 := by norm_num [edge_count]

private theorem trace_measurable (U : State) :
    Measurable (fun q : State × Gauge => temporalTrace U q.1 q.2) := by
  unfold temporalTrace
  apply Finset.measurable_sum
  intro e _
  exact halfTrace_measurable.comp (by unfold temporalWord; fun_prop)

private theorem trace_rotation (U V : State) (a : Gauge) (h : ℝ) :
    temporalTrace (left h U) V a = Real.cos h * temporalTrace U V a +
      Real.sin h * temporalTrace (left (Real.pi/2) U) V a := by
  have hs (L R : SU2) : halfTrace (L*SU2JointPlaquetteCubic.axis 0 h*R) =
      Real.cos h*halfTrace (L*R) +
        Real.sin h*halfTrace (L*SU2JointPlaquetteCubic.axis 0 (Real.pi/2)*R) := by
    simp only [halfTrace, Submonoid.coe_mul, SU2AxisMatrixJets.axis_matrix_formula,
      Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul, zero_add,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      traceReal, Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
    ring
  have he (e : SpatialEdge) : halfTrace (temporalWord (left h U) V a e) =
      Real.cos h*halfTrace (temporalWord U V a e) +
        Real.sin h*halfTrace (temporalWord (left (Real.pi/2) U) V a e) := by
    simpa only [temporalWord, left, one_mul, mul_assoc] using
      hs 1 (U e*a (shift e.1 e.2)*(V e)⁻¹*(a e.1)⁻¹)
  unfold temporalTrace
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

def traceSlope (h : ℝ) (V : State) (a : Gauge) : ℝ :=
  -Real.sin h * temporalTrace leftEndpoint V a +
    Real.cos h * temporalTrace (left (Real.pi/2) leftEndpoint) V a

private theorem trace_derivative (h : ℝ) (V : State) (a : Gauge) :
    HasDerivAt (fun t => temporalTrace (left t leftEndpoint) V a) (traceSlope h V a) h := by
  have he : (fun t => temporalTrace (left t leftEndpoint) V a) =
      (fun t => Real.cos t * temporalTrace leftEndpoint V a +
        Real.sin t * temporalTrace (left (Real.pi/2) leftEndpoint) V a) :=
    funext (trace_rotation leftEndpoint V a)
  rw [he]
  exact ((Real.hasDerivAt_cos h).mul_const _).add ((Real.hasDerivAt_sin h).mul_const _)

private theorem traceSlope_measurable (h : ℝ) :
    Measurable (fun q : State × Gauge => traceSlope h q.1 q.2) :=
  ((trace_measurable leftEndpoint).const_mul _).add ((trace_measurable _).const_mul _)

private theorem traceSlope_bound (h : ℝ) (V : State) (a : Gauge) : |traceSlope h V a| ≤ 384 := by
  unfold traceSlope
  have h1 := mul_le_mul (Real.abs_sin_le_one h) (trace_bound leftEndpoint V a)
    (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have h2 := mul_le_mul (Real.abs_cos_le_one h) (trace_bound (left (Real.pi/2) leftEndpoint) V a)
    (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  calc
    _ ≤ |-Real.sin h * temporalTrace leftEndpoint V a| +
      |Real.cos h * temporalTrace (left (Real.pi/2) leftEndpoint) V a| := abs_add_le _ _
    _ ≤ 384 := by rw [abs_mul, abs_neg, abs_mul]; linarith

def reducedWeight (β h : ℝ) (V : State) (a : Gauge) : ℝ :=
  Real.exp (-β * (spatialAction V/2 + temporalAction (left h leftEndpoint) V a))

def reducedWeightSlope (β h : ℝ) (V : State) (a : Gauge) : ℝ :=
  reducedWeight β h V a * (β * traceSlope h V a)

private theorem temporal_trace (U V : State) (a : Gauge) :
    temporalAction U V a = 192 - temporalTrace U V a := by
  unfold temporalAction temporalTrace
  rw [Finset.sum_sub_distrib]
  norm_num [edge_count]

private theorem weight_measurable (β h : ℝ) :
    Measurable (fun q : State × Gauge => reducedWeight β h q.1 q.2) := by
  unfold reducedWeight
  exact (((spatial_action_measurable.comp measurable_fst).div_const 2).add
    (temporal_action_joint_measurable.comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))).const_mul (-β) |>.exp

private theorem weightSlope_measurable (β h : ℝ) :
    Measurable (fun q : State × Gauge => reducedWeightSlope β h q.1 q.2) :=
  (weight_measurable β h).mul ((traceSlope_measurable h).const_mul β)

private theorem weight_derivative (β h : ℝ) (V : State) (a : Gauge) :
    HasDerivAt (fun t => reducedWeight β t V a) (reducedWeightSlope β h V a) h := by
  have hd := (((trace_derivative h V a).const_sub 192).const_add (spatialAction V/2)).const_mul (-β)
  have he : (fun t => reducedWeight β t V a) =
      (fun t => Real.exp (-β * (spatialAction V/2 + (192-temporalTrace (left t leftEndpoint) V a)))) := by
    funext t
    rw [reducedWeight, temporal_trace]
  rw [he]
  convert hd.exp using 1 <;> simp only [reducedWeightSlope, reducedWeight, temporal_trace] <;> ring

private theorem weight_bound (β h : ℝ) (V : State) (a : Gauge) :
    |reducedWeight β h V a| ≤ Real.exp (768*|β|) := by
  have hA : 0 ≤ spatialAction V/2 + temporalAction (left h leftEndpoint) V a :=
    add_nonneg (div_nonneg (spatial_action_bounds V).1 (by norm_num)) (temporal_action_bounds _ _ _).1
  have hB : spatialAction V/2 + temporalAction (left h leftEndpoint) V a ≤ 768 := by
    linarith [(spatial_action_bounds V).2, (temporal_action_bounds (left h leftEndpoint) V a).2]
  unfold reducedWeight
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    -β * _ ≤ |β| * _ := mul_le_mul_of_nonneg_right (neg_le_abs β) hA
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hB (abs_nonneg β)]

private theorem weightSlope_bound (β h : ℝ) (V : State) (a : Gauge) :
    |reducedWeightSlope β h V a| ≤ Real.exp (768*|β|) * (|β| *384) := by
  unfold reducedWeightSlope
  rw [abs_mul, abs_mul]
  exact mul_le_mul (weight_bound β h V a)
    (mul_le_mul_of_nonneg_left (traceSlope_bound h V a) (abs_nonneg β))
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le

def reduced (β h : ℝ) (V : State) : ℝ := ∫ a, reducedWeight β h V a ∂gaugeHaar

def reducedSlope (β h : ℝ) (V : State) : ℝ := ∫ a, reducedWeightSlope β h V a ∂gaugeHaar

theorem reduced_measurable (β h : ℝ) : Measurable (reduced β h) :=
  (weight_measurable β h).stronglyMeasurable.integral_prod_right.measurable

theorem reducedSlope_measurable (β h : ℝ) : Measurable (reducedSlope β h) :=
  (weightSlope_measurable β h).stronglyMeasurable.integral_prod_right.measurable

theorem reduced_bound (β h : ℝ) (V : State) : |reduced β h V| ≤ Real.exp (768*|β|) := by
  simpa only [reduced, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := gaugeHaar) (f := reducedWeight β h V)
      (C := Real.exp (768*|β|)) (ae_of_all _ (fun a => by
        simpa only [Real.norm_eq_abs] using weight_bound β h V a))

theorem reducedSlope_bound (β h : ℝ) (V : State) :
    |reducedSlope β h V| ≤ Real.exp (768*|β|) * (|β| *384) := by
  simpa only [reducedSlope, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := gaugeHaar) (f := reducedWeightSlope β h V)
      (C := Real.exp (768*|β|) * (|β| *384)) (ae_of_all _ (fun a => by
        simpa only [Real.norm_eq_abs] using weightSlope_bound β h V a))

/-- First Haar differentiation with a GLOBAL fixed-beta domination bound. -/
theorem reduced_derivative (β h : ℝ) (V : State) :
    HasDerivAt (fun t => reduced β t V) (reducedSlope β h V) h := by
  have hs : Set.Ioo (h-1) (h+1) ∈ 𝓝 h := Ioo_mem_nhds (by linarith) (by linarith)
  have hm (t : ℝ) : AEStronglyMeasurable (reducedWeight β t V) gaugeHaar :=
    ((weight_measurable β t).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hi : Integrable (reducedWeight β h V) gaugeHaar :=
    Integrable.of_bound (hm h) _ (ae_of_all _ (fun a => by
      simpa only [Real.norm_eq_abs] using weight_bound β h V a))
  have hd : AEStronglyMeasurable (reducedWeightSlope β h V) gaugeHaar :=
    ((weightSlope_measurable β h).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  obtain ⟨_, hz⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall hm) hi hd
    (ae_of_all _ (fun a t _ => by simpa only [Real.norm_eq_abs] using weightSlope_bound β t V a))
    (integrable_const _) (ae_of_all _ (fun a t _ => weight_derivative β t V a))
  exact hz


private theorem linear_derivative (β : ℝ) (f : State → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) :
    HasDerivAt (fun h => ∫ V, reduced β h V * f V ∂boundaryHaar)
      (∫ V, reducedSlope β 0 V * f V ∂boundaryHaar) 0 := by
  let F := fun h V => reduced β h V * f V
  let F' := fun h V => reducedSlope β h V * f V
  have hm (h : ℝ) : AEStronglyMeasurable (F h) boundaryHaar :=
    ((reduced_measurable β h).mul hf).aestronglyMeasurable
  have hi : Integrable (F 0) boundaryHaar := by
    apply Integrable.of_bound (hm 0) (Real.exp (768*|β|)*M)
    exact ae_of_all _ (fun V => by
      change ‖reduced β 0 V * f V‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (reduced_bound β 0 V) (hb V) (abs_nonneg _) (Real.exp_pos _).le)
  have hd : AEStronglyMeasurable (F' 0) boundaryHaar :=
    ((reducedSlope_measurable β 0).mul hf).aestronglyMeasurable
  have hbound : ∀ᵐ V ∂boundaryHaar, ∀ h ∈ Set.Ioo (-1:ℝ) 1,
      ‖F' h V‖ ≤ (Real.exp (768*|β|)*(|β| * 384))*M := by
    filter_upwards with V h _
    change ‖reducedSlope β h V * f V‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (reducedSlope_bound β h V) (hb V) (abs_nonneg _)
      (mul_nonneg (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) (by norm_num)))
  obtain ⟨_, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall hm) hi hd hbound (integrable_const _)
    (ae_of_all _ (fun V h _ => (reduced_derivative β h V).mul_const (f V)))
  exact h

private theorem square_derivative (β : ℝ) (f : State → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) :
    HasDerivAt (fun h => ∫ V, (reduced β h V)^2 * f V ∂boundaryHaar)
      (∫ V, (2 * reduced β 0 V * reducedSlope β 0 V) * f V ∂boundaryHaar) 0 := by
  let F := fun h V => (reduced β h V)^2 * f V
  let F' := fun h V => (2 * reduced β h V * reducedSlope β h V) * f V
  have hm (h : ℝ) : AEStronglyMeasurable (F h) boundaryHaar :=
    (((reduced_measurable β h).pow_const 2).mul hf).aestronglyMeasurable
  have hi : Integrable (F 0) boundaryHaar := by
    apply Integrable.of_bound (hm 0) (Real.exp (768*|β|)^2*M)
    filter_upwards with V
    change ‖(reduced β 0 V)^2 * f V‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (reduced_bound β 0 V) 2)
      (hb V) (abs_nonneg _) (sq_nonneg _)
  have hd : AEStronglyMeasurable (F' 0) boundaryHaar :=
    ((((reduced_measurable β 0).const_mul 2).mul (reducedSlope_measurable β 0)).mul hf).aestronglyMeasurable
  have hbound : ∀ᵐ V ∂boundaryHaar, ∀ h ∈ Set.Ioo (-1:ℝ) 1,
      ‖F' h V‖ ≤ (2*Real.exp (768*|β|)*(Real.exp (768*|β|)*(|β| * 384)))*M := by
    filter_upwards with V h _
    change ‖(2 * reduced β h V * reducedSlope β h V) * f V‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (reduced_bound β h V) (by norm_num))
      (reducedSlope_bound β h V) (abs_nonneg _) (by positivity)) (hb V) (abs_nonneg _) (by positivity)
  have hdiff : ∀ᵐ V ∂boundaryHaar, ∀ h ∈ Set.Ioo (-1:ℝ) 1,
      HasDerivAt (fun t => F t V) (F' h V) h := by
    filter_upwards with V h _
    simpa only [F, F', Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat] using
      ((reduced_derivative β h V).pow 2).mul_const (f V)
  obtain ⟨_, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall hm) hi hd hbound (integrable_const _) hdiff
  exact h

/-- Only the endpoint spatial scalar is extracted; the middle action stays. -/
theorem kernel_factor (β h : ℝ) (V : State) :
    kernel β (left h leftEndpoint) V =
      PeriodicPhysicalKineticReduction.multiplier β (left h leftEndpoint) * reduced β h V := by
  have he (a : Gauge) : weight β (left h leftEndpoint) V a =
      PeriodicPhysicalKineticReduction.multiplier β (left h leftEndpoint) * reducedWeight β h V a := by
    unfold weight halfAction PeriodicPhysicalKineticReduction.multiplier reducedWeight
    rw [← Real.exp_add]
    congr 1
    ring
  unfold kernel reduced
  simp_rw [he]
  rw [integral_const_mul]

private theorem axis_zero : SU2JointPlaquetteCubic.axis 0 0 = 1 := by
  apply Subtype.ext
  change (SU2JointPlaquetteCubic.axis 0 0 : M2) = 1
  simp [SU2AxisMatrixJets.axis_matrix_formula]

private theorem left_zero (U : State) : left 0 U = U := by
  funext e
  simp only [left, axis_zero, one_mul]

private theorem moving_winding (h : ℝ) :
    PeriodicCenteredHolonomy.first (left h leftEndpoint) = Real.sin (4*h) := by
  have he : left h leftEndpoint =
      gaugeAction (fun _ => SU2JointPlaquetteCubic.axis 0 h) (right (-h) leftEndpoint) := by
    funext e
    simp only [left, right, gaugeAction, neg_neg]
    group
  change halfTrace (PeriodicSpatialHolonomy.winding (left h leftEndpoint)
    PeriodicCenteredHolonomy.origin 0) = _
  rw [he, PeriodicSpatialHolonomy.trace_gauge]
  exact winding_curve h

/-- The reduced single-kernel moment is exact, before any differentiation. -/
theorem linear_moment (β : ℝ) (hβ : 0 ≤ β) (h : ℝ) :
    (∫ V, reduced β h V * weightedWinding β V ∂boundaryHaar) =
      (CubeHaarUpper.laplace β ^ 192 * SU2WilsonConvolution.coefficient β ^ 4) * Real.sin (4*h) := by
  apply mul_left_cancel₀ (show PeriodicPhysicalKineticReduction.multiplier β (left h leftEndpoint) ≠ 0
    from Real.exp_ne_zero _)
  rw [← integral_const_mul]
  have he (V : State) : PeriodicPhysicalKineticReduction.multiplier β (left h leftEndpoint) *
      (reduced β h V * weightedWinding β V) = kernel β (left h leftEndpoint) V * weightedWinding β V := by
    rw [kernel_factor]
    ring
  simp_rw [he]
  rw [kernel_winding β hβ, moving_winding]
  ring

private theorem slope_moment (β : ℝ) (hβ : 0 ≤ β) :
    (∫ V, reducedSlope β 0 V * weightedWinding β V ∂boundaryHaar) =
      4 * CubeHaarUpper.laplace β ^ 192 * SU2WilsonConvolution.coefficient β ^ 4 := by
  have hd := linear_derivative β (weightedWinding β) (weightedWinding_measurable β)
    (Real.exp (192*|β|)) (Real.exp_pos _).le (weightedWinding_bound β)
  have he : (fun h => ∫ V, reduced β h V * weightedWinding β V ∂boundaryHaar) =
      (fun h => (CubeHaarUpper.laplace β ^ 192 * SU2WilsonConvolution.coefficient β ^ 4) * Real.sin (4*h)) :=
    funext (linear_moment β hβ)
  rw [he] at hd
  have hs : HasDerivAt (fun h : ℝ => Real.sin (4*h)) 4 0 := by
    convert (Real.hasDerivAt_sin (4*(0:ℝ))).comp 0 ((hasDerivAt_id (0:ℝ)).const_mul 4) using 1 <;> norm_num <;> rfl
  have hh := hd.unique (hs.const_mul (CubeHaarUpper.laplace β ^ 192 * SU2WilsonConvolution.coefficient β ^ 4))
  linarith


/-- A FROZEN physical middle observable. Its denominator uses the BASE endpoint,
not the moving endpoint; no auxiliary temporal variable appears in this test. -/
def frozen (β : ℝ) (V : State) : ℝ := weightedWinding β V / kernel β leftEndpoint V

theorem frozen_measurable (β : ℝ) : Measurable (frozen β) :=
  (weightedWinding_measurable β).div
    ((kernel_joint_measurable β).comp (measurable_const.prodMk measurable_id))

theorem frozen_gauge (β : ℝ) (a : Gauge) (V : State) :
    frozen β (gaugeAction a V) = frozen β V := by
  unfold frozen
  rw [weightedWinding_gauge, kernel_right_invariant]

theorem frozen_bound (β : ℝ) (V : State) : |frozen β V| ≤ Real.exp (960*|β|) := by
  unfold frozen
  rw [abs_div, abs_of_pos (kernel_positive β leftEndpoint V)]
  calc
    _ ≤ Real.exp (192*|β|) / Real.exp (-768*|β|) :=
      (div_le_div_of_nonneg_right (weightedWinding_bound β V) (kernel_positive β leftEndpoint V).le).trans
        (div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) (kernel_bounds β leftEndpoint V).1)
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

private theorem right_zero (U : State) : right 0 U = U := by
  funext e
  simp only [right, neg_zero, axis_zero, mul_one]

private theorem base_factor (β : ℝ) (V : State) :
    kernel β leftEndpoint V =
      PeriodicPhysicalKineticReduction.multiplier β leftEndpoint * reduced β 0 V := by
  simpa only [left_zero] using kernel_factor β 0 V

private theorem frozen_cancel (β : ℝ) (V : State) :
    reduced β 0 V * frozen β V =
      weightedWinding β V / PeriodicPhysicalKineticReduction.multiplier β leftEndpoint := by
  unfold frozen
  have hm : PeriodicPhysicalKineticReduction.multiplier β leftEndpoint ≠ 0 := Real.exp_ne_zero _
  field_simp [(kernel_positive β leftEndpoint V).ne', hm]
  rw [base_factor]
  ring

def squareMass (β h : ℝ) : ℝ := ∫ V, (reduced β h V)^2 ∂boundaryHaar

private theorem bridge_reduced (β h : ℝ) (V : State) :
    PeriodicGroundBridge.bridgeWeight β (left h leftEndpoint) (right h rightEndpoint) V =
      (PeriodicPhysicalKineticReduction.multiplier β (left h leftEndpoint))^2 * (reduced β h V)^2 := by
  rw [bridge_square, ← PeriodicPhysicalBridgeScore.kernel_left_right β h leftEndpoint V,
    kernel_factor, mul_pow]

/-- The TRUE moving middle normalizer, with its extracted endpoint scalar. -/
theorem normalizer_reduced (β h : ℝ) :
    PeriodicGroundBridge.normalizer β (left h leftEndpoint) (right h rightEndpoint) =
      (PeriodicPhysicalKineticReduction.multiplier β (left h leftEndpoint))^2 * squareMass β h := by
  unfold PeriodicGroundBridge.normalizer
  simp_rw [bridge_reduced]
  rw [integral_const_mul]
  rfl

theorem squareMass_positive (β h : ℝ) : 0 < squareMass β h := by
  have hpos := PeriodicGroundBridge.normalizer_pos β (left h leftEndpoint) (right h rightEndpoint)
  rw [normalizer_reduced] at hpos
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos (Real.exp_pos _))).mp hpos

/-- Actual normalized bridge expectation. The MIDDLE spatial action remains in
reduced, and BOTH moving integrals are retained. -/
theorem expectation_reduced (β h : ℝ) (f : State → ℝ) :
    (∫ V, f V ∂PeriodicGroundBridge.law β (left h leftEndpoint) (right h rightEndpoint)) =
      (∫ V, (reduced β h V)^2 * f V ∂boundaryHaar) / squareMass β h := by
  rw [PeriodicGroundBridge.integral_formula, normalizer_reduced]
  simp_rw [bridge_reduced, mul_assoc]
  rw [integral_const_mul]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (Real.exp_ne_zero _))

private theorem numerator_zero (β : ℝ) (hβ : 0 ≤ β) :
    (∫ V, (reduced β 0 V)^2 * frozen β V ∂boundaryHaar) = 0 := by
  have he (V : State) : (reduced β 0 V)^2 * frozen β V =
      (reduced β 0 V * weightedWinding β V) / PeriodicPhysicalKineticReduction.multiplier β leftEndpoint := by
    calc
      _ = reduced β 0 V * (reduced β 0 V * frozen β V) := by ring
      _ = _ := by rw [frozen_cancel]; ring
  simp_rw [he]
  rw [integral_div, linear_moment β hβ 0]
  simp only [mul_zero, Real.sin_zero, zero_div]

theorem frozen_mean_zero (β : ℝ) (hβ : 0 ≤ β) :
    (∫ V, frozen β V ∂PeriodicGroundBridge.law β leftEndpoint rightEndpoint) = 0 := by
  have h := expectation_reduced β 0 (frozen β)
  simp only [left_zero, right_zero] at h
  rw [h, numerator_zero β hβ, zero_div]

private theorem numerator_derivative (β : ℝ) (hβ : 0 ≤ β) :
    HasDerivAt (fun h => ∫ V, (reduced β h V)^2 * frozen β V ∂boundaryHaar)
      (8 * CubeHaarUpper.laplace β ^ 192 * SU2WilsonConvolution.coefficient β ^ 4 /
        PeriodicPhysicalKineticReduction.multiplier β leftEndpoint) 0 := by
  have hd := square_derivative β (frozen β) (frozen_measurable β)
    (Real.exp (960*|β|)) (Real.exp_pos _).le (frozen_bound β)
  have he (V : State) : (2 * reduced β 0 V * reducedSlope β 0 V) * frozen β V =
      (2 / PeriodicPhysicalKineticReduction.multiplier β leftEndpoint) *
        (reducedSlope β 0 V * weightedWinding β V) := by
    calc
      _ = (2 * reducedSlope β 0 V) * (reduced β 0 V * frozen β V) := by ring
      _ = _ := by rw [frozen_cancel]; ring
  simp_rw [he] at hd
  rw [integral_const_mul, slope_moment β hβ] at hd
  convert hd using 1 <;> ring

private theorem normalizer_base (β : ℝ) :
    PeriodicGroundBridge.normalizer β leftEndpoint rightEndpoint =
      (PeriodicPhysicalKineticReduction.multiplier β leftEndpoint)^2 * squareMass β 0 := by
  simpa only [left_zero, right_zero] using normalizer_reduced β 0

/-- Positive response will follow from this ACTUAL fixed-observable derivative,
not an expectation-level kinetic formula or a changing test. -/
theorem frozen_derivative (β : ℝ) (hβ : 0 ≤ β) :
    HasDerivAt (fun h => ∫ V, frozen β V
      ∂PeriodicGroundBridge.law β (left h leftEndpoint) (right h rightEndpoint))
      (8 * CubeHaarUpper.laplace β ^ 192 *
        PeriodicPhysicalKineticReduction.multiplier β leftEndpoint * SU2WilsonConvolution.coefficient β ^ 4 /
          PeriodicGroundBridge.normalizer β leftEndpoint rightEndpoint) 0 := by
  have hn := numerator_derivative β hβ
  have hz := square_derivative β (fun _ => 1) measurable_const 1 (by norm_num) (fun _ => by norm_num)
  simp only [mul_one] at hz
  change HasDerivAt (squareMass β) _ 0 at hz
  have hd := hn.div hz (squareMass_positive β 0).ne'
  rw [numerator_zero β hβ] at hd
  have he : (fun h => ∫ V, frozen β V
      ∂PeriodicGroundBridge.law β (left h leftEndpoint) (right h rightEndpoint)) =
        (fun h => (∫ V, (reduced β h V)^2 * frozen β V ∂boundaryHaar) / squareMass β h) :=
    funext (fun h => expectation_reduced β h _)
  rw [he]
  convert hd using 1
  rw [normalizer_base]
  field_simp [(squareMass_positive β 0).ne', show PeriodicPhysicalKineticReduction.multiplier β leftEndpoint ≠ 0
    from Real.exp_ne_zero _]
  <;> ring


/-- Exact non-auxiliary score pairing for the fixed physical test. -/
theorem score_pairing (β : ℝ) (hβ : 0 ≤ β) :
    (∫ V, frozen β V * PeriodicPhysicalBridgeScore.physicalScore β leftEndpoint rightEndpoint V
      ∂PeriodicGroundBridge.law β leftEndpoint rightEndpoint) =
      8 * CubeHaarUpper.laplace β ^ 192 *
        PeriodicPhysicalKineticReduction.multiplier β leftEndpoint * SU2WilsonConvolution.coefficient β ^ 4 /
          PeriodicGroundBridge.normalizer β leftEndpoint rightEndpoint := by
  have h := PeriodicPhysicalBridgeScore.physical_derivative β leftEndpoint rightEndpoint
    (frozen β) (frozen_measurable β) (Real.exp (960*|β|)) (Real.exp_pos _).le (frozen_bound β)
  exact h.unique (frozen_derivative β hβ)

private theorem response_positive (β : ℝ) (hβ : 0 ≤ β)
    (hα : SU2WilsonConvolution.coefficient β ≠ 0) :
    0 < 8 * CubeHaarUpper.laplace β ^ 192 *
      PeriodicPhysicalKineticReduction.multiplier β leftEndpoint * SU2WilsonConvolution.coefficient β ^ 4 /
        PeriodicGroundBridge.normalizer β leftEndpoint rightEndpoint := by
  have hp : 0 < SU2WilsonConvolution.coefficient β ^ 4 := by
    have h := sq_pos_of_pos (sq_pos_of_ne_zero hα)
    nlinarith only [h]
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos (CubeHaarUpper.laplace_pos β hβ) _))
    (Real.exp_pos _)) hp) (PeriodicGroundBridge.normalizer_pos β leftEndpoint rightEndpoint)

theorem frozen_slope_positive (β : ℝ) (hβ : 0 ≤ β)
    (hα : SU2WilsonConvolution.coefficient β ≠ 0) :
    0 < deriv (fun h => ∫ V, frozen β V
      ∂PeriodicGroundBridge.law β (left h leftEndpoint) (right h rightEndpoint)) 0 := by
  rw [(frozen_derivative β hβ).deriv]
  exact response_positive β hβ hα

/-- A genuine NONZERO physical conditional Fisher energy under the ORIGINAL
normalized two-sided middle law. No stationary first-moment inference is used. -/
theorem physical_energy_positive (β : ℝ) (hβ : 0 ≤ β)
    (hα : SU2WilsonConvolution.coefficient β ≠ 0) :
    0 < ∫ V, (PeriodicPhysicalBridgeScore.physicalScore β leftEndpoint rightEndpoint V)^2
      ∂PeriodicGroundBridge.law β leftEndpoint rightEndpoint := by
  let φ := PeriodicPhysicalBridgeScore.physicalScore β leftEndpoint rightEndpoint
  let μ := PeriodicGroundBridge.law β leftEndpoint rightEndpoint
  have hp := response_positive β hβ hα
  have he := score_pairing β hβ
  by_contra hbad
  have hz : (∫ V, (φ V)^2 ∂μ) = 0 :=
    le_antisymm (not_lt.mp hbad) (integral_nonneg (fun _ => sq_nonneg _))
  have ha := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun V => sq_nonneg (φ V)))
    (PeriodicPhysicalBridgeScore.physicalScore_memLp β leftEndpoint rightEndpoint).integrable_sq).mp hz
  have hφ : φ =ᵐ[μ] 0 := by
    filter_upwards [ha] with V hV
    change (φ V)^2 = 0 at hV
    change φ V = 0
    nlinarith
  have hzero : (∫ V, frozen β V * φ V ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hφ] with V hV
    change frozen β V * φ V = 0
    change φ V = 0 at hV
    rw [hV, mul_zero]
  change (∫ V, frozen β V * φ V ∂μ) = _ at he
  rw [hzero] at he
  linarith

/-- The nonzero coefficient hypothesis holds throughout a large-beta tail by
an existing proved single-link limit, with no new positivity axiom. -/
theorem eventual_physical_energy : ∀ᶠ β : ℝ in atTop,
    0 < ∫ V, (PeriodicPhysicalBridgeScore.physicalScore β leftEndpoint rightEndpoint V)^2
      ∂PeriodicGroundBridge.law β leftEndpoint rightEndpoint := by
  have hcoef := (tendsto_order.mp SU2WilsonConvolution.coefficient_tendsto_one).1
    (1/2:ℝ) (by norm_num)
  filter_upwards [hcoef, eventually_ge_atTop (0:ℝ)] with β hα hβ
  exact physical_energy_positive β hβ (ne_of_gt (by linarith))

end OperatorDerivativeRewrite.Foundation.PeriodicPhysicalFisherWitness
