import Foundation.PeriodicJointHighResponse
import Foundation.SU2AxisMatrixJets
/-! Actual endpoint rotations and their normalized two-slab Wilson response.
All middle spatial links and both temporal fields are retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix
namespace OperatorDerivativeRewrite.Foundation.PeriodicEndpointScore
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab
open SU2TraceHessianModel
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar

abbrev Space := PeriodicAugmentedBridge.Space

def left (h : ℝ) (U : State) : State := fun e => SU2JointPlaquetteCubic.axis 0 h*U e
def right (h : ℝ) (W : State) : State := fun e => W e*SU2JointPlaquetteCubic.axis 0 (-h)

def traceSum (U W : State) (q : Space) : ℝ :=
  ∑ e : SpatialEdge,(halfTrace (temporalWord U q.1 q.2.1 e)+
    halfTrace (temporalWord q.1 W q.2.2 e))

theorem traceSum_measurable (U W : State) : Measurable (traceSum U W) := by
  unfold traceSum
  apply Finset.measurable_sum
  intro e _
  apply Measurable.add
  · exact halfTrace_measurable.comp (by unfold temporalWord; fun_prop)
  · exact halfTrace_measurable.comp (by unfold temporalWord; fun_prop)

theorem traceSum_bound (U W : State) (q : Space) : |traceSum U W q|≤384 := by
  unfold traceSum
  calc
    _ ≤ ∑ e : SpatialEdge,|halfTrace (temporalWord U q.1 q.2.1 e)+
        halfTrace (temporalWord q.1 W q.2.2 e)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : SpatialEdge,(2:ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      have hl := halfTrace_bound (temporalWord U q.1 q.2.1 e)
      have hr := halfTrace_bound (temporalWord q.1 W q.2.2 e)
      exact (abs_add_le _ _).trans (by linarith)
    _ = 384 := by norm_num [edge_count]

private theorem slot_trace (L R : SU2) (h : ℝ) :
    halfTrace (L*SU2JointPlaquetteCubic.axis 0 h*R)=
      Real.cos h*halfTrace (L*R)+
        Real.sin h*halfTrace (L*SU2JointPlaquetteCubic.axis 0 (Real.pi/2)*R) := by
  simp only [halfTrace,Submonoid.coe_mul,SU2AxisMatrixJets.axis_matrix_formula,
    Real.cos_pi_div_two,Real.sin_pi_div_two,zero_smul,one_smul,zero_add,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
    traceReal,Matrix.trace_add,Matrix.trace_smul,Complex.add_re,Complex.smul_re,smul_eq_mul]
  ring

theorem traceSum_rotation (U W : State) (q : Space) (h : ℝ) :
    traceSum (left h U) (right h W) q=
      Real.cos h*traceSum U W q+
        Real.sin h*traceSum (left (Real.pi/2) U) (right (Real.pi/2) W) q := by
  have hl (e : SpatialEdge) :
      halfTrace (temporalWord (left h U) q.1 q.2.1 e)=
        Real.cos h*halfTrace (temporalWord U q.1 q.2.1 e)+
          Real.sin h*halfTrace (temporalWord (left (Real.pi/2) U) q.1 q.2.1 e) := by
    simpa only [temporalWord,left,one_mul,mul_assoc] using
      slot_trace 1 (U e*q.2.1 (shift e.1 e.2)*(q.1 e)⁻¹*(q.2.1 e.1)⁻¹) h
  have hr (e : SpatialEdge) :
      halfTrace (temporalWord q.1 (right h W) q.2.2 e)=
        Real.cos h*halfTrace (temporalWord q.1 W q.2.2 e)+
          Real.sin h*halfTrace (temporalWord q.1 (right (Real.pi/2) W) q.2.2 e) := by
    simpa only [temporalWord,right,mul_inv_rev,SU2AxisMatrixJets.axis_inv,neg_neg,mul_assoc] using
      slot_trace (q.1 e*q.2.2 (shift e.1 e.2)) ((W e)⁻¹*(q.2.2 e.1)⁻¹) h
  unfold traceSum
  simp_rw [hl,hr]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem central_trace (U W : State) (q : Space) :
    PeriodicAugmentedBridge.centralAction U W q=spatialAction q.1+384-traceSum U W q := by
  unfold PeriodicAugmentedBridge.centralAction temporalAction traceSum
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,edge_count,nsmul_eq_mul,mul_one]
  ring


/-- Exact relative exponent for arbitrary actual endpoint pairs. -/
def phase (β : ℝ) (U W : State) (h : ℝ) (q : Space) : ℝ :=
  β*((Real.cos h-1)*traceSum U W q+
    Real.sin h*traceSum (left (Real.pi/2) U) (right (Real.pi/2) W) q)

def phaseSlope (β : ℝ) (U W : State) (h : ℝ) (q : Space) : ℝ :=
  β*((-Real.sin h)*traceSum U W q+
    Real.cos h*traceSum (left (Real.pi/2) U) (right (Real.pi/2) W) q)

theorem phase_measurable (β : ℝ) (U W : State) (h : ℝ) : Measurable (phase β U W h) :=
  (((traceSum_measurable U W).const_mul _).add
    ((traceSum_measurable _ _).const_mul _)).const_mul _

private theorem phaseSlope_measurable (β : ℝ) (U W : State) (h : ℝ) :
    Measurable (phaseSlope β U W h) :=
  (((traceSum_measurable U W).const_mul _).add
    ((traceSum_measurable _ _).const_mul _)).const_mul _

theorem phase_bound (β : ℝ) (U W : State) (h : ℝ) (q : Space) :
    |phase β U W h q|≤1152*|β| := by
  have hc : |Real.cos h-1|≤2 := (abs_sub _ _).trans (by
    rw [abs_one]
    linarith [Real.abs_cos_le_one h])
  have hs := Real.abs_sin_le_one h
  have hC := traceSum_bound U W q
  have hD := traceSum_bound (left (Real.pi/2) U) (right (Real.pi/2) W) q
  unfold phase
  rw [abs_mul]
  have hm : |(Real.cos h-1)*traceSum U W q+
      Real.sin h*traceSum (left (Real.pi/2) U) (right (Real.pi/2) W) q|≤1152 := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    have h1 := mul_le_mul hc hC (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
    have h2 := mul_le_mul hs hD (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith
  nlinarith [abs_nonneg β]

theorem phaseSlope_bound (β : ℝ) (U W : State) (h : ℝ) (q : Space) :
    |phaseSlope β U W h q|≤768*|β| := by
  have hc := Real.abs_cos_le_one h
  have hs := Real.abs_sin_le_one h
  have hC := traceSum_bound U W q
  have hD := traceSum_bound (left (Real.pi/2) U) (right (Real.pi/2) W) q
  unfold phaseSlope
  rw [abs_mul]
  have hm : |(-Real.sin h)*traceSum U W q+
      Real.cos h*traceSum (left (Real.pi/2) U) (right (Real.pi/2) W) q|≤768 := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_neg]
    have h1 := mul_le_mul hs hC (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have h2 := mul_le_mul hc hD (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    linarith
  nlinarith [abs_nonneg β]

theorem phase_hasDerivAt (β : ℝ) (U W : State) (h : ℝ) (q : Space) :
    HasDerivAt (fun t => phase β U W t q) (phaseSlope β U W h q) h := by
  exact ((((Real.hasDerivAt_cos h).sub_const 1).mul_const (traceSum U W q)).add
    ((Real.hasDerivAt_sin h).mul_const
      (traceSum (left (Real.pi/2) U) (right (Real.pi/2) W) q))).const_mul β

private theorem central_integral (β : ℝ) (U W : State) (f : Space → ℝ) :
    (∫ q,f q ∂PeriodicAugmentedBridge.law β U W)=
      (∫ q,Real.exp (-β*PeriodicAugmentedBridge.centralAction U W q)*f q
        ∂PeriodicAugmentedBridge.reference)/
      (∫ q,Real.exp (-β*PeriodicAugmentedBridge.centralAction U W q)
        ∂PeriodicAugmentedBridge.reference) := by
  rw [PeriodicAugmentedBridge.integral_formula,← PeriodicAugmentedBridge.total_integral]
  simp_rw [PeriodicAugmentedBridge.density_phase,mul_assoc,integral_const_mul]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

theorem central_weight_rotation (β : ℝ) (U W : State) (h : ℝ) (q : Space) :
    Real.exp (-β*PeriodicAugmentedBridge.centralAction (left h U) (right h W) q)=
      Real.exp (-β*PeriodicAugmentedBridge.centralAction U W q)*Real.exp (phase β U W h q) := by
  rw [← Real.exp_add]
  congr 1
  rw [central_trace,central_trace,traceSum_rotation]
  unfold phase
  ring

def weighted (β : ℝ) (U W : State) (f : Space → ℝ) (h : ℝ) : ℝ :=
  ∫ q,f q*Real.exp (phase β U W h q) ∂PeriodicAugmentedBridge.law β U W

theorem rotated_integral (β : ℝ) (U W : State) (h : ℝ) (f : Space → ℝ) :
    (∫ q,f q ∂PeriodicAugmentedBridge.law β (left h U) (right h W))=
      weighted β U W f h/weighted β U W (fun _ => 1) h := by
  rw [central_integral]
  unfold weighted
  rw [central_integral,central_integral]
  simp only [one_mul]
  have hN : (∫ q,Real.exp (-β*PeriodicAugmentedBridge.centralAction U W q)*
      (f q*Real.exp (phase β U W h q)) ∂PeriodicAugmentedBridge.reference)=
      ∫ q,Real.exp (-β*PeriodicAugmentedBridge.centralAction (left h U) (right h W) q)*f q
        ∂PeriodicAugmentedBridge.reference := by
    apply integral_congr_ae
    filter_upwards with q
    rw [central_weight_rotation]
    ring
  rw [hN]
  simp_rw [← central_weight_rotation]
  have hz : (∫ q,Real.exp (-β*PeriodicAugmentedBridge.centralAction U W q)
      ∂PeriodicAugmentedBridge.reference)≠0 := by
    have he := PeriodicAugmentedBridge.total_integral β U W
    simp_rw [PeriodicAugmentedBridge.density_phase,integral_const_mul] at he
    exact (mul_ne_zero_iff.mp (he.trans_ne (PeriodicGroundBridge.normalizer_pos β U W).ne')).2
  exact (div_div_div_cancel_right₀ hz _ _).symm

theorem weighted_zero (β : ℝ) (U W : State) (f : Space → ℝ) :
    weighted β U W f 0=∫ q,f q ∂PeriodicAugmentedBridge.law β U W := by
  simp only [weighted,phase,Real.cos_zero,Real.sin_zero,sub_self,zero_mul,mul_zero,add_zero,
    Real.exp_zero,mul_one]

/-- Differentiation of the ACTUAL relative weight under the fixed base bridge law. -/
theorem weighted_hasDerivAt_zero (β : ℝ) (U W : State) (f : Space → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0≤M) (hfb : ∀ q,|f q|≤M) :
    HasDerivAt (weighted β U W f)
      (∫ q,f q*(β*traceSum (left (Real.pi/2) U) (right (Real.pi/2) W) q)
        ∂PeriodicAugmentedBridge.law β U W) 0 := by
  let μ := PeriodicAugmentedBridge.law β U W
  let F := fun h q => f q*Real.exp (phase β U W h q)
  let F' := fun h q => f q*Real.exp (phase β U W h q)*phaseSlope β U W h q
  have hs : Set.Ioo (-1:ℝ) 1∈𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hmeas : ∀ h,AEStronglyMeasurable (F h) μ := fun h =>
    (hf.mul (phase_measurable β U W h).exp).aestronglyMeasurable
  have hint : Integrable (F 0) μ := by
    apply Integrable.mono' (integrable_const M) (hmeas 0)
    filter_upwards with q
    simpa only [F,phase,Real.cos_zero,Real.sin_zero,sub_self,zero_mul,mul_zero,add_zero,
      Real.exp_zero,mul_one,Real.norm_eq_abs] using hfb q
  have hdmeas : AEStronglyMeasurable (F' 0) μ :=
    ((hf.mul (phase_measurable β U W 0).exp).mul
      (phaseSlope_measurable β U W 0)).aestronglyMeasurable
  have hbound : ∀ᵐ q ∂μ,∀ h∈Set.Ioo (-1:ℝ) 1,
      ‖F' h q‖≤M*Real.exp (1152*|β|)*(768*|β|) := by
    filter_upwards with q h _
    have he : Real.exp (phase β U W h q)≤Real.exp (1152*|β|) :=
      Real.exp_le_exp.mpr ((le_abs_self _).trans (phase_bound β U W h q))
    change ‖f q*Real.exp (phase β U W h q)*phaseSlope β U W h q‖≤_
    rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul (hfb q) he (Real.exp_pos _).le hM)
      (phaseSlope_bound β U W h q) (abs_nonneg _)
      (mul_nonneg hM (Real.exp_pos _).le)
  have hdiff : ∀ᵐ q ∂μ,∀ h∈Set.Ioo (-1:ℝ) 1,HasDerivAt (F · q) (F' h q) h := by
    filter_upwards with q h _
    have hd := (phase_hasDerivAt β U W h q).exp.const_mul (f q)
    simpa only [F,F',Function.comp_def,mul_comm,mul_left_comm,mul_assoc] using hd
  obtain ⟨_,hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall hmeas) hint hdmeas hbound (integrable_const _) hdiff
  change HasDerivAt (fun h => ∫ q,f q*Real.exp (phase β U W h q) ∂μ) _ 0
  simpa only [F,F',phase,phaseSlope,Real.cos_zero,Real.sin_zero,sub_self,zero_mul,mul_zero,
    one_mul,zero_add,add_zero,Real.exp_zero,mul_one,neg_zero] using hd

/-- Actual endpoint derivative, with the full conditional normalizer. -/
theorem expectation_hasDerivAt (β : ℝ) (U W : State) (f : Space → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0≤M) (hfb : ∀ q,|f q|≤M) :
    HasDerivAt (fun h => ∫ q,f q ∂PeriodicAugmentedBridge.law β (left h U) (right h W))
      ((∫ q,f q*(β*traceSum (left (Real.pi/2) U) (right (Real.pi/2) W) q)
        ∂PeriodicAugmentedBridge.law β U W)-
       (∫ q,f q ∂PeriodicAugmentedBridge.law β U W)*
        (∫ q,β*traceSum (left (Real.pi/2) U) (right (Real.pi/2) W) q
          ∂PeriodicAugmentedBridge.law β U W)) 0 := by
  have hn := weighted_hasDerivAt_zero β U W f hf M hM hfb
  have hd := weighted_hasDerivAt_zero β U W (fun _ => 1) measurable_const 1
    (by norm_num) (fun _ => by norm_num)
  have hz : weighted β U W (fun _ => 1) 0=1 := by rw [weighted_zero]; simp
  have h := hn.div hd (by rw [hz]; norm_num)
  simp only [weighted_zero,hz,one_mul,mul_one,one_pow,div_one] at h
  convert h using 1
  funext t
  exact rotated_integral β U W t f

def direction (U W : State) : Space → ℝ :=
  traceSum (left (Real.pi/2) U) (right (Real.pi/2) W)

def score (β : ℝ) (U W : State) (q : Space) : ℝ :=
  β*(direction U W q-∫ z,direction U W z ∂PeriodicAugmentedBridge.law β U W)

theorem score_measurable (β : ℝ) (U W : State) : Measurable (score β U W) :=
  ((traceSum_measurable _ _).sub measurable_const).const_mul β

theorem score_bound (β : ℝ) (U W : State) (q : Space) : |score β U W q|≤768*|β| := by
  have hm : ‖∫ z,direction U W z ∂PeriodicAugmentedBridge.law β U W‖≤384 := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := PeriodicAugmentedBridge.law β U W) (f := direction U W) (C := 384)
      (ae_of_all _ (fun z => by simpa only [direction,Real.norm_eq_abs] using traceSum_bound _ _ z))
  have hh : |direction U W q-∫ z,direction U W z ∂PeriodicAugmentedBridge.law β U W|≤768 := by
    apply (abs_sub _ _).trans
    rw [Real.norm_eq_abs] at hm
    have hd := traceSum_bound (left (Real.pi/2) U) (right (Real.pi/2) W) q
    change |direction U W q|≤384 at hd
    linarith
  unfold score
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left hh (abs_nonneg β)).trans_eq (mul_comm _ _)

theorem score_memLp (β : ℝ) (U W : State) :
    MemLp (score β U W) 2 (PeriodicAugmentedBridge.law β U W) :=
  MemLp.of_bound (score_measurable β U W).aestronglyMeasurable (768*|β|)
    (ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs] using score_bound β U W q))

/-- Native-score form of the genuine endpoint derivative on its bounded core. -/
theorem expectation_score (β : ℝ) (U W : State) (f : Space → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0≤M) (hfb : ∀ q,|f q|≤M) :
    HasDerivAt (fun h => ∫ q,f q ∂PeriodicAugmentedBridge.law β (left h U) (right h W))
      (∫ q,f q*score β U W q ∂PeriodicAugmentedBridge.law β U W) 0 := by
  have h := expectation_hasDerivAt β U W f hf M hM hfb
  have hfi : Integrable f (PeriodicAugmentedBridge.law β U W) :=
    Integrable.of_bound hf.aestronglyMeasurable M
      (ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs] using hfb q))
  have hdi : Integrable (fun q => f q*(β*direction U W q))
      (PeriodicAugmentedBridge.law β U W) := by
    apply Integrable.of_bound (hf.mul ((traceSum_measurable _ _).const_mul β)).aestronglyMeasurable
      (M*(|β| *384))
    filter_upwards with q
    change ‖f q*(β*traceSum (left (Real.pi/2) U) (right (Real.pi/2) W) q)‖≤_
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    exact mul_le_mul (hfb q) (mul_le_mul_of_nonneg_left (traceSum_bound _ _ q) (abs_nonneg β))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hM
  have he : (∫ q,f q*score β U W q ∂PeriodicAugmentedBridge.law β U W)=
      (∫ q,f q*(β*direction U W q) ∂PeriodicAugmentedBridge.law β U W)-
      (∫ q,f q ∂PeriodicAugmentedBridge.law β U W)*
        (∫ q,β*direction U W q ∂PeriodicAugmentedBridge.law β U W) := by
    have hp (q : Space) : f q*score β U W q=
        f q*(β*direction U W q)-f q*(β*∫ z,direction U W z ∂PeriodicAugmentedBridge.law β U W) := by
      unfold score
      ring
    simp_rw [hp]
    rw [integral_sub hdi (hfi.mul_const _),integral_mul_const,integral_const_mul]
  rw [he]
  exact h

def badEnergy (β : ℝ) (U W : State) : ℝ :=
  ∫ q,((fun q : Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad).indicator
    (fun q => (score β U W q)^2) q ∂PeriodicAugmentedBridge.law β U W

theorem badEnergy_nonneg (β : ℝ) (U W : State) : 0≤badEnergy β U W :=
  integral_nonneg (fun _ => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)

theorem badEnergy_bound (β : ℝ) (U W : State) :
    badEnergy β U W≤(768*|β|)^2*(PeriodicGroundBridge.law β U W).real
      PeriodicCancellingRestTail.bad := by
  let E : Set Space := (fun q : Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad
  have hE : MeasurableSet E := measurable_fst PeriodicCancellingRestTail.bad_measurable
  have hi : Integrable (E.indicator (fun q => (score β U W q)^2))
      (PeriodicAugmentedBridge.law β U W) := (score_memLp β U W).integrable_sq.indicator hE
  have hc : Integrable (E.indicator (fun _ : Space => (768*|β|)^2))
      (PeriodicAugmentedBridge.law β U W) := (integrable_const _).indicator hE
  have hp (q : Space) : E.indicator (fun q => (score β U W q)^2) q≤
      E.indicator (fun _ => (768*|β|)^2) q := by
    by_cases hq : q∈E
    · rw [Set.indicator_of_mem hq,Set.indicator_of_mem hq]
      have hs := score_bound β U W q
      nlinarith [abs_nonneg (score β U W q),sq_abs (score β U W q)]
    · simp only [Set.indicator_of_notMem hq,le_refl]
  have h := integral_mono hi hc hp
  rw [integral_indicator_const _ hE] at h
  have he : (PeriodicAugmentedBridge.law β U W).real E=
      (PeriodicGroundBridge.law β U W).real PeriodicCancellingRestTail.bad := by
    apply congrArg ENNReal.toReal
    rw [← (PeriodicAugmentedBridge.projection_preserving β U W).map_eq,
      Measure.map_apply measurable_fst PeriodicCancellingRestTail.bad_measurable]
  change badEnergy β U W≤_ at h
  rw [he] at h
  exact h.trans_eq (mul_comm _ _)

attribute [local irreducible] traceSum direction score badEnergy
  PeriodicAugmentedBridge.law PeriodicAugmentedBridge.reference PeriodicAugmentedBridge.density

private theorem traceSum_joint_measurable :
    Measurable (fun p : (State × State) × Space => traceSum p.1.1 p.1.2 p.2) := by
  unfold traceSum
  apply Finset.measurable_sum
  intro e _
  apply Measurable.add
  · exact halfTrace_measurable.comp (by unfold temporalWord; fun_prop)
  · exact halfTrace_measurable.comp (by unfold temporalWord; fun_prop)

private theorem direction_joint_measurable :
    Measurable (fun p : (State × State) × Space => direction p.1.1 p.1.2 p.2) := by
  have hL : Measurable (fun p : (State × State) × Space => left (Real.pi/2) p.1.1) := by
    apply measurable_pi_lambda
    intro e
    exact measurable_const.mul ((measurable_pi_apply e).comp (measurable_fst.comp measurable_fst))
  have hR : Measurable (fun p : (State × State) × Space => right (Real.pi/2) p.1.2) := by
    apply measurable_pi_lambda
    intro e
    exact ((measurable_pi_apply e).comp (measurable_snd.comp measurable_fst)).mul measurable_const
  unfold direction
  change Measurable (fun p : (State × State) × Space =>
    traceSum (left (Real.pi/2) p.1.1) (right (Real.pi/2) p.1.2) p.2)
  exact traceSum_joint_measurable.comp ((hL.prodMk hR).prodMk measurable_snd)

private theorem density_joint_measurable (β : ℝ) :
    Measurable (fun p : (State × State) × Space => PeriodicAugmentedBridge.density β p.1.1 p.1.2 p.2) := by
  have h1 : Measurable (fun p : (State × State) × Space => ((p.1.1,p.2.1),p.2.2.1)) := by fun_prop
  have h2 : Measurable (fun p : (State × State) × Space => ((p.2.1,p.1.2),p.2.2.2)) := by fun_prop
  unfold PeriodicAugmentedBridge.density
  exact ((weight_joint_measurable β).comp h1).mul ((weight_joint_measurable β).comp h2)

private theorem meanDirection_measurable (β : ℝ) :
    Measurable (fun p : State × State => ∫ q,direction p.1 p.2 q ∂PeriodicAugmentedBridge.law β p.1 p.2) := by
  have he : (fun p : State × State => ∫ q,direction p.1 p.2 q ∂PeriodicAugmentedBridge.law β p.1 p.2)=
      (fun p => (∫ q,PeriodicAugmentedBridge.density β p.1 p.2 q*direction p.1 p.2 q
        ∂PeriodicAugmentedBridge.reference)/PeriodicGroundBridge.normalizer β p.1 p.2) := by
    funext p
    exact PeriodicAugmentedBridge.integral_formula β p.1 p.2 _
  rw [he]
  exact ((density_joint_measurable β).mul direction_joint_measurable).stronglyMeasurable.integral_prod_right.measurable.div
    (PeriodicGroundBridge.normalizer_measurable β)

private theorem score_joint_measurable (β : ℝ) :
    Measurable (fun p : (State × State) × Space => score β p.1.1 p.1.2 p.2) := by
  unfold score
  exact (direction_joint_measurable.sub ((meanDirection_measurable β).comp measurable_fst)).const_mul β

/-- Actual measurability is proved before taking endpoint averages. -/
theorem badEnergy_measurable (β : ℝ) : Measurable (fun p : State × State => badEnergy β p.1 p.2) := by
  have hf : Measurable (fun p : (State × State) × Space =>
      ((fun q : Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad).indicator
        (fun q => (score β p.1.1 p.1.2 q)^2) p.2) := by
    exact (score_joint_measurable β |>.pow_const 2).indicator
      ((measurable_fst.comp measurable_snd) PeriodicCancellingRestTail.bad_measurable)
  have he : (fun p : State × State => badEnergy β p.1 p.2)=
      (fun p => (∫ q,PeriodicAugmentedBridge.density β p.1 p.2 q*
        ((fun q : Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad).indicator
          (fun q => (score β p.1 p.2 q)^2) q ∂PeriodicAugmentedBridge.reference)/
            PeriodicGroundBridge.normalizer β p.1 p.2) := by
    funext p
    unfold badEnergy
    exact PeriodicAugmentedBridge.integral_formula β p.1 p.2 _
  rw [he]
  exact ((density_joint_measurable β).mul hf).stronglyMeasurable.integral_prod_right.measurable.div
    (PeriodicGroundBridge.normalizer_measurable β)

/-- Actual derivative-weighted rare-event estimate under the TRUE stationary
TWO-step endpoint law, not a fixed-endpoint or volume-uniform bound. -/
theorem averaged_badEnergy {β : ℝ} (hb : 16777216≤β) (g : PeriodicSlabGround.GroundData β) :
    (∫ U,∫ W,badEnergy β U W ∂((g.transition ∘ₖ g.transition) U) ∂g.stationary) ≤
      (768*|β|)^2*(PeriodicGroundHaarScale.upperConstant/
        PeriodicGaugeSaturatedGround.eigenLowerConstant)*Real.exp (-β) := by
  letI := g.transition_markov
  letI := g.stationary_probability
  let p : State × State → ℝ := fun z =>
    (PeriodicGroundBridge.law β z.1 z.2).real PeriodicCancellingRestTail.bad
  let c : ℝ := (768*|β|)^2
  have hc : 0≤c := sq_nonneg _
  have hp0 (z : State × State) : 0≤p z := measureReal_nonneg
  have hp1 (z : State × State) : p z≤1 := measureReal_le_one
  have hpm : Measurable p := by
    have h := (measurable_const.indicator PeriodicCancellingRestTail.bad_measurable :
      Measurable (PeriodicCancellingRestTail.bad.indicator (fun _ : State => (1:ℝ))))
    have hm := h.stronglyMeasurable.integral_kernel (κ := PeriodicGroundBridge.bridgeKernel β)
    have he : (fun z : State × State => ∫ V,PeriodicCancellingRestTail.bad.indicator
        (fun _ : State => (1:ℝ)) V ∂PeriodicGroundBridge.law β z.1 z.2)=p := by
      funext z
      rw [integral_indicator_const (1:ℝ) PeriodicCancellingRestTail.bad_measurable]
      change (PeriodicGroundBridge.law β z.1 z.2).real PeriodicCancellingRestTail.bad*1=_
      exact mul_one _
    rw [← he]
    simpa only [PeriodicGroundBridge.bridgeKernel_apply] using hm.measurable
  have hpabs (z : State × State) : |p z|≤1 := by rw [abs_of_nonneg (hp0 z)]; exact hp1 z
  have hEabs (z : State × State) : |badEnergy β z.1 z.2|≤c := by
    rw [abs_of_nonneg (badEnergy_nonneg β z.1 z.2)]
    exact (badEnergy_bound β z.1 z.2).trans (mul_le_of_le_one_right hc (hp1 z))
  have hiE (U : State) : Integrable (fun W => badEnergy β U W)
      ((g.transition ∘ₖ g.transition) U) :=
    Integrable.of_bound ((badEnergy_measurable β).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      c (ae_of_all _ (fun W => by simpa only [Real.norm_eq_abs] using hEabs (U,W)))
  have hiP (U : State) : Integrable (fun W => p (U,W))
      ((g.transition ∘ₖ g.transition) U) :=
    Integrable.of_bound (hpm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      1 (ae_of_all _ (fun W => by simpa only [Real.norm_eq_abs] using hpabs (U,W)))
  have hmE : Measurable (fun U => ∫ W,badEnergy β U W ∂((g.transition ∘ₖ g.transition) U)) :=
    (badEnergy_measurable β).stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hmP : Measurable (fun U => ∫ W,p (U,W) ∂((g.transition ∘ₖ g.transition) U)) :=
    hpm.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hboundE (U : State) : ‖∫ W,badEnergy β U W ∂((g.transition ∘ₖ g.transition) U)‖≤c := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := (g.transition ∘ₖ g.transition) U) (f := fun W => badEnergy β U W) (C := c)
      (ae_of_all _ (fun W => by simpa only [Real.norm_eq_abs] using hEabs (U,W)))
  have hboundP (U : State) : ‖∫ W,p (U,W) ∂((g.transition ∘ₖ g.transition) U)‖≤1 := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := (g.transition ∘ₖ g.transition) U) (f := fun W => p (U,W)) (C := 1)
      (ae_of_all _ (fun W => by simpa only [Real.norm_eq_abs] using hpabs (U,W)))
  have hE : Integrable (fun U => ∫ W,badEnergy β U W ∂((g.transition ∘ₖ g.transition) U)) g.stationary :=
    Integrable.of_bound hmE.aestronglyMeasurable c (ae_of_all _ hboundE)
  have hP : Integrable (fun U => c*(∫ W,p (U,W) ∂((g.transition ∘ₖ g.transition) U))) g.stationary :=
    (Integrable.of_bound hmP.aestronglyMeasurable 1 (ae_of_all _ hboundP)).const_mul c
  have hh (U : State) : (∫ W,badEnergy β U W ∂((g.transition ∘ₖ g.transition) U))≤
      c*(∫ W,p (U,W) ∂((g.transition ∘ₖ g.transition) U)) := by
    rw [← integral_const_mul]
    exact integral_mono (hiE U) ((hiP U).const_mul c) (fun W => badEnergy_bound β U W)
  have h := integral_mono hE hP hh
  rw [integral_const_mul] at h
  change (∫ U,∫ W,badEnergy β U W ∂((g.transition ∘ₖ g.transition) U) ∂g.stationary)≤
    c*(∫ U,∫ W,(PeriodicGroundBridge.law β U W).real PeriodicCancellingRestTail.bad
      ∂((g.transition ∘ₖ g.transition) U) ∂g.stationary) at h
  rw [PeriodicCancellingRestTail.averaged_bridge_identity] at h
  calc
    _ ≤ _ := h.trans (mul_le_mul_of_nonneg_left
      (PeriodicCancellingRestTail.stationary_bad_bound hb g) hc)
    _ = _ := by ring

/-- The displayed bad-event energy is the norm of an actual native L2 field. -/
theorem badEnergy_native (β : ℝ) (U W : State) :
    ∃ Z : Lp ℝ 2 (PeriodicAugmentedBridge.law β U W),
      (Z : Space → ℝ)=ᵐ[PeriodicAugmentedBridge.law β U W]
        ((fun q : Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad).indicator (score β U W) ∧
      ‖Z‖^2=badEnergy β U W := by
  let E : Set Space := (fun q : Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad
  have hE : MeasurableSet E := measurable_fst PeriodicCancellingRestTail.bad_measurable
  have hm := (score_memLp β U W).indicator hE
  refine ⟨hm.toLp _,hm.coeFn_toLp,?_⟩
  rw [BochnerL2Dominated.norm_sq_integral]
  unfold badEnergy
  apply integral_congr_ae
  filter_upwards [hm.coeFn_toLp] with q hq
  rw [hq,Real.norm_eq_abs,sq_abs]
  by_cases he : q∈E
  · rw [Set.indicator_of_mem he,Set.indicator_of_mem he]
  · rw [Set.indicator_of_notMem he,Set.indicator_of_notMem he]
    norm_num

/-- The actual derivative-weighted averaged bad energy vanishes for EVERY
choice of ground data as beta tends to infinity. No derivative of that choice
is assumed or taken, and no statement about the remaining response is made. -/
theorem averaged_badEnergy_tendsto (g : ∀ β : ℝ,PeriodicSlabGround.GroundData β) :
    Tendsto (fun β => ∫ U,∫ W,badEnergy β U W
      ∂(((g β).transition ∘ₖ (g β).transition) U) ∂(g β).stationary) atTop (𝓝 0) := by
  let R : ℝ := PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant
  have hu : Tendsto (fun β : ℝ => (768*|β|)^2*R*Real.exp (-β)) atTop (𝓝 0) := by
    have h : Tendsto (fun β : ℝ => ((768:ℝ)^2*R)*(β^2*Real.exp (-β))) atTop (𝓝 0) := by
      simpa only [mul_zero] using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul ((768:ℝ)^2*R)
    convert h using 1
    funext β
    rw [mul_pow,sq_abs]
    ring
  apply squeeze_zero' (Eventually.of_forall (fun β => integral_nonneg (fun U =>
    integral_nonneg (fun W => badEnergy_nonneg β U W)))) ?_ hu
  filter_upwards [eventually_ge_atTop (16777216:ℝ)] with β hb
  exact averaged_badEnergy hb (g β)
end OperatorDerivativeRewrite.Foundation.PeriodicEndpointScore
