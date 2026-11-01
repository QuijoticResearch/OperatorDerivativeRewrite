import Foundation.PeriodicEndpointFibreWitness
/-! Endpoint-retaining physical middle response after actual temporal integration.
This conditioning differs from the stationary middle-only Ward projection. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.PeriodicPhysicalBridgeScore
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicEndpointScore
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar kernel

theorem kernel_left_right (β h : ℝ) (U V : State) :
    kernel β (left h U) V=kernel β (right (-h) U) V := by
  have he : left h U=gaugeAction (fun _ => SU2JointPlaquetteCubic.axis 0 h) (right (-h) U) := by
    funext e
    simp only [left,right,gaugeAction,neg_neg]
    group
  rw [he,kernel_left_invariant]

/-- A fixed diagonal pair has an EVEN actual middle bridge law. This is not
stationary endpoint averaging and does not require a gauge-invariant test. -/
theorem diagonal_law_even (β h : ℝ) (U : State) :
    PeriodicGroundBridge.law β (left h U) (right h U)=
      PeriodicGroundBridge.law β (left (-h) U) (right (-h) U) := by
  have he : PeriodicGroundBridge.bridgeWeight β (left h U) (right h U)=
      PeriodicGroundBridge.bridgeWeight β (left (-h) U) (right (-h) U) := by
    funext V
    unfold PeriodicGroundBridge.bridgeWeight
    simp_rw [kernel_left_right,neg_neg]
    rw [kernel_symmetric β V (right h U),kernel_symmetric β V (right (-h) U)]
    ring
  unfold PeriodicGroundBridge.law
  rw [he]

theorem diagonal_pairing_zero (β : ℝ) (U : State) (f : State → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0≤M) (hb : ∀ V,|f V|≤M) :
    (∫ q,f q.1*score β U U q ∂PeriodicAugmentedBridge.law β U U)=0 := by
  let F := fun h : ℝ => ∫ q,f q.1 ∂PeriodicAugmentedBridge.law β (left h U) (right h U)
  have hd := expectation_score β U U (fun q => f q.1) (hf.comp measurable_fst) M hM (fun q => hb q.1)
  have he : (fun h => F (-h))=F := by
    funext h
    dsimp only [F]
    rw [PeriodicAugmentedBridge.projection_integral β _ _ f hf M hb,
      PeriodicAugmentedBridge.projection_integral β _ _ f hf M hb,
      diagonal_law_even β h U]
  have hd0 : HasDerivAt F (∫ q,f q.1*score β U U q ∂PeriodicAugmentedBridge.law β U U) (-(0:ℝ)) := by
    simpa only [neg_zero] using hd
  have hn := hd0.comp 0 (hasDerivAt_neg (0:ℝ))
  change HasDerivAt (fun h => F (-h)) _ 0 at hn
  rw [he] at hn
  have hu := hd.unique hn
  nlinarith

def temporalReference : Measure (Gauge × Gauge) := gaugeHaar.prod gaugeHaar
private instance temporalReference_probability : IsProbabilityMeasure temporalReference := by unfold temporalReference; infer_instance

def auxiliaryWeight (β : ℝ) (U W V : State) (ab : Gauge × Gauge) : ℝ :=
  PeriodicAugmentedBridge.density β U W (V,ab)

private theorem auxiliaryWeight_measurable (β : ℝ) (U W V : State) : Measurable (auxiliaryWeight β U W V) :=
  (PeriodicAugmentedBridge.density_measurable β U W).comp (measurable_const.prodMk measurable_id)

private theorem auxiliaryWeight_integrable (β : ℝ) (U W V : State) :
    Integrable (auxiliaryWeight β U W V) temporalReference := by
  apply Integrable.of_bound (auxiliaryWeight_measurable β U W V).aestronglyMeasurable (Real.exp (768*|β|)^2)
  filter_upwards with ab
  change ‖PeriodicAugmentedBridge.density β U W (V,ab)‖≤_
  rw [Real.norm_eq_abs,abs_of_pos (PeriodicAugmentedBridge.density_pos β U W (V,ab))]
  exact PeriodicAugmentedBridge.density_upper β U W (V,ab)

private theorem auxiliary_mass (β : ℝ) (U W V : State) :
    SignedDensityProbabilitySampling.mass temporalReference (auxiliaryWeight β U W V)=
      PeriodicGroundBridge.bridgeWeight β U W V := by
  unfold SignedDensityProbabilitySampling.mass auxiliaryWeight
  simp_rw [abs_of_pos (PeriodicAugmentedBridge.density_pos β U W (V,_))]
  exact PeriodicAugmentedBridge.gauge_pair_integral β U W V

/-- Actual temporal conditional probability at FIXED U,W,V. -/
def auxiliaryLaw (β : ℝ) (U W V : State) : Measure (Gauge × Gauge) :=
  SignedDensityProbabilitySampling.sampler temporalReference (auxiliaryWeight β U W V)

theorem auxiliary_probability (β : ℝ) (U W V : State) : IsProbabilityMeasure (auxiliaryLaw β U W V) :=
  SignedDensityProbabilitySampling.sampler_probability temporalReference _ (auxiliaryWeight_integrable β U W V)
    (by rw [auxiliary_mass]; exact PeriodicGroundBridge.bridgeWeight_pos β U W V)

theorem auxiliary_integral (β : ℝ) (U W V : State) (f : Gauge × Gauge → ℝ) :
    (∫ ab,f ab ∂auxiliaryLaw β U W V)=
      (∫ ab,PeriodicAugmentedBridge.density β U W (V,ab)*f ab ∂temporalReference)/
        PeriodicGroundBridge.bridgeWeight β U W V := by
  have h := YMPositiveKernel.positive_sampler_integral temporalReference (auxiliaryWeight β U W V) f
    (auxiliaryWeight_measurable β U W V) (fun ab => (PeriodicAugmentedBridge.density_pos β U W (V,ab)).le)
    (by rw [auxiliary_mass]; exact PeriodicGroundBridge.bridgeWeight_pos β U W V)
  rw [auxiliary_mass] at h
  exact h

/-- Conditional physical score BEFORE endpoint averaging, using the actual two
Wilson temporal densities. This is not the stationary middle-only projection. -/
def physicalScore (β : ℝ) (U W : State) (V : State) : ℝ :=
  ∫ ab,score β U W (V,ab) ∂auxiliaryLaw β U W V

theorem physicalScore_measurable (β : ℝ) (U W : State) : Measurable (physicalScore β U W) := by
  have he : physicalScore β U W=(fun V =>
      (∫ ab,PeriodicAugmentedBridge.density β U W (V,ab)*score β U W (V,ab) ∂temporalReference)/
        PeriodicGroundBridge.bridgeWeight β U W V) := by
    funext V
    exact auxiliary_integral β U W V _
  rw [he]
  exact ((PeriodicAugmentedBridge.density_measurable β U W).mul (score_measurable β U W)).stronglyMeasurable.integral_prod_right.measurable.div
    (PeriodicGroundBridge.bridgeWeight_measurable β U W)

theorem physicalScore_bound (β : ℝ) (U W V : State) : |physicalScore β U W V|≤768*|β| := by
  letI := auxiliary_probability β U W V
  simpa only [physicalScore,Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ := auxiliaryLaw β U W V) (f := fun ab => score β U W (V,ab)) (C := 768*|β|)
    (ae_of_all _ (fun ab => by simpa only [Real.norm_eq_abs] using score_bound β U W (V,ab)))

theorem physicalScore_memLp (β : ℝ) (U W : State) :
    MemLp (physicalScore β U W) 2 (PeriodicGroundBridge.law β U W) :=
  MemLp.of_bound (physicalScore_measurable β U W).aestronglyMeasurable (768*|β|)
    (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using physicalScore_bound β U W V))

/-- Exact original-law duality with bounded middle observables. Both temporal
integrals and the true middle/conditional normalizers are retained. -/
theorem physical_pairing (β : ℝ) (U W : State) (f : State → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0≤M) (hb : ∀ V,|f V|≤M) :
    (∫ q,f q.1*score β U W q ∂PeriodicAugmentedBridge.law β U W)=
      ∫ V,f V*physicalScore β U W V ∂PeriodicGroundBridge.law β U W := by
  have hi : Integrable (fun q : PeriodicAugmentedBridge.Space =>
      PeriodicAugmentedBridge.density β U W q*(f q.1*score β U W q)) PeriodicAugmentedBridge.reference := by
    apply Integrable.of_bound ((PeriodicAugmentedBridge.density_measurable β U W).mul
      ((hf.comp measurable_fst).mul (score_measurable β U W))).aestronglyMeasurable
      ((Real.exp (768*|β|)^2)*(M*(768*|β|)))
    filter_upwards with q
    change ‖PeriodicAugmentedBridge.density β U W q*(f q.1*score β U W q)‖≤_
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (PeriodicAugmentedBridge.density_pos β U W q)]
    exact mul_le_mul (PeriodicAugmentedBridge.density_upper β U W q)
      (mul_le_mul (hb q.1) (score_bound β U W q) (abs_nonneg _) hM)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (sq_nonneg _)
  rw [PeriodicAugmentedBridge.integral_formula,PeriodicGroundBridge.integral_formula]
  congr 1
  rw [PeriodicAugmentedBridge.reference,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards with V
  rw [physicalScore,auxiliary_integral]
  have he : (fun ab : Gauge × Gauge => PeriodicAugmentedBridge.density β U W (V,ab)*(f V*score β U W (V,ab)))=
      (fun ab => f V*(PeriodicAugmentedBridge.density β U W (V,ab)*score β U W (V,ab))) := by
    funext ab
    ring
  rw [he,integral_const_mul]
  field_simp [(PeriodicGroundBridge.bridgeWeight_pos β U W V).ne']
  rfl

/-- Genuine physical middle response for the ACTUAL endpoint curve, on its
bounded measurable fixed-observable core. -/
theorem physical_derivative (β : ℝ) (U W : State) (f : State → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0≤M) (hb : ∀ V,|f V|≤M) :
    HasDerivAt (fun h => ∫ V,f V ∂PeriodicGroundBridge.law β (left h U) (right h W))
      (∫ V,f V*physicalScore β U W V ∂PeriodicGroundBridge.law β U W) 0 := by
  have h := expectation_score β U W (fun q => f q.1) (hf.comp measurable_fst) M hM (fun q => hb q.1)
  rw [physical_pairing β U W f hf M hM hb] at h
  convert h using 1
  funext h
  exact (PeriodicAugmentedBridge.projection_integral β _ _ f hf M hb).symm

/-- An admissible FROZEN physical score tests its own actual physical Fisher
energy. This energy must be proved nonzero separately for a nonzero response. -/
theorem frozen_physical_derivative (β : ℝ) (U W : State) :
    HasDerivAt (fun h => ∫ V,physicalScore β U W V
      ∂PeriodicGroundBridge.law β (left h U) (right h W))
      (∫ V,(physicalScore β U W V)^2 ∂PeriodicGroundBridge.law β U W) 0 := by
  simpa only [pow_two] using physical_derivative β U W (physicalScore β U W)
    (physicalScore_measurable β U W) (768*|β|) (mul_nonneg (by norm_num) (abs_nonneg _))
    (physicalScore_bound β U W)

theorem diagonal_physical_energy_zero (β : ℝ) (U : State) :
    (∫ V,(physicalScore β U U V)^2 ∂PeriodicGroundBridge.law β U U)=0 := by
  have h := diagonal_pairing_zero β U (physicalScore β U U) (physicalScore_measurable β U U)
    (768*|β|) (mul_nonneg (by norm_num) (abs_nonneg _)) (physicalScore_bound β U U)
  rw [physical_pairing β U U (physicalScore β U U) (physicalScore_measurable β U U)
    (768*|β|) (mul_nonneg (by norm_num) (abs_nonneg _)) (physicalScore_bound β U U)] at h
  simpa only [pow_two] using h

theorem diagonal_physical_zero (β : ℝ) (U : State) :
    physicalScore β U U=ᵐ[PeriodicGroundBridge.law β U U] 0 := by
  have hi := (physicalScore_memLp β U U).integrable_sq
  have hz := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun V => sq_nonneg (physicalScore β U U V))) hi).mp
    (diagonal_physical_energy_zero β U)
  filter_upwards [hz] with V hV
  change physicalScore β U U V=0
  change (physicalScore β U U V)^2=0 at hV
  nlinarith

private theorem right_weight_transform (β : ℝ) (g b : Gauge) (V W : State) :
    weight β (gaugeAction g V) W b=weight β V W (g⁻¹*b) := by
  have h := weight_left β g (g⁻¹*b) V W
  rw [show g*(g⁻¹*b)=b by group] at h
  exact h

private theorem density_middle_gauge (β : ℝ) (g : Gauge) (U W V : State) (ab : Gauge × Gauge) :
    PeriodicAugmentedBridge.density β U W (gaugeAction g V,ab)=
      PeriodicAugmentedBridge.density β U W (V,(ab.1*g,g⁻¹*ab.2)) := by
  simp only [PeriodicAugmentedBridge.density,weight_right,right_weight_transform]

private theorem direction_middle_gauge (g : Gauge) (U W V : State) (ab : Gauge × Gauge) :
    direction U W (gaugeAction g V,ab)=direction U W (V,(ab.1*g,g⁻¹*ab.2)) := by
  have hr (e : SpatialEdge) :
      halfTrace (temporalWord (gaugeAction g V) (right (Real.pi/2) W) ab.2 e)=
        halfTrace (temporalWord V (right (Real.pi/2) W) (g⁻¹*ab.2) e) := by
    have h := temporal_left_word g (g⁻¹*ab.2) V (right (Real.pi/2) W) e
    rw [show g*(g⁻¹*ab.2)=ab.2 by group] at h
    rw [h,halfTrace_conjugate]
  unfold direction traceSum
  simp_rw [temporal_right_word,hr]

private theorem score_middle_gauge (β : ℝ) (g : Gauge) (U W V : State) (ab : Gauge × Gauge) :
    score β U W (gaugeAction g V,ab)=score β U W (V,(ab.1*g,g⁻¹*ab.2)) := by
  unfold score
  rw [direction_middle_gauge]

/-- The endpoint-retaining physical score really is gauge invariant in the
middle field. No invariance in the fixed endpoint direction is asserted. -/
theorem physicalScore_gauge (β : ℝ) (g : Gauge) (U W V : State) :
    physicalScore β U W (gaugeAction g V)=physicalScore β U W V := by
  rw [physicalScore,auxiliary_integral,physicalScore,auxiliary_integral]
  have hn : PeriodicGroundBridge.bridgeWeight β U W (gaugeAction g V)=
      PeriodicGroundBridge.bridgeWeight β U W V := by
    unfold PeriodicGroundBridge.bridgeWeight
    rw [kernel_right_invariant,kernel_left_invariant]
  rw [hn]
  have h := ((gauge_right_preserving g).prod (gauge_left_preserving g⁻¹)).integral_comp
    ((MeasurableEquiv.mulRight g).prodCongr (MeasurableEquiv.mulLeft g⁻¹)).measurableEmbedding
    (fun ab : Gauge × Gauge => PeriodicAugmentedBridge.density β U W (V,ab)*score β U W (V,ab))
  change (∫ ab,PeriodicAugmentedBridge.density β U W (V,(ab.1*g,g⁻¹*ab.2))*
    score β U W (V,(ab.1*g,g⁻¹*ab.2)) ∂gaugeHaar.prod gaugeHaar)=
    (∫ ab,PeriodicAugmentedBridge.density β U W (V,ab)*score β U W (V,ab) ∂gaugeHaar.prod gaugeHaar) at h
  simp_rw [density_middle_gauge,score_middle_gauge]
  exact congrArg (fun x => x/PeriodicGroundBridge.bridgeWeight β U W V) h

/-- Actual conditional reconstruction has an exact residual. It does not turn
auxiliary Fisher information into physical information or a lower frame bound. -/
theorem fisher_decomposition (β : ℝ) (U W : State) :
    (∫ q, (score β U W q)^2 ∂PeriodicAugmentedBridge.law β U W) =
      (∫ V, (physicalScore β U W V)^2 ∂PeriodicGroundBridge.law β U W) +
      (∫ q, (score β U W q - physicalScore β U W q.1)^2
        ∂PeriodicAugmentedBridge.law β U W) := by
  let μ := PeriodicAugmentedBridge.law β U W
  let s := score β U W
  let t := fun q : PeriodicAugmentedBridge.Space => physicalScore β U W q.1
  have hs : MemLp s 2 μ := score_memLp β U W
  have ht : MemLp t 2 μ :=
    (physicalScore_memLp β U W).comp_measurePreserving
      (PeriodicAugmentedBridge.projection_preserving β U W)
  have hp := physical_pairing β U W (physicalScore β U W)
    (physicalScore_measurable β U W) (768 * |β|)
    (mul_nonneg (by norm_num) (abs_nonneg _)) (physicalScore_bound β U W)
  have hbound (V : State) : |(physicalScore β U W V)^2| ≤ (768 * |β|)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hb := physicalScore_bound β U W V
    nlinarith [sq_abs (physicalScore β U W V), abs_nonneg (physicalScore β U W V)]
  have hproj := PeriodicAugmentedBridge.projection_integral β U W
    (fun V => (physicalScore β U W V)^2)
    ((physicalScore_measurable β U W).pow_const 2) ((768 * |β|)^2) hbound
  have hx : (∫ q, t q * s q ∂μ) = ∫ q, (t q)^2 ∂μ := by
    rw [hproj]
    simpa only [pow_two] using hp
  have hid : (∫ q, (s q - t q)^2 ∂μ) =
      (∫ q, (s q)^2 ∂μ) + (∫ q, (t q)^2 ∂μ) - 2 * ∫ q, t q * s q ∂μ := by
    have he : (fun q => (s q - t q)^2) =
        (fun q => ((s q)^2 + (t q)^2) - 2 * (t q * s q)) := by
      funext q
      ring
    rw [he]
    have hi := integral_sub (hs.integrable_sq.add ht.integrable_sq)
      ((ht.integrable_mul hs).const_mul 2)
    simp only [Pi.add_apply, Pi.mul_apply] at hi
    rw [hi]
    have ha := integral_add hs.integrable_sq ht.integrable_sq
    rw [ha, integral_const_mul]
  change (∫ q, (s q)^2 ∂μ) = _
  rw [← hproj]
  change (∫ q, (s q)^2 ∂μ) = (∫ q, (t q)^2 ∂μ) + ∫ q, (s q - t q)^2 ∂μ
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicPhysicalBridgeScore
