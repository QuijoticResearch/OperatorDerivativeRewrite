import Foundation.PeriodicTransportedRoot
import Foundation.PeriodicFlatLocusQuarticObstruction
import Foundation.SU2TwoAxisStabilizerHaar
/-! Full64-variable temporal Haar control with the compact root integrated.
Transported root coordinates give a root-uniform189-power upper bound;
actual winding mismatch and Haar-nullness then prove an o(|t|^189) limit at
noncentral common-axis winding, unlike the positive fixed-root coefficient.
No191-power coefficient, stationary normalization or physical mass gap is claimed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Quaternion Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicRootHaarControl
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereJets
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicGaugeSaturatedGround PeriodicRelativeGaugeGaussian
open PeriodicFlatBackgroundHessian PeriodicTransportedRoot
open PeriodicRootedHaarControl (chartState budget)
open PeriodicRelativeGaugeTails (smallGauge smallGauge_measurable)
open PeriodicFullHaarGaussianLimit (chart density localField localField_measurable)
attribute [local irreducible] PeriodicWilsonSlab.weight chartState gaugeRay assemble framedGauge unframedGauge normalGauge

private theorem section_measurable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (f : A × B → C) (hf : Measurable f) (a : A) :
    Measurable (fun b => f (a,b)) := hf.comp (measurable_const.prodMk measurable_id)

def integrand (H : State) (X Y : Velocity) (t : ℝ) (p : SU2 × RelField) : ℝ :=
  PeriodicWilsonSlab.weight (1/t^2) (chartState H X t) (chartState H Y t) (fromCoordinates H p)

def rootBlock (H : State) (X Y : Velocity) (t : ℝ) (c : SU2) : ℝ := ∫ r,integrand H X Y t (c,r) ∂relFieldHaar
def interior (H : State) (X Y : Velocity) (t : ℝ) (c : SU2) : ℝ := ∫ r in localField,integrand H X Y t (c,r) ∂relFieldHaar
def exterior (H : State) (X Y : Velocity) (t : ℝ) (c : SU2) : ℝ := ∫ r in localFieldᶜ,integrand H X Y t (c,r) ∂relFieldHaar

theorem integrand_measurable (H : State) (X Y : Velocity) (t : ℝ) : Measurable (integrand H X Y t) :=
  (PeriodicAnchoredHaarLimit.weight_measurable _ _ _).comp (fromCoordinates_preserving H).measurable

theorem integrand_integrable (H : State) (X Y : Velocity) (t : ℝ) :
    Integrable (integrand H X Y t) (law.prod relFieldHaar) :=
  (fromCoordinates_preserving H).integrable_comp_of_integrable (weight_integrable _ _ _)

theorem section_integrable (H : State) (X Y : Velocity) (t : ℝ) (c : SU2) :
    Integrable (fun r => integrand H X Y t (c,r)) relFieldHaar := by
  apply Integrable.of_bound (section_measurable _ (integrand_measurable H X Y t) c).aestronglyMeasurable
    (Real.exp (768*|1/t^2|))
  filter_upwards [] with r
  rw [Real.norm_eq_abs,abs_of_pos (by unfold integrand PeriodicWilsonSlab.weight; exact Real.exp_pos _)]
  exact (weight_bounds _ _ _ _).2

theorem rootBlock_integrable (H : State) (X Y : Velocity) (t : ℝ) :
    Integrable (rootBlock H X Y t) law := (integrand_integrable H X Y t).integral_prod_left

theorem kernel_root_integral (H : State) (X Y : Velocity) (t : ℝ) :
    kernel (1/t^2) (chartState H X t) (chartState H Y t)=∫ c,rootBlock H X Y t c ∂law := by
  rw [kernel,integral_coordinates H _ (PeriodicAnchoredHaarLimit.weight_measurable _ _ _)]
  exact integral_prod _ (integrand_integrable H X Y t)

theorem block_split (H : State) (X Y : Velocity) (t : ℝ) (c : SU2) :
    rootBlock H X Y t c=interior H X Y t c+exterior H X Y t c :=
  (integral_add_compl localField_measurable (section_integrable H X Y t c)).symm

def scaledDensity (H : State) (X Y : Velocity) (t : ℝ) (c : SU2) (Z : Field) : ℝ :=
  density (t • Z)*localField.indicator (fun r => integrand H X Y t (c,r)) (chart (t • Z))

theorem scaledDensity_measurable (H : State) (X Y : Velocity) (t : ℝ) (c : SU2) :
    Measurable (scaledDensity H X Y t c) := by
  have hm := ((section_measurable _ (integrand_measurable H X Y t) c).indicator localField_measurable).comp
    (PeriodicFullHaarGaussianLimit.chart_measurable.comp (measurable_id.const_smul t))
  exact (PeriodicFullHaarGaussianLimit.density_measurable.comp (measurable_id.const_smul t)).mul hm

theorem scaledDensity_bound (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (c : SU2) (Z : Field) :
    ‖scaledDensity H X Y t c Z‖≤PeriodicAnchoredHaarLimit.majorant X Y Z := by
  unfold scaledDensity PeriodicAnchoredHaarLimit.majorant
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (PeriodicFullHaarGaussianLimit.density_nonneg _)]
  apply mul_le_mul (PeriodicFullHaarGaussianLimit.density_le_zero _) ?_ (abs_nonneg _)
    (PeriodicFullHaarGaussianLimit.density_nonneg _)
  by_cases hr : chart (t • Z)∈localField
  · rw [Set.indicator_of_mem hr,abs_of_pos (by unfold integrand PeriodicWilsonSlab.weight; exact Real.exp_pos _)]
    have hg := (PeriodicFullHaarGaussianLimit.small_assemble c (chart (t • Z))).mpr hr
    have hh := PeriodicTransportedRoot.inside_weight_bound H X Y Z c t ht (by
      unfold gaugeRay PeriodicRelativeGaugeGaussian.chartField
      exact hg)
    convert hh using 1
    unfold integrand fromCoordinates normalGauge gaugeRay PeriodicRelativeGaugeGaussian.chartField chart
    rfl
  · rw [Set.indicator_of_notMem hr,abs_zero]
    positivity

theorem scaledDensity_integrable (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (c : SU2) :
    Integrable (scaledDensity H X Y t c) :=
  (PeriodicAnchoredHaarLimit.majorant_integrable X Y).mono'
    (scaledDensity_measurable H X Y t c).aestronglyMeasurable (ae_of_all _ (scaledDensity_bound H X Y t ht c))

theorem interior_scaling (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (c : SU2) :
    interior H X Y t c/|t|^189=∫ Z : Field,scaledDensity H X Y t c Z := by
  have hs : interior H X Y t c=|t|^189*(∫ Z : Field,scaledDensity H X Y t c Z) := by
    rw [interior,PeriodicFullHaarGaussianLimit.integral_local _
      (section_measurable _ (integrand_measurable H X Y t) c),
      PeriodicFullHaarGaussianLimit.integral_rescale _ t ht]
    rfl
  apply (div_eq_iff (pow_ne_zero 189 (abs_ne_zero.mpr ht))).mpr
  rw [hs]
  ring

def gaussianBound (X Y : Velocity) : ℝ := ∫ Z : Field,PeriodicAnchoredHaarLimit.majorant X Y Z

theorem interior_scaled_bound (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (c : SU2) :
    interior H X Y t c/|t|^189≤gaussianBound X Y := by
  rw [interior_scaling H X Y t ht c]
  exact integral_mono (scaledDensity_integrable H X Y t ht c) (PeriodicAnchoredHaarLimit.majorant_integrable X Y)
    (fun Z => ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm).trans (scaledDensity_bound H X Y t ht c Z))

theorem exterior_nonneg (H : State) (X Y : Velocity) (t : ℝ) (c : SU2) : 0≤exterior H X Y t c := by
  unfold exterior
  apply integral_nonneg
  intro r
  unfold integrand PeriodicWilsonSlab.weight
  exact (Real.exp_pos _).le

theorem exterior_bound (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (c : SU2) :
    exterior H X Y t c≤Real.exp (budget X Y)*Real.exp (-PeriodicRootedHaarControl.exteriorRate/t^2) := by
  let C := Real.exp (budget X Y)*Real.exp (-PeriodicRootedHaarControl.exteriorRate/t^2)
  have hh := norm_setIntegral_le_of_norm_le_const (μ := relFieldHaar) (s := localFieldᶜ)
    (f := fun r => integrand H X Y t (c,r)) (measure_lt_top _ _) (fun r hr => by
      rw [Real.norm_eq_abs,abs_of_pos (by unfold integrand PeriodicWilsonSlab.weight; exact Real.exp_pos _)]
      apply PeriodicTransportedRoot.outside_weight_bound H X Y t ht (fromCoordinates H (c,r))
      unfold fromCoordinates
      rw [framed_unframed]
      exact fun hg => hr ((PeriodicFullHaarGaussianLimit.small_assemble c r).mp hg))
  have hm : relFieldHaar.real localFieldᶜ≤1 := measureReal_le_one
  have hc : 0≤C := by unfold C; positivity
  have hi := mul_le_mul_of_nonneg_left hm hc
  simp only [mul_one] at hi
  exact (le_abs_self _).trans (hh.trans hi)

def tailBound (X Y : Velocity) (t : ℝ) : ℝ :=
  Real.exp (budget X Y)*(Real.exp (-PeriodicRelativeGaugeTails.exteriorRate/t^2)/|t|^189)

theorem tailBound_limit (X Y : Velocity) : Tendsto (tailBound X Y) (𝓝[≠] 0) (𝓝 0) := by
  change Tendsto (fun t : ℝ => Real.exp (budget X Y)*(Real.exp (-PeriodicRelativeGaugeTails.exteriorRate/t^2)/|t|^189)) (𝓝[≠] 0) (𝓝 0)
  simpa only [mul_zero] using PeriodicRelativeGaugeTails.exponential_scale_limit.const_mul (Real.exp (budget X Y))

theorem exterior_scaled_bound (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (c : SU2) :
    exterior H X Y t c/|t|^189≤tailBound X Y t := by
  have hb := exterior_bound H X Y t ht c
  have hr : PeriodicRelativeGaugeTails.exteriorRate≤PeriodicRootedHaarControl.exteriorRate := by
    norm_num [PeriodicRelativeGaugeTails.exteriorRate,PeriodicRootedHaarControl.exteriorRate]
  have he : Real.exp (-PeriodicRootedHaarControl.exteriorRate/t^2)≤
      Real.exp (-PeriodicRelativeGaugeTails.exteriorRate/t^2) := by
    apply Real.exp_le_exp.mpr
    have hd := div_le_div_of_nonneg_right hr (sq_nonneg t)
    simpa only [neg_div] using neg_le_neg hd
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (budget X Y)).le
  have hd := div_le_div_of_nonneg_right (hb.trans hm) (by positivity : (0 : ℝ)≤|t|^189)
  simpa only [tailBound,mul_div_assoc] using hd

theorem rootBlock_scaled_bound (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (c : SU2) :
    rootBlock H X Y t c/|t|^189≤gaussianBound X Y+tailBound X Y t := by
  rw [block_split,add_div]
  exact add_le_add (interior_scaled_bound H X Y t ht c) (exterior_scaled_bound H X Y t ht c)

theorem kernel_scaled_bound (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) :
    kernel (1/t^2) (chartState H X t) (chartState H Y t)/|t|^189≤gaussianBound X Y+tailBound X Y t := by
  rw [kernel_root_integral,← integral_div]
  have hh := integral_mono ((rootBlock_integrable H X Y t).div_const (|t|^189))
    (integrable_const (gaussianBound X Y+tailBound X Y t)) (rootBlock_scaled_bound H X Y t ht)
  simpa only [integral_const,probReal_univ,one_smul] using hh


open PeriodicLoopVariation (distance)

def mismatchRate (H : State) (i : Fin 3) (c : SU2) : ℝ :=
  distance (PeriodicSpatialHolonomy.winding H root i)
    (c*PeriodicSpatialHolonomy.winding H root i*c⁻¹)^2/96

theorem mismatch_weight_bound (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0)
    (i : Fin 3) (c : SU2) (r : RelField) :
    integrand H X Y t (c,r)≤Real.exp (budget X Y)*Real.exp (-mismatchRate H i c/t^2) := by
  have hh := PeriodicFlatLocusQuarticObstruction.winding_square_temporal H H (fromCoordinates H (c,r)) root i
  rw [PeriodicSpatialHolonomy.winding_gauge] at hh
  have hr : fromCoordinates H (c,r) root=c := (unframed_root H _).trans (assemble_root _ _)
  rw [hr] at hh
  have hc := PeriodicRootedHaarControl.ray_comparison H X Y t (fromCoordinates H (c,r))
  have hl : mismatchRate H i c≤temporalAction (chartState H X t) (chartState H Y t)
      (fromCoordinates H (c,r))+t^2*budget X Y := by
    unfold mismatchRate
    linarith
  have ha := PeriodicRelativeGaugeTails.halfAction_temporal (chartState H X t) (chartState H Y t)
    (fromCoordinates H (c,r))
  have hb : mismatchRate H i c/t^2≤halfAction (chartState H X t) (chartState H Y t)
      (fromCoordinates H (c,r))/t^2+budget X Y := by
    apply (div_le_iff₀ (sq_pos_of_ne_zero ht)).mpr
    rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 ht)]
    nlinarith
  rw [← Real.exp_add]
  unfold integrand PeriodicWilsonSlab.weight
  apply Real.exp_le_exp.mpr
  simp only [div_eq_mul_inv,one_mul] at hb ⊢
  linarith

theorem mismatch_block_bound (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (i : Fin 3) (c : SU2) :
    rootBlock H X Y t c≤Real.exp (budget X Y)*Real.exp (-mismatchRate H i c/t^2) := by
  have hh := integral_mono (section_integrable H X Y t c) (integrable_const _)
    (mismatch_weight_bound H X Y t ht i c)
  simpa only [rootBlock,integral_const,probReal_univ,one_smul] using hh

theorem rootBlock_nonneg (H : State) (X Y : Velocity) (t : ℝ) (c : SU2) : 0≤rootBlock H X Y t c := by
  unfold rootBlock
  apply integral_nonneg
  intro r
  unfold integrand PeriodicWilsonSlab.weight
  exact (Real.exp_pos _).le

theorem exponential_scale_limit (rate : ℝ) (hRate : 0<rate) :
    Tendsto (fun t : ℝ => Real.exp (-rate/t^2)/|t|^189) (𝓝[≠] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (95 : ℝ) rate hRate).comp
    FourCubeHaarPartitionAsymptotic.inverse_square_tendsto
  simp only [Real.rpow_ofNat,Function.comp_def] at h
  have h190 : Tendsto (fun t : ℝ => Real.exp (-rate/t^2)/|t|^190) (𝓝[≠] 0) (𝓝 0) := by
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hp : |t|^(190 : ℕ)=(t^2)^(95 : ℕ) := by
      calc
        _ = (|t|^2)^95 := by rw [← pow_mul]
        _ = _ := by rw [sq_abs]
    rw [div_pow,one_pow,← hp]
    have he : -rate*(1/t^2)=-rate/t^2 := by ring
    rw [he]
    ring
  have hz : Tendsto (fun t : ℝ => |t|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero] using continuous_abs.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ)≤𝓝 0)
  have hh := hz.mul h190
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : |t|≠0 := abs_ne_zero.mpr ht
  rw [show (190 : ℕ)=189+1 by decide,pow_succ]
  field_simp

theorem noncritical_block_limit (H : State) (X Y : Velocity) (i : Fin 3) (c : SU2)
    (hc : 0<mismatchRate H i c) :
    Tendsto (fun t : ℝ => rootBlock H X Y t c/|t|^189) (𝓝[≠] 0) (𝓝 0) := by
  have hh := (exponential_scale_limit _ hc).const_mul (Real.exp (budget X Y))
  simp only [mul_zero] at hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t =>
    div_nonneg (rootBlock_nonneg H X Y t c) (by positivity))) ?_ hh
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hb := div_le_div_of_nonneg_right (mismatch_block_bound H X Y t ht i c) (by positivity : (0 : ℝ)≤|t|^189)
  simpa only [mul_div_assoc] using hb

theorem kernel_scaled_limit_of_ae_mismatch (H : State) (X Y : Velocity) (i : Fin 3)
    (hc : ∀ᵐ c ∂law,0<mismatchRate H i c) :
    Tendsto (fun t : ℝ => kernel (1/t^2) (chartState H X t) (chartState H Y t)/|t|^189)
      (𝓝[≠] 0) (𝓝 0) := by
  have hm (t : ℝ) : AEStronglyMeasurable (fun c => rootBlock H X Y t c/|t|^189) law :=
    ((rootBlock_integrable H X Y t).div_const _).aestronglyMeasurable
  have hb : ∀ᶠ t : ℝ in 𝓝[≠] 0,∀ᵐ c ∂law,‖rootBlock H X Y t c/|t|^189‖≤gaussianBound X Y+1 := by
    filter_upwards [self_mem_nhdsWithin,(tailBound_limit X Y).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1))] with t ht ht'
    apply ae_of_all
    intro c
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (rootBlock_nonneg H X Y t c) (by positivity))]
    exact (rootBlock_scaled_bound H X Y t ht c).trans (by linarith)
  have hh : Tendsto (fun t : ℝ => ∫ c,rootBlock H X Y t c/|t|^189 ∂law) (𝓝[≠] 0) (𝓝 (∫ c : SU2,(0 : ℝ) ∂law)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => gaussianBound X Y+1)
    · exact Filter.Eventually.of_forall hm
    · exact hb
    · exact integrable_const _
    · filter_upwards [hc] with c hc
      exact noncritical_block_limit H X Y i c hc
  simp only [integral_zero] at hh
  convert hh using 1
  funext t
  rw [kernel_root_integral,integral_div]


open ProbabilityTheory
open PeriodicLoopVariation (lift)

private theorem gaussianDirection_imJ (x : Raw) (hx : x≠0) :
    (lift (gaussianDirection x)).imJ=x 2/‖WithLp.toLp 2 x‖ := by
  have hlp : WithLp.toLp 2 x≠0 := by simpa using hx
  unfold lift gaussianDirection
  change ((equiv.symm (equiv (QuaternionAngularHaar.direction (WithLp.toLp 2 x))) : QuaternionAngularHaar.Group) : ℍ).imJ=_
  rw [equiv.symm_apply_apply]
  change (QuaternionAngularHaar.rawDirection (WithLp.toLp 2 x)).imJ=_
  rw [QuaternionAngularHaar.rawDirection,if_neg hlp]
  change (NormedSpace.normalize (WithLp.toLp 2 x)) 2=_
  simp [NormedSpace.normalize,div_eq_mul_inv,mul_comm]

theorem imJ_ae_ne_zero : ∀ᵐ c ∂law,(lift c).imJ≠0 := by
  have hm : Continuous (fun c : SU2 => (lift c).imJ) :=
    Quaternion.continuous_imJ.comp (continuous_subtype_val.comp homeomorph.symm.continuous)
  rw [← gaussianDirection_law]
  apply (ae_map_iff gaussianDirection_measurable.aemeasurable
    (hm.measurable (measurableSet_singleton 0).compl)).mpr
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hh : ∀ᵐ x ∂Measure.pi (fun _ : Fin 4 => gaussianReal 0 1),x 2≠0 :=
    (measurePreserving_eval (fun _ : Fin 4 => gaussianReal 0 1) 2).quasiMeasurePreserving.ae
      ((gaussianReal 0 1).ae_ne 0)
  filter_upwards [hh,rawGaussian_ae_ne_zero] with x hx hx'
  rw [gaussianDirection_imJ x hx']
  exact div_ne_zero hx (norm_ne_zero_iff.mpr (by simpa using hx'))

theorem axis_turn_ae_pos (θ : ℝ) (hθ : Real.sin θ≠0) :
    ∀ᵐ c ∂law,0<SU2TwoAxisStabilizerHaar.turn 0 θ c := by
  filter_upwards [imJ_ae_ne_zero] with c hc
  have hh := SU2TwoAxisStabilizerHaar.turn_zero_square θ c
  have hp : 0<4*Real.sin θ^2*((lift c).imJ^2+(lift c).imK^2) :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hθ))
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hc) (sq_nonneg _))
  nlinarith [SU2TwoAxisStabilizerHaar.turn_nonneg 0 θ c]


theorem axis_winding_mismatch_ae (H : State) (i : Fin 3) (θ : ℝ)
    (hw : PeriodicSpatialHolonomy.winding H root i=SU2JointPlaquetteCubic.axis 0 θ)
    (hθ : Real.sin θ≠0) : ∀ᵐ c ∂law,0<mismatchRate H i c := by
  filter_upwards [axis_turn_ae_pos θ hθ] with c hc
  have he : mismatchRate H i c=SU2TwoAxisStabilizerHaar.turn 0 θ c^2/96 := by
    unfold mismatchRate SU2TwoAxisStabilizerHaar.turn
    rw [hw]
    unfold distance
    rw [norm_sub_rev]
  rw [he]
  exact div_pos (sq_pos_of_pos hc) (by norm_num)

theorem kernel_scaled_limit_of_axis_winding (H : State) (X Y : Velocity) (i : Fin 3) (θ : ℝ)
    (hw : PeriodicSpatialHolonomy.winding H root i=SU2JointPlaquetteCubic.axis 0 θ)
    (hθ : Real.sin θ≠0) :
    Tendsto (fun t : ℝ => kernel (1/t^2) (chartState H X t) (chartState H Y t)/|t|^189)
      (𝓝[≠] 0) (𝓝 0) :=
  kernel_scaled_limit_of_ae_mismatch H X Y i (axis_winding_mismatch_ae H i θ hw hθ)

theorem commonAxis_winding (α : Fin 3 → ℝ) (i : Fin 3) :
    PeriodicSpatialHolonomy.winding (PeriodicAnchoredHaarLimit.base (PeriodicChargedFourier.background α)) root i=
      SU2JointPlaquetteCubic.axis 0 (4*α i) := by
  change SU2JointPlaquetteCubic.axis 0 (α i)*SU2JointPlaquetteCubic.axis 0 (α i)*
    SU2JointPlaquetteCubic.axis 0 (α i)*SU2JointPlaquetteCubic.axis 0 (α i)=_
  exact PeriodicFlatLocusQuarticObstruction.winding_field_zero (α i) root

/-- The full64-variable Haar kernel loses the positive189-power coefficient
of the fixed-identity-root block when a common-axis winding is noncentral.
No191-power coefficient or native stationary normalization is asserted. -/
theorem commonAxis_kernel_scaled_limit (α : Fin 3 → ℝ) (X Y : Velocity) (i : Fin 3)
    (hi : Real.sin (4*α i)≠0) :
    Tendsto (fun t : ℝ => kernel (1/t^2)
      (chartState (PeriodicAnchoredHaarLimit.base (PeriodicChargedFourier.background α)) X t)
      (chartState (PeriodicAnchoredHaarLimit.base (PeriodicChargedFourier.background α)) Y t)/|t|^189)
      (𝓝[≠] 0) (𝓝 0) :=
  kernel_scaled_limit_of_axis_winding _ X Y i (4*α i) (commonAxis_winding α i) hi

/-- Actual full-Haar / fixed-root block ratio tends to zero on the stated
noncentral-winding stratum. Replacing one by the other is therefore invalid. -/
theorem commonAxis_full_to_fixed_ratio (α : Fin 3 → ℝ) (X Y : Velocity) (i : Fin 3)
    (hi : Real.sin (4*α i)≠0) :
    Tendsto (fun t : ℝ => kernel (1/t^2)
      (chartState (PeriodicAnchoredHaarLimit.base (PeriodicChargedFourier.background α)) X t)
      (chartState (PeriodicAnchoredHaarLimit.base (PeriodicChargedFourier.background α)) Y t)/
      PeriodicAnchoredHaarLimit.block (PeriodicAnchoredHaarLimit.base (PeriodicChargedFourier.background α)) X Y t)
      (𝓝[≠] 0) (𝓝 0) := by
  have hh := (commonAxis_kernel_scaled_limit α X Y i hi).div
    (PeriodicAnchoredHaarLimit.block_scaled_limit _ X Y (PeriodicChargedFourier.background_commutes α))
    (PeriodicAnchoredHaarLimit.coefficient_pos _ X Y).ne'
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact div_div_div_cancel_right₀ (pow_ne_zero 189 (abs_ne_zero.mpr ht)) _ _

end OperatorDerivativeRewrite.Foundation.PeriodicRootHaarControl
