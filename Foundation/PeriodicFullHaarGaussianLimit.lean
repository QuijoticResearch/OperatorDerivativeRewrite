import Foundation.PeriodicRelativeGaugeTails
/-! Actual full64-vertex temporal Haar-kernel asymptotics on constant Wilson
chart rays. Exact63-relative chart transport and the genuine absolute189-power
Jacobian combine with the verified cap domination and exterior suppression.
The leading coefficient is positive and finite; the vacuum-diagonal ratio
converges to the common-root Gaussian kernel. This is a pointwise raw-kernel
statement, not stationary ground normalization or a spectral/mass-gap theorem. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicFullHaarGaussianLimit
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open SU2HemisphereJets (sizeSq)
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicConstantQuarticJet PeriodicConstantRootLimit
open PeriodicGaugeSaturatedGround PeriodicRelativeGaugeGaussian PeriodicRelativeGaugeTails
open SU2HaarLaplaceUpper
open FourCubePinnedCoercivity
open FourCubeHaarProductCoordinates (coordinateLaw coordinateLaw_finite chart_map_coordinateLaw
  chartDensity_nonneg chartDensity_measurable chartDensity_integrable coordinateLaw_apply_integral)
attribute [local irreducible] weight kernel halfAction temporalAction spatialAction SU2RootAdjoint.rotate
attribute [local irreducible] assemble gaugeRay

abbrev Field := RelFieldIndex → Triple

def chart (Y : Field) : RelField := fun v => hemisphereChart (Y v)
def jointHemisphere : Set RelField := Set.univ.pi (fun _ => hemisphere)
def localField : Set RelField := Set.univ.pi (fun _ => localCut)
def chartLaw : Measure Field := Measure.pi (fun _ : RelFieldIndex => coordinateLaw)
private instance chartLaw_finite : IsFiniteMeasure chartLaw := by unfold chartLaw; infer_instance

theorem chart_measurable : Measurable chart :=
  measurable_pi_iff.mpr (fun v => SU2HemisphereChart.chart_measurable.comp (measurable_pi_apply v))
theorem localField_measurable : MeasurableSet localField :=
  MeasurableSet.univ_pi (fun _ => localCut_measurable)
theorem localField_subset : localField ⊆ jointHemisphere := by
  intro h hh v hv
  exact localCut_subset (hh v hv)

theorem chart_map : chartLaw.map chart=relFieldHaar.restrict jointHemisphere := by
  rw [show relFieldHaar.restrict jointHemisphere=
    Measure.pi (fun _ : RelFieldIndex => law.restrict hemisphere) from
    Measure.restrict_pi_pi (fun _ : RelFieldIndex => law) (fun _ => hemisphere)]
  have hh := Measure.pi_map_pi (fun _ : RelFieldIndex => SU2HemisphereChart.chart_measurable.aemeasurable (μ := coordinateLaw))
  change (Measure.pi (fun _ : RelFieldIndex => coordinateLaw)).map chart=_
  rw [chart_map_coordinateLaw] at hh
  exact hh

def density (Y : Field) : ℝ := ∏ v,chartDensity (Y v)
theorem density_nonneg (Y : Field) : 0 ≤ density Y :=
  Finset.prod_nonneg (fun v _ => chartDensity_nonneg (Y v))
theorem density_measurable : Measurable density := by
  unfold density
  exact Finset.measurable_prod _ (fun v _ => chartDensity_measurable.comp (measurable_pi_apply v))
theorem density_integrable : Integrable density := by
  rw [show density=(fun Y : Field => ∏ v,chartDensity (Y v)) from rfl,volume_pi]
  exact Integrable.fintype_prod (fun _ : RelFieldIndex => chartDensity_integrable)

private theorem integral_density_box (s : RelFieldIndex → Set Triple) (hs : ∀ e,MeasurableSet (s e)) :
    (∫ Y in Set.univ.pi s,density Y)=∏ e : RelFieldIndex,∫ y in s e,chartDensity y := by
  have hi : (Set.univ.pi s).indicator density=
      (fun Y : Field => ∏ e : RelFieldIndex,(s e).indicator chartDensity (Y e)) := by
    funext Y
    by_cases hY : Y∈Set.univ.pi s
    · have hy : ∀ e,Y e∈s e := by simpa only [Set.mem_pi,Set.mem_univ,true_implies] using hY
      rw [Set.indicator_of_mem hY]
      unfold density
      apply Finset.prod_congr rfl
      intro e _
      exact (Set.indicator_of_mem (hy e) _).symm
    · rw [Set.indicator_of_notMem hY]
      have hy : ¬ ∀ e,Y e∈s e := by simpa only [Set.mem_pi,Set.mem_univ,true_implies] using hY
      push_neg at hy
      obtain ⟨e,he⟩ := hy
      exact (Finset.prod_eq_zero (Finset.mem_univ e) (Set.indicator_of_notMem he _)).symm
  rw [← integral_indicator (MeasurableSet.univ_pi hs),hi,volume_pi,
    integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro e _
  exact integral_indicator (hs e)

theorem chartLaw_density : chartLaw=
    (volume : Measure Field).withDensity (fun Y => ENNReal.ofReal (density Y)) := by
  unfold chartLaw
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal density_integrable.integrableOn
      (ae_of_all _ density_nonneg),integral_density_box s hs,
    ENNReal.ofReal_prod_of_nonneg (fun e _ => integral_nonneg (fun y => chartDensity_nonneg y))]
  apply Finset.prod_congr rfl
  intro e _
  exact (coordinateLaw_apply_integral (s e) (hs e)).symm


/-- Exact actual local Haar integral, with every cutoff and density factor retained. -/
theorem integral_local (f : RelField → ℝ) (hf : Measurable f) :
    (∫ h in localField,f h ∂relFieldHaar)=
      ∫ Y : Field,density Y*localField.indicator f (chart Y) := by
  classical
  have hm := hf.indicator localField_measurable
  have h := integral_map (μ := chartLaw) chart_measurable.aemeasurable hm.aestronglyMeasurable
  rw [chart_map,integral_indicator localField_measurable,
    Measure.restrict_restrict_of_subset localField_subset] at h
  rw [chartLaw_density,integral_withDensity_eq_integral_toReal_smul
    density_measurable.ennreal_ofReal (ae_of_all volume (fun _ => ENNReal.ofReal_lt_top))] at h
  simpa only [ENNReal.toReal_ofReal (density_nonneg _),smul_eq_mul] using h

theorem field_finrank : Module.finrank ℝ Field=189 := by
  change Module.finrank ℝ (RelFieldIndex → Fin 3 → ℝ)=189
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fin_fun,Finset.sum_const,Finset.card_univ,rel_count]
  norm_num

theorem integral_rescale (f : Field → ℝ) (t : ℝ) (ht : t ≠ 0) :
    (∫ Y : Field,f Y)=|t|^189*(∫ Y : Field,f (t • Y)) := by
  have hh := Measure.integral_comp_smul (volume : Measure Field) f t
  rw [field_finrank,smul_eq_mul,abs_inv,abs_pow] at hh
  rw [hh]
  have hp : |t|^189 ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr ht)
  field_simp


theorem assemble_relative (c : SU2) (h : RelField) (v : SpatialVertex) :
    assemble c h v*(assemble c h root)⁻¹=anchored h v := by
  rw [assemble_root]
  unfold assemble
  group

theorem small_assemble (c : SU2) (h : RelField) : assemble c h∈smallGauge ↔ h∈localField := by
  constructor
  · intro hg v hv
    have hh := hg v.val
    rw [assemble_relative] at hh
    change defect (h v)<1/4
    simpa only [anchored,dif_neg v.property] using hh
  · intro hh v
    change defect (assemble c h v*(assemble c h root)⁻¹)<1/4
    rw [assemble_relative]
    unfold anchored
    split_ifs with hv
    · rw [FourCubePinnedCoercivity.defect_one]
      norm_num
    · exact hh ⟨v,hv⟩ (Set.mem_univ _)

theorem indicator_assemble (f : Gauge → ℝ) (c : SU2) (h : RelField) :
    smallGauge.indicator f (assemble c h)=localField.indicator (fun h => f (assemble c h)) h := by
  classical
  by_cases hh : h∈localField
  · rw [Set.indicator_of_mem ((small_assemble c h).mpr hh),Set.indicator_of_mem hh]
  · rw [Set.indicator_of_notMem (fun hn => hh ((small_assemble c h).mp hn)),Set.indicator_of_notMem hh]

theorem density_le_zero (Z : Field) : density Z≤density 0 := by
  exact Finset.prod_le_prod₀ (fun v _ => chartDensity_nonneg (Z v))
    (fun v _ => FourCubeHaarLaplaceDensity.chartDensity_le_zero (Z v))

theorem density_continuous : Continuous density :=
  continuous_finsetProd _ (fun v _ =>
    FourCubeHaarLaplaceDensity.chartDensity_continuous.comp (continuous_apply v))

theorem density_positive (Z : Field) : 0<density Z :=
  Finset.prod_pos (fun v _ => FourCubeHaarLaplaceDensity.chartDensity_positive (Z v))

theorem density_zero : density (0 : Field)=chartDensity 0^63 := by
  simp [density,rel_count]

theorem gaugeRay_measurable (t : ℝ) :
    Measurable (fun p : SU2 × Field => gaugeRay p.2 p.1 t) := by
  have he : (fun p : SU2 × Field => gaugeRay p.2 p.1 t)=
      (fun p : SU2 × Field => assemble p.1 (chart (t • p.2))) := by
    funext p
    unfold gaugeRay PeriodicRelativeGaugeGaussian.chartField chart
    rfl
  rw [he]
  have hm : Measurable (fun p : SU2 × Field => chart (t • p.2)) :=
    chart_measurable.comp (measurable_snd.const_smul t)
  exact assemble_measurable.comp (measurable_fst.prodMk hm)

theorem weight_measurable (β : ℝ) (U V : State) : Measurable (weight β U V) :=
  (weight_joint_measurable β).comp
    ((measurable_const : Measurable (fun _ : Gauge => (U,V))).prodMk measurable_id)

theorem cutoffWeight_joint_measurable (a b : Velocities) (t : ℝ) :
    Measurable (fun p : SU2 × Field => cutoffWeight a b t p.1 p.2) :=
  ((weight_measurable (1/t^2) (constantState a t) (constantState b t)).indicator
    smallGauge_measurable).comp (gaugeRay_measurable t)

def scaledDensity (a b : Velocities) (t : ℝ) (p : SU2 × Field) : ℝ :=
  density (t • p.2)*cutoffWeight a b t p.1 p.2

def gaussianDensity (a b : Velocities) (p : SU2 × Field) : ℝ :=
  density 0*(gaussianIntegrand a b p.1*Real.exp (-graphEnergy p.2))

def majorant (a b : Velocities) (p : SU2 × Field) : ℝ :=
  density 0*(Real.exp (sourceBudget a b)*Real.exp (-envelopeRate*fieldSizeSq p.2))

theorem scaledDensity_measurable (a b : Velocities) (t : ℝ) : Measurable (scaledDensity a b t) :=
  (density_measurable.comp (measurable_snd.const_smul t)).mul (cutoffWeight_joint_measurable a b t)

theorem scaledDensity_bound (a b : Velocities) (t : ℝ) (ht : t≠0) (p : SU2 × Field) :
    ‖scaledDensity a b t p‖≤majorant a b p := by
  unfold scaledDensity majorant
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (density_nonneg _)]
  exact mul_le_mul (density_le_zero _) (cutoffWeight_bound a b t ht p.1 p.2)
    (abs_nonneg _) (density_nonneg _)

theorem majorant_integrable (a b : Velocities) : Integrable (majorant a b) (law.prod volume) := by
  have hi := (integrable_const (μ := law) (1 : ℝ)).mul_prod
    ((gaussian_envelope_integrable a b).const_mul (density 0))
  unfold majorant
  simpa only [one_mul] using hi

theorem scaledDensity_integrable (a b : Velocities) (t : ℝ) (ht : t≠0) :
    Integrable (scaledDensity a b t) (law.prod volume) :=
  (majorant_integrable a b).mono' (scaledDensity_measurable a b t).aestronglyMeasurable
    (ae_of_all _ (scaledDensity_bound a b t ht))

theorem scaledDensity_tendsto (a b : Velocities) (p : SU2 × Field) :
    Tendsto (fun t : ℝ => scaledDensity a b t p) (𝓝[≠] 0) (𝓝 (gaussianDensity a b p)) := by
  have hz : Tendsto (fun t : ℝ => t • p.2) (𝓝[≠] 0) (𝓝 (0 : Field)) := by
    have hc : Continuous (fun t : ℝ => t • p.2) := continuous_id.smul continuous_const
    simpa only [zero_smul] using
      hc.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ)≤𝓝 0)
  exact ((density_continuous.tendsto 0).comp hz).mul (cutoffWeight_tendsto a b p.1 p.2)

theorem scaledDensity_integral_tendsto (a b : Velocities) :
    Tendsto (fun t : ℝ => ∫ p,scaledDensity a b t p ∂law.prod volume) (𝓝[≠] 0)
      (𝓝 (∫ p,gaussianDensity a b p ∂law.prod volume)) := by
  apply tendsto_integral_filter_of_dominated_convergence (majorant a b)
  · exact Filter.Eventually.of_forall (fun t => (scaledDensity_measurable a b t).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ae_of_all _ (scaledDensity_bound a b t ht)
  · exact majorant_integrable a b
  · exact ae_of_all _ (scaledDensity_tendsto a b)

theorem interior_root_iterated (a b : Velocities) (t : ℝ) :
    insidePartition a b t=∫ c,∫ h in localField,
      weight (1/t^2) (constantState a t) (constantState b t) (assemble c h) ∂relFieldHaar ∂law := by
  have hm := weight_measurable (1/t^2) (constantState a t) (constantState b t)
  have hi := assemble_preserving.integrable_comp_of_integrable
    ((weight_integrable (1/t^2) (constantState a t) (constantState b t)).indicator smallGauge_measurable)
  change Integrable (fun p : SU2 × RelField => smallGauge.indicator
    (weight (1/t^2) (constantState a t) (constantState b t)) (assemble p.1 p.2)) (law.prod relFieldHaar) at hi
  rw [insidePartition,← integral_indicator smallGauge_measurable,integral_split _ (hm.indicator smallGauge_measurable)]
  rw [integral_prod _ hi]
  simp_rw [indicator_assemble,integral_indicator localField_measurable]

theorem interior_root_chart (a b : Velocities) (t : ℝ) :
    insidePartition a b t=∫ c,∫ Z : Field,density Z*localField.indicator
      (fun h => weight (1/t^2) (constantState a t) (constantState b t) (assemble c h)) (chart Z) ∂volume ∂law := by
  rw [interior_root_iterated]
  apply integral_congr_ae
  filter_upwards with c
  apply integral_local
  have hm : Measurable (fun h : RelField => assemble c h) :=
    assemble_measurable.comp ((measurable_const : Measurable (fun _ : RelField => c)).prodMk measurable_id)
  exact (weight_measurable (1/t^2) (constantState a t) (constantState b t)).comp hm

theorem coordinate_rescale (a b : Velocities) (t : ℝ) (ht : t≠0) (c : SU2) :
    (∫ Z : Field,density Z*localField.indicator
      (fun h => weight (1/t^2) (constantState a t) (constantState b t) (assemble c h)) (chart Z))=
      |t|^189*(∫ Z : Field,scaledDensity a b t (c,Z)) := by
  rw [integral_rescale _ t ht]
  congr 1
  apply integral_congr_ae
  filter_upwards with Z
  have he := indicator_assemble (weight (1/t^2) (constantState a t) (constantState b t)) c (chart (t • Z))
  rw [← he]
  unfold scaledDensity cutoffWeight gaugeRay PeriodicRelativeGaugeGaussian.chartField chart
  rfl

theorem interior_scaled (a b : Velocities) (t : ℝ) (ht : t≠0) :
    insidePartition a b t/|t|^189=∫ p,scaledDensity a b t p ∂law.prod volume := by
  apply (div_eq_iff (pow_ne_zero 189 (abs_ne_zero.mpr ht))).mpr
  rw [interior_root_chart]
  simp_rw [coordinate_rescale a b t ht]
  rw [integral_const_mul,integral_prod _ (scaledDensity_integrable a b t ht)]
  ring

def leadingConstant : ℝ := density 0*graphGaussianMass

theorem leadingConstant_pos : 0<leadingConstant :=
  mul_pos (density_positive 0) graphGaussianMass_pos

theorem gaussian_integral (a b : Velocities) :
    (∫ p,gaussianDensity a b p ∂law.prod volume)=leadingConstant*gaussianKernel a b := by
  unfold gaussianDensity leadingConstant
  rw [integral_const_mul,jointGaussian_factor]
  ring

theorem interior_limit (a b : Velocities) :
    Tendsto (fun t : ℝ => insidePartition a b t/|t|^189) (𝓝[≠] 0)
      (𝓝 (leadingConstant*gaussianKernel a b)) := by
  have h := scaledDensity_integral_tendsto a b
  rw [gaussian_integral] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (interior_scaled a b t ht).symm

theorem full_kernel_limit (a b : Velocities) :
    Tendsto (fun t : ℝ => kernel (1/t^2) (constantState a t) (constantState b t)/|t|^189)
      (𝓝[≠] 0) (𝓝 (leadingConstant*gaussianKernel a b)) := by
  have h := (interior_limit a b).add (outside_scaled_limit a b)
  simpa only [add_zero,← add_div,← kernel_split] using h

theorem leadingConstant_formula : leadingConstant=chartDensity 0^63*graphGaussianMass := by
  unfold leadingConstant
  rw [density_zero]

theorem gaussianKernel_zero : gaussianKernel 0 0=1 := by
  unfold gaussianKernel gaussianIntegrand rootEnergy
  simp [PeriodicRelativeGaugeGaussian.rotate_zero,sizeSq]

theorem vacuum_kernel_limit :
    Tendsto (fun t : ℝ => kernel (1/t^2) (1 : State) 1/|t|^189) (𝓝[≠] 0)
      (𝓝 leadingConstant) := by
  simpa only [constantState_zero,gaussianKernel_zero,mul_one] using full_kernel_limit 0 0

/-- An actual full-Haar vacuum-diagonal ratio, not principal-eigenvalue or
stationary-ground normalization, and not a constructed Markov kernel. -/
theorem vacuum_ratio_limit (a b : Velocities) :
    Tendsto (fun t : ℝ => kernel (1/t^2) (constantState a t) (constantState b t)/kernel (1/t^2) (1 : State) 1)
      (𝓝[≠] 0) (𝓝 (gaussianKernel a b)) := by
  have h := (full_kernel_limit a b).div vacuum_kernel_limit leadingConstant_pos.ne'
  have he : (leadingConstant*gaussianKernel a b)/leadingConstant=gaussianKernel a b := by
    field_simp [leadingConstant_pos.ne']
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact div_div_div_cancel_right₀ (pow_ne_zero 189 (abs_ne_zero.mpr ht)) _ _

theorem full_kernel_unscaled_tendsto_zero (a b : Velocities) :
    Tendsto (fun t : ℝ => kernel (1/t^2) (constantState a t) (constantState b t))
      (𝓝[≠] 0) (𝓝 0) := by
  have hz : Tendsto (fun t : ℝ => |t|^189) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => |t|^189) := continuous_abs.pow 189
    simpa only [abs_zero,zero_pow (by decide : 189≠0)] using hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ)≤𝓝 0)
  have h := (full_kernel_limit a b).mul hz
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact div_mul_cancel₀ _ (pow_ne_zero 189 (abs_ne_zero.mpr ht))

end OperatorDerivativeRewrite.Foundation.PeriodicFullHaarGaussianLimit
