import Foundation.PeriodicRootedHaarControl
/-! Actual63-relative-variable Haar asymptotics at the FIXED identity root,
for arbitrary nonconstant real-color boundary velocities around commuting
constant SU(2) backgrounds. Hemisphere jets, exact chart transport/Jacobian,
prelimit Gaussian domination and exterior suppression prove the189-power limit
and same-background diagonal ratio. The full64-variable kernel, compact-root
integration and native stationary normalization remain separate obligations. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicAnchoredHaarLimit
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart SU2HemisphereJets SU2RootAdjoint
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicGaugeSaturatedGround PeriodicRelativeGaugeGaussian
open PeriodicFlatBackgroundHessian PeriodicTemporalQuadratic PeriodicAnchoredCovariantGaussian
open PeriodicRootedHaarControl
open PeriodicRelativeGaugeTails (smallGauge smallGauge_measurable gaugeRay_eventually_small)
open PeriodicFullHaarGaussianLimit (chart density localField localField_measurable)

def base (h : Fin 3 → SU2) : State := fun e => h e.2

private def edgeVectors (h : Fin 3 → SU2) (X Y : Velocity) (Z : Field)
    (e : SpatialEdge) : Fin 4 → Triple :=
  ![X e,rotate (h e.2) (velocity Z (shift e.1 e.2)),Y e,velocity Z e.1]
private def faceVectors (h : Fin 3 → SU2) (X : Velocity) (p : SpatialFace) : Fin 4 → Triple :=
  ![X (p.val.1,p.val.2.1),rotate (h p.val.2.1) (X (shift p.val.1 p.val.2.1,p.val.2.2)),
    rotate (h p.val.2.2) (X (shift p.val.1 p.val.2.2,p.val.2.1)),X (p.val.1,p.val.2.2)]

theorem temporal_word_chart (h : Fin 3 → SU2) (X Y : Velocity) (Z : Field) (t : ℝ) (e : SpatialEdge) :
    temporalWord (chartState (base h) X t) (chartState (base h) Y t) (gaugeRay Z 1 t) e=
      hemisphereChart (t • X e)*hemisphereChart (t • rotate (h e.2) (velocity Z (shift e.1 e.2)))*
        (hemisphereChart (t • Y e))⁻¹*(hemisphereChart (t • velocity Z e.1))⁻¹ := by
  unfold temporalWord chartState base
  rw [gaugeRay_apply,gaugeRay_apply]
  simp only [mul_one]
  rw [← rotate_smul,← PeriodicConstantRootLimit.chart_conjugates]
  group

theorem spatial_word_chart (h : Fin 3 → SU2) (X : Velocity) (t : ℝ) (p : SpatialFace)
    (hc : h p.val.2.1*h p.val.2.2=h p.val.2.2*h p.val.2.1) :
    spatialWord (chartState (base h) X t) p=
      hemisphereChart (t • X (p.val.1,p.val.2.1))*
        hemisphereChart (t • rotate (h p.val.2.1) (X (shift p.val.1 p.val.2.1,p.val.2.2)))*
        (hemisphereChart (t • rotate (h p.val.2.2) (X (shift p.val.1 p.val.2.2,p.val.2.1))))⁻¹*
        (hemisphereChart (t • X (p.val.1,p.val.2.2)))⁻¹ := by
  unfold spatialWord chartState base
  rw [flat_word _ _ _ _ _ _ hc,PeriodicConstantRootLimit.chart_conjugates,
    PeriodicConstantRootLimit.chart_conjugates,rotate_smul,rotate_smul]

private theorem temporal_term_chart (h : Fin 3 → SU2) (X Y : Velocity) (Z : Field)
    (t : ℝ) (e : SpatialEdge) :
    1-halfTrace (temporalWord (chartState (base h) X t) (chartState (base h) Y t) (gaugeRay Z 1 t) e)=
      wordRay (edgeVectors h X Y Z e) t := by
  rw [temporal_word_chart]
  rfl
private theorem spatial_term_chart (h : Fin 3 → SU2) (X : Velocity) (t : ℝ) (p : SpatialFace)
    (hc : ∀ i j,h i*h j=h j*h i) :
    1-halfTrace (spatialWord (chartState (base h) X t) p)=wordRay (faceVectors h X p) t := by
  rw [spatial_word_chart h X t p (hc _ _)]
  rfl

theorem temporal_chart_limit (h : Fin 3 → SU2) (X Y : Velocity) (Z : Field) :
    Tendsto (fun t : ℝ => temporalAction (chartState (base h) X t) (chartState (base h) Y t)
      (gaugeRay Z 1 t)/t^2) (𝓝[≠] 0) (𝓝 (temporalEnergy h X Y (velocity Z)/2)) := by
  have hh := tendsto_finsetSum Finset.univ (fun e (_ : e∈(Finset.univ : Finset SpatialEdge)) =>
    word_quadratic_limit (edgeVectors h X Y Z e))
  have he (e : SpatialEdge) : edgeVectors h X Y Z e 0+edgeVectors h X Y Z e 1-
      edgeVectors h X Y Z e 2-edgeVectors h X Y Z e 3=
      X e-Y e-gaugeGradient h (velocity Z) e := by
    ext i
    simp [edgeVectors,gaugeGradient]
    ring
  change Tendsto _ _ (𝓝 (∑ e : SpatialEdge,sizeSq (edgeVectors h X Y Z e 0+edgeVectors h X Y Z e 1-
    edgeVectors h X Y Z e 2-edgeVectors h X Y Z e 3)/2)) at hh
  simp_rw [he] at hh
  have hf : (fun t : ℝ => temporalAction (chartState (base h) X t) (chartState (base h) Y t)
      (gaugeRay Z 1 t)/t^2)=(fun t => ∑ e : SpatialEdge,wordRay (edgeVectors h X Y Z e) t/t^2) := by
    funext t
    unfold temporalAction
    simp_rw [temporal_term_chart]
    exact Finset.sum_div _ _ _
  rw [hf]
  simpa only [temporalEnergy,Finset.sum_div] using hh

theorem spatial_chart_limit (h : Fin 3 → SU2) (X : Velocity) (hc : ∀ i j,h i*h j=h j*h i) :
    Tendsto (fun t : ℝ => spatialAction (chartState (base h) X t)/t^2) (𝓝[≠] 0) (𝓝 (quadratic h X/2)) := by
  have hh := tendsto_finsetSum Finset.univ (fun p (_ : p∈(Finset.univ : Finset SpatialFace)) =>
    word_quadratic_limit (faceVectors h X p))
  have hf : (fun t : ℝ => spatialAction (chartState (base h) X t)/t^2)=
      (fun t => ∑ p : SpatialFace,wordRay (faceVectors h X p) t/t^2) := by
    funext t
    unfold spatialAction
    simp_rw [spatial_term_chart h X t _ hc]
    exact Finset.sum_div _ _ _
  rw [hf]
  have he (p : SpatialFace) : faceVectors h X p 0+faceVectors h X p 1-
      faceVectors h X p 2-faceVectors h X p 3=covariantCurl h X p.val.1 p.val.2.1 p.val.2.2 := rfl
  change Tendsto _ _ (𝓝 (∑ p : SpatialFace,sizeSq (faceVectors h X p 0+faceVectors h X p 1-
    faceVectors h X p 2-faceVectors h X p 3)/2)) at hh
  simp_rw [he] at hh
  simpa only [quadratic,Finset.sum_div] using hh

theorem half_chart_limit (h : Fin 3 → SU2) (X Y : Velocity) (Z : Field)
    (hc : ∀ i j,h i*h j=h j*h i) :
    Tendsto (fun t : ℝ => halfAction (chartState (base h) X t) (chartState (base h) Y t)
      (gaugeRay Z 1 t)/t^2) (𝓝[≠] 0)
      (𝓝 ((quadratic h X/2+temporalEnergy h X Y (velocity Z)+quadratic h Y/2)/2)) := by
  have hh := (((spatial_chart_limit h X hc).div_const 2).add (temporal_chart_limit h X Y Z)).add
    ((spatial_chart_limit h Y hc).div_const 2)
  convert hh using 1
  · funext t
    unfold halfAction
    ring
  · ring

theorem weight_chart_limit (h : Fin 3 → SU2) (X Y : Velocity) (Z : Field)
    (hc : ∀ i j,h i*h j=h j*h i) :
    Tendsto (fun t : ℝ => PeriodicWilsonSlab.weight (1/t^2) (chartState (base h) X t)
      (chartState (base h) Y t) (gaugeRay Z 1 t)) (𝓝[≠] 0) (𝓝 (normalWeight h X Y Z)) := by
  change Tendsto _ _ (𝓝 (Real.exp (-((quadratic h X/2+
    temporalEnergy h X Y (velocity Z)+quadratic h Y/2)/2))))
  have hh := (Real.continuous_exp.tendsto (-((quadratic h X/2+
      temporalEnergy h X Y (velocity Z)+quadratic h Y/2)/2))).comp (half_chart_limit h X Y Z hc).neg
  convert hh using 1
  funext t
  unfold PeriodicWilsonSlab.weight
  congr 1
  ring

attribute [local irreducible] PeriodicWilsonSlab.weight chartState gaugeRay assemble

private theorem section_measurable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (f : A × B → C) (hf : Measurable f) (a : A) :
    Measurable (fun b => f (a,b)) := hf.comp (measurable_const.prodMk measurable_id)

def cutoff (H : State) (X Y : Velocity) (t : ℝ) (Z : Field) : ℝ :=
  smallGauge.indicator (PeriodicWilsonSlab.weight (1/t^2) (chartState H X t) (chartState H Y t)) (gaugeRay Z 1 t)

theorem cutoff_bound (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (Z : Field) :
    |cutoff H X Y t Z|≤Real.exp (budget X Y)*Real.exp (-PeriodicRootedHaarControl.envelopeRate*fieldSizeSq Z) := by
  unfold cutoff
  by_cases hg : gaugeRay Z 1 t∈smallGauge
  · rw [Set.indicator_of_mem hg,abs_of_pos (by unfold PeriodicWilsonSlab.weight; exact Real.exp_pos _)]
    exact PeriodicRootedHaarControl.inside_weight_bound H X Y Z t ht hg
  · rw [Set.indicator_of_notMem hg,abs_zero]
    positivity

theorem cutoff_limit (h : Fin 3 → SU2) (X Y : Velocity) (Z : Field)
    (hc : ∀ i j,h i*h j=h j*h i) :
    Tendsto (fun t : ℝ => cutoff (base h) X Y t Z) (𝓝[≠] 0) (𝓝 (normalWeight h X Y Z)) := by
  apply (weight_chart_limit h X Y Z hc).congr'
  filter_upwards [(gaugeRay_eventually_small Z 1).filter_mono nhdsWithin_le_nhds] with t ht
  exact (Set.indicator_of_mem ht _).symm

def scaledDensity (H : State) (X Y : Velocity) (t : ℝ) (Z : Field) : ℝ :=
  density (t • Z)*cutoff H X Y t Z

def majorant (X Y : Velocity) (Z : Field) : ℝ :=
  density 0*(Real.exp (budget X Y)*Real.exp (-PeriodicRootedHaarControl.envelopeRate*fieldSizeSq Z))

theorem weight_measurable (β : ℝ) (U V : State) : Measurable (PeriodicWilsonSlab.weight β U V) :=
  PeriodicFullHaarGaussianLimit.weight_measurable β U V

theorem scaledDensity_measurable (H : State) (X Y : Velocity) (t : ℝ) : Measurable (scaledDensity H X Y t) := by
  have hg : Measurable (fun Z : Field => gaugeRay Z 1 t) :=
    section_measurable (fun p : SU2 × Field => gaugeRay p.2 p.1 t)
      (PeriodicFullHaarGaussianLimit.gaugeRay_measurable t) 1
  have hc := ((weight_measurable (1/t^2) (chartState H X t) (chartState H Y t)).indicator
    smallGauge_measurable).comp hg
  exact ((PeriodicFullHaarGaussianLimit.density_measurable.comp (measurable_id.const_smul t))).mul hc

theorem scaledDensity_bound (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (Z : Field) :
    ‖scaledDensity H X Y t Z‖≤majorant X Y Z := by
  unfold scaledDensity majorant
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (PeriodicFullHaarGaussianLimit.density_nonneg _)]
  exact mul_le_mul (PeriodicFullHaarGaussianLimit.density_le_zero _) (cutoff_bound H X Y t ht Z)
    (abs_nonneg _) (PeriodicFullHaarGaussianLimit.density_nonneg _)

theorem majorant_integrable (X Y : Velocity) : Integrable (majorant X Y) :=
  ((fieldGaussian_integrable PeriodicRootedHaarControl.envelopeRate
    PeriodicRootedHaarControl.envelopeRate_pos).const_mul (Real.exp (budget X Y))).const_mul (density 0)

theorem scaledDensity_limit (h : Fin 3 → SU2) (X Y : Velocity) (Z : Field)
    (hc : ∀ i j,h i*h j=h j*h i) :
    Tendsto (fun t : ℝ => scaledDensity (base h) X Y t Z) (𝓝[≠] 0)
      (𝓝 (density 0*normalWeight h X Y Z)) := by
  have hz : Tendsto (fun t : ℝ => t • Z) (𝓝[≠] 0) (𝓝 (0 : Field)) := by
    have he : Continuous (fun t : ℝ => t • Z) := continuous_id.smul continuous_const
    simpa only [zero_smul] using he.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ)≤𝓝 0)
  exact ((PeriodicFullHaarGaussianLimit.density_continuous.tendsto 0).comp hz).mul (cutoff_limit h X Y Z hc)

theorem scaledDensity_integral_limit (h : Fin 3 → SU2) (X Y : Velocity)
    (hc : ∀ i j,h i*h j=h j*h i) :
    Tendsto (fun t : ℝ => ∫ Z : Field,scaledDensity (base h) X Y t Z) (𝓝[≠] 0)
      (𝓝 (density 0*∫ Z : Field,normalWeight h X Y Z)) := by
  have hlim : Tendsto (fun t : ℝ => ∫ Z : Field,scaledDensity (base h) X Y t Z) (𝓝[≠] 0)
      (𝓝 (∫ Z : Field,density 0*normalWeight h X Y Z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (majorant X Y)
    · exact Filter.Eventually.of_forall (fun t => (scaledDensity_measurable (base h) X Y t).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact ae_of_all _ (scaledDensity_bound (base h) X Y t ht)
    · exact majorant_integrable X Y
    · exact ae_of_all _ (fun Z => scaledDensity_limit h X Y Z hc)
  simpa only [integral_const_mul] using hlim

def integrand (H : State) (X Y : Velocity) (t : ℝ) (r : RelField) : ℝ :=
  PeriodicWilsonSlab.weight (1/t^2) (chartState H X t) (chartState H Y t) (assemble 1 r)
def block (H : State) (X Y : Velocity) (t : ℝ) : ℝ := ∫ r,integrand H X Y t r ∂relFieldHaar
def interior (H : State) (X Y : Velocity) (t : ℝ) : ℝ := ∫ r in localField,integrand H X Y t r ∂relFieldHaar
def exterior (H : State) (X Y : Velocity) (t : ℝ) : ℝ := ∫ r in localFieldᶜ,integrand H X Y t r ∂relFieldHaar

theorem integrand_measurable (H : State) (X Y : Velocity) (t : ℝ) : Measurable (integrand H X Y t) := by
  have ha : Measurable (fun r : RelField => assemble 1 r) :=
    section_measurable (fun p : SU2 × RelField => assemble p.1 p.2) assemble_measurable 1
  exact (weight_measurable (1/t^2) (chartState H X t) (chartState H Y t)).comp ha

theorem integrand_integrable (H : State) (X Y : Velocity) (t : ℝ) :
    Integrable (integrand H X Y t) relFieldHaar := by
  apply Integrable.of_bound (integrand_measurable H X Y t).aestronglyMeasurable (Real.exp (768*|1/t^2|))
  filter_upwards [] with r
  rw [Real.norm_eq_abs,abs_of_pos (by unfold integrand PeriodicWilsonSlab.weight; exact Real.exp_pos _)]
  exact (weight_bounds _ _ _ _).2

theorem block_split (H : State) (X Y : Velocity) (t : ℝ) :
    block H X Y t=interior H X Y t+exterior H X Y t :=
  (integral_add_compl localField_measurable (integrand_integrable H X Y t)).symm

theorem block_pos (H : State) (X Y : Velocity) (t : ℝ) : 0<block H X Y t := by
  have hi := integrand_integrable H X Y t
  unfold block integrand PeriodicWilsonSlab.weight at hi ⊢
  exact integral_exp_pos hi

theorem interior_scaling (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) :
    interior H X Y t/|t|^189=∫ Z : Field,scaledDensity H X Y t Z := by
  have hs : interior H X Y t=|t|^189*(∫ Z : Field,scaledDensity H X Y t Z) := by
    rw [interior,PeriodicFullHaarGaussianLimit.integral_local _ (integrand_measurable H X Y t),
      PeriodicFullHaarGaussianLimit.integral_rescale _ t ht]
    apply congrArg (fun a : ℝ => |t|^189*a)
    apply integral_congr_ae
    filter_upwards [] with Z
    unfold scaledDensity cutoff integrand
    rw [← PeriodicFullHaarGaussianLimit.indicator_assemble
      (PeriodicWilsonSlab.weight (1/t^2) (chartState H X t) (chartState H Y t)) 1 (chart (t • Z))]
    unfold gaugeRay PeriodicRelativeGaugeGaussian.chartField PeriodicFullHaarGaussianLimit.chart
    rfl
  apply (div_eq_iff (pow_ne_zero 189 (abs_ne_zero.mpr ht))).mpr
  rw [hs]
  ring

theorem interior_scaled_limit (h : Fin 3 → SU2) (X Y : Velocity)
    (hc : ∀ i j,h i*h j=h j*h i) :
    Tendsto (fun t : ℝ => interior (base h) X Y t/|t|^189) (𝓝[≠] 0)
      (𝓝 (density 0*∫ Z : Field,normalWeight h X Y Z)) := by
  apply (scaledDensity_integral_limit h X Y hc).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (interior_scaling (base h) X Y t ht).symm

theorem exterior_nonneg (H : State) (X Y : Velocity) (t : ℝ) : 0≤exterior H X Y t := by
  unfold exterior
  apply integral_nonneg
  intro r
  unfold integrand PeriodicWilsonSlab.weight
  exact (Real.exp_pos _).le

theorem exterior_bound (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) :
    exterior H X Y t≤Real.exp (budget X Y)*Real.exp (-PeriodicRootedHaarControl.exteriorRate/t^2) := by
  let C := Real.exp (budget X Y)*Real.exp (-PeriodicRootedHaarControl.exteriorRate/t^2)
  have hh := norm_setIntegral_le_of_norm_le_const (μ := relFieldHaar) (s := localFieldᶜ)
    (f := integrand H X Y t) (measure_lt_top _ _) (fun r hr => by
      rw [Real.norm_eq_abs,abs_of_pos (by unfold integrand PeriodicWilsonSlab.weight; exact Real.exp_pos _)]
      exact PeriodicRootedHaarControl.outside_weight_bound H X Y t ht (assemble 1 r) (assemble_root 1 r)
        (fun hg => hr ((PeriodicFullHaarGaussianLimit.small_assemble 1 r).mp hg)))
  have hm : relFieldHaar.real localFieldᶜ≤1 := measureReal_le_one
  have hc : 0≤C := by unfold C; positivity
  have hi := mul_le_mul_of_nonneg_left hm hc
  simp only [mul_one] at hi
  exact (le_abs_self _).trans (hh.trans hi)

theorem exterior_scaled_limit (H : State) (X Y : Velocity) :
    Tendsto (fun t : ℝ => exterior H X Y t/|t|^189) (𝓝[≠] 0) (𝓝 0) := by
  have hh := PeriodicRelativeGaugeTails.exponential_scale_limit.const_mul (Real.exp (budget X Y))
  simp only [mul_zero] at hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t =>
    div_nonneg (exterior_nonneg H X Y t) (by positivity))) ?_ hh
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hb := exterior_bound H X Y t ht
  have hr : PeriodicRelativeGaugeTails.exteriorRate≤PeriodicRootedHaarControl.exteriorRate := by
    norm_num [PeriodicRelativeGaugeTails.exteriorRate,PeriodicRootedHaarControl.exteriorRate]
  have he : Real.exp (-PeriodicRootedHaarControl.exteriorRate/t^2)≤
      Real.exp (-PeriodicRelativeGaugeTails.exteriorRate/t^2) := by
    apply Real.exp_le_exp.mpr
    have hd := div_le_div_of_nonneg_right hr (sq_nonneg t)
    simpa only [neg_div] using neg_le_neg hd
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (budget X Y)).le
  have hd := div_le_div_of_nonneg_right (hb.trans hm) (by positivity : (0 : ℝ)≤|t|^189)
  simpa only [mul_div_assoc] using hd

/-- Actual fixed-identity-root63-variable Haar block; NOT the full64-variable kernel. -/
theorem block_scaled_limit (h : Fin 3 → SU2) (X Y : Velocity)
    (hc : ∀ i j,h i*h j=h j*h i) :
    Tendsto (fun t : ℝ => block (base h) X Y t/|t|^189) (𝓝[≠] 0)
      (𝓝 (density 0*∫ Z : Field,normalWeight h X Y Z)) := by
  have hh := (interior_scaled_limit h X Y hc).add (exterior_scaled_limit (base h) X Y)
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [] with t
  rw [← add_div,← block_split]

theorem coefficient_pos (h : Fin 3 → SU2) (X Y : Velocity) :
    0<density 0*∫ Z : Field,normalWeight h X Y Z :=
  mul_pos (PeriodicFullHaarGaussianLimit.density_positive _) (normal_integral_pos h X Y)

/-- Same-background fixed-root vacuum ratio, not stationary normalization or the full kernel. -/
theorem block_ratio_limit (h : Fin 3 → SU2) (X Y : Velocity)
    (hc : ∀ i j,h i*h j=h j*h i) :
    Tendsto (fun t : ℝ => block (base h) X Y t/block (base h) 0 0 t) (𝓝[≠] 0)
      (𝓝 ((∫ Z : Field,normalWeight h X Y Z)/(∫ Z : Field,normalWeight h 0 0 Z))) := by
  have hh := (block_scaled_limit h X Y hc).div (block_scaled_limit h 0 0 hc) (coefficient_pos h 0 0).ne'
  have hd := (PeriodicFullHaarGaussianLimit.density_positive (0 : Field)).ne'
  have hn := (normal_integral_pos h 0 0).ne'
  have he : (density 0*(∫ Z : Field,normalWeight h X Y Z))/(density 0*(∫ Z : Field,normalWeight h 0 0 Z))=
      (∫ Z : Field,normalWeight h X Y Z)/(∫ Z : Field,normalWeight h 0 0 Z) := by
    field_simp [hd,hn]
  rw [he] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact div_div_div_cancel_right₀ (pow_ne_zero 189 (abs_ne_zero.mpr ht)) _ _

end OperatorDerivativeRewrite.Foundation.PeriodicAnchoredHaarLimit
