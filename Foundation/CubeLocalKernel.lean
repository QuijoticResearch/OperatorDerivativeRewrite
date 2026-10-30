import Foundation.CubeRelativeChart

/-! Gaussian domination and exact local-coordinate representation of the actual Wilson kernel. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CubeLocalKernel
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open CubeTemporalSlab CubeWilsonSlab CubeAxialSlice CubeAxialGauge CubeChordTransfer
open CubeTemporalRootHaar CubeTemporalConfinement CubeTemporalExterior CubeRelativeChart
open FourCubePinnedCoercivity SU2HaarLaplaceUpper
open FourCubeHemisphereCoercivity (chartRate_smul local_defect_lower small_defect_chartRate)
open FourCubeHaarLaplaceDensity (chartDensity_le_zero)
attribute [local irreducible] defect weight axialState reduced assemble law relativeHaar gaugeHaar

def mass (Y : Field) : ℝ := ∑ v,(chartRate (Y v)-1)

theorem mass_smul (t : ℝ) (Y : Field) : mass (t • Y)=t^2*mass Y := by
  simp only [mass,Pi.smul_apply,chartRate_smul,Finset.mul_sum]

theorem local_energy_lower (Y : Field) (hY : chartField Y ∈ localField) :
    mass Y/4 ≤ relativeEnergy (chartField Y) := by
  have hh (v : RelativeIndex) : (chartRate (Y v)-1)/4 ≤ defect (hemisphereChart (Y v)) := by
    have hr := small_defect_chartRate (hemisphereChart (Y v)) (hY v (Set.mem_univ v))
    rw [coordinates_chart] at hr
    exact local_defect_lower _ hr
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hh v)
  simpa only [mass,relativeEnergy,chartField,Finset.sum_div] using hs

private theorem relative_assemble (c : SU2) (h : Relative) : relative (assemble c h)=h := by
  funext v
  simp [relative,assemble_root,assemble,anchored,v.property,mul_assoc]

/-- Actual nonlinear slab action, not the Hessian of a different completed cell. -/
theorem scaled_action_lower (t : ℝ) (ht : t ≠ 0) (q r : Chords) (c : SU2)
    (Y : Field) (hY : chartField (t • Y) ∈ localField) :
    mass Y/252 ≤ (1/t^2)*halfAction (axialState q) (axialState r)
      (assemble c (chartField (t • Y))) := by
  have he := local_energy_lower (t • Y) hY
  rw [mass_smul] at he
  have hb : 0 ≤ 1/t^2 := by positivity
  have hc : (1/t^2)*(t^2*mass Y/4)=mass Y/4 := by field_simp [ht]
  have hs := mul_le_mul_of_nonneg_left he hb
  rw [hc] at hs
  have hh := halfAction_lower q r (assemble c (chartField (t • Y)))
  rw [relative_assemble] at hh
  have hA := (spatial_action_bounds (axialState q)).1
  have hB := (spatial_action_bounds (axialState r)).1
  have hh' : relativeEnergy (chartField (t • Y))/63 ≤
      halfAction (axialState q) (axialState r) (assemble c (chartField (t • Y))) := by linarith
  have hs' := mul_le_mul_of_nonneg_left hh' hb
  nlinarith

def scaledCutoff (t : ℝ) : Set Field := {Y | chartField (t • Y) ∈ localField}

def scaledDensity (t : ℝ) (U V : State) (c : SU2) : Field → ℝ := by
  classical
  exact (scaledCutoff t).indicator (fun Y => density (t • Y)*
    weight (1/t^2) (axialState (reduced U)) (axialState (reduced V))
      (assemble c (chartField (t • Y))))

attribute [local irreducible] scaledDensity

theorem scaledCutoff_measurable (t : ℝ) : MeasurableSet (scaledCutoff t) :=
  localField_measurable.preimage (chartField_measurable.comp
    (continuous_const_smul t : Continuous (fun Y : Field => t • Y)).measurable)

theorem scaledDensity_joint_measurable (t : ℝ) (U V : State) :
    Measurable (fun p : SU2 × Field => scaledDensity t U V p.1 p.2) := by
  have hY : Measurable (fun p : SU2 × Field => t • p.2) := by fun_prop
  have ha := assemble_measurable.comp (measurable_fst.prodMk (chartField_measurable.comp hY))
  have hw : Measurable (fun p : SU2 × Field => weight (1/t^2)
      (axialState (reduced U)) (axialState (reduced V)) (assemble p.1 (chartField (t • p.2)))) :=
    (weight_joint_measurable (1/t^2)).comp
      ((measurable_const : Measurable (fun _ : SU2 × Field =>
        (axialState (reduced U),axialState (reduced V)))).prodMk ha)
  have hd := (CubeRelativeChart.density_measurable.comp hY).mul hw
  have hi := hd.indicator ((scaledCutoff_measurable t).preimage measurable_snd)
  convert hi using 1
  funext p
  classical
  by_cases h : p.2 ∈ scaledCutoff t <;> simp [scaledDensity,h]

theorem scaledDensity_measurable (t : ℝ) (U V : State) (c : SU2) :
    Measurable (scaledDensity t U V c) := by
  change Measurable ((fun p : SU2 × Field => scaledDensity t U V p.1 p.2) ∘
    (fun Y : Field => (c,Y)))
  exact (scaledDensity_joint_measurable t U V).comp
    ((measurable_const : Measurable (fun _ : Field => c)).prodMk measurable_id)

theorem scaledDensity_nonnegative (t : ℝ) (U V : State) (c : SU2) (Y : Field) :
    0 ≤ scaledDensity t U V c Y := by
  classical
  unfold scaledDensity
  apply Set.indicator_nonneg
  intro Y _
  apply mul_nonneg (density_nonneg _)
  unfold weight
  exact (Real.exp_pos _).le

theorem density_bound (Y : Field) : density Y ≤ (chartDensity 0)^7 := by
  have hh := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun v _ => FourCubeHaarProductCoordinates.chartDensity_nonneg (Y v))
    (fun v _ => chartDensity_le_zero (Y v))
  simpa only [density,Finset.prod_const,Finset.card_univ,relative_count] using hh

/-- Uniform in both original boundaries and in the free root. The cutoff is essential. -/
theorem scaledDensity_bound (t : ℝ) (ht : t ≠ 0) (U V : State) (c : SU2) (Y : Field) :
    scaledDensity t U V c Y ≤ (chartDensity 0)^7*Real.exp (-mass Y/252) := by
  classical
  unfold scaledDensity
  by_cases h : Y ∈ scaledCutoff t
  · rw [Set.indicator_of_mem h]
    have hw : weight (1/t^2) (axialState (reduced U)) (axialState (reduced V))
        (assemble c (chartField (t • Y))) ≤ Real.exp (-mass Y/252) := by
      unfold weight
      apply Real.exp_le_exp.mpr
      linarith [scaled_action_lower t ht (reduced U) (reduced V) c Y h]
    exact mul_le_mul (density_bound _) hw (by unfold weight; exact (Real.exp_pos _).le) (pow_nonneg (FourCubeHaarProductCoordinates.chartDensity_nonneg _) 7)
  · rw [Set.indicator_of_notMem h]
    exact mul_nonneg (pow_nonneg (FourCubeHaarProductCoordinates.chartDensity_nonneg _) 7) (Real.exp_pos _).le

theorem gaussian_integrable : Integrable (fun Y : Field => Real.exp (-mass Y/252)) := by
  have hi := SU2HaarLaplaceUpper.gaussian_integrable (1/63) (by norm_num)
  have he : (fun Y : Field => Real.exp (-mass Y/252))=
      (fun Y => ∏ v : RelativeIndex,Real.exp (-(1/63 : ℝ)*(chartRate (Y v)-1)/4)) := by
    funext Y
    rw [← Real.exp_sum]
    congr 1
    simp only [mass,← Finset.sum_div,← Finset.mul_sum]
    ring
  rw [he,volume_pi]
  exact Integrable.fintype_prod (fun _ : RelativeIndex => hi)

theorem scaledDensity_integrable (t : ℝ) (ht : t ≠ 0) (U V : State) (c : SU2) :
    Integrable (scaledDensity t U V c) := by
  apply (gaussian_integrable.const_mul ((chartDensity 0)^7)).mono'
    (scaledDensity_measurable t U V c).aestronglyMeasurable
  filter_upwards with Y
  rw [Real.norm_eq_abs,abs_of_nonneg (scaledDensity_nonnegative t U V c Y)]
  exact scaledDensity_bound t ht U V c Y

theorem scaledDensity_joint_integrable (t : ℝ) (ht : t ≠ 0) (U V : State) :
    Integrable (fun p : SU2 × Field => scaledDensity t U V p.1 p.2) (law.prod volume) := by
  apply ((gaussian_integrable.const_mul ((chartDensity 0)^7)).comp_snd law).mono'
    (scaledDensity_joint_measurable t U V).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (scaledDensity_nonnegative t U V p.1 p.2)]
  exact scaledDensity_bound t ht U V p.1 p.2


private theorem indicator_assemble (f : Gauge → ℝ) (c : SU2) (h : Relative) :
    localRegion.indicator f (assemble c h)=
      localField.indicator (fun h => f (assemble c h)) h := by
  classical
  have he : assemble c h ∈ localRegion ↔ h ∈ localField := by
    simpa only [localField,Set.mem_pi,Set.mem_univ,true_implies] using assemble_mem c h
  by_cases hh : h ∈ localField
  · rw [Set.indicator_of_mem hh,Set.indicator_of_mem (he.mpr hh)]
  · rw [Set.indicator_of_notMem hh,Set.indicator_of_notMem (fun hg => hh (he.mp hg))]

private theorem assembled_weight_measurable (beta : ℝ) (U V : State) :
    Measurable (fun p : SU2 × Relative => weight beta U V (assemble p.1 p.2)) :=
  (weight_joint_measurable beta).comp
    ((measurable_const : Measurable (fun _ : SU2 × Relative => (U,V))).prodMk assemble_measurable)

/-- Genuine root/relative Fubini identity for the actual local integral. -/
theorem interior_root_iterated (beta : ℝ) (U V : State) :
    interior beta U V=∫ c,∫ h in localField,
      weight beta (axialState (reduced U)) (axialState (reduced V)) (assemble c h)
        ∂relativeHaar ∂law := by
  have hm : Measurable (weight beta (axialState (reduced U)) (axialState (reduced V))) :=
    (weight_joint_measurable beta).comp
      ((measurable_const : Measurable (fun _ : Gauge =>
        (axialState (reduced U),axialState (reduced V)))).prodMk measurable_id)
  have hi := assemble_preserving.integrable_comp_of_integrable
    ((weight_integrable beta (axialState (reduced U)) (axialState (reduced V))).indicator localRegion_measurable)
  change Integrable (fun p : SU2 × Relative => localRegion.indicator
    (weight beta (axialState (reduced U)) (axialState (reduced V))) (assemble p.1 p.2))
      (law.prod relativeHaar) at hi
  rw [CubeTemporalExterior.interior,← integral_indicator localRegion_measurable,integral_split _ (hm.indicator localRegion_measurable)]
  rw [integral_prod _ hi]
  simp_rw [indicator_assemble,integral_indicator localField_measurable]

/-- The local actual kernel in the exact seven-link coordinate density. -/
theorem interior_root_chart (beta : ℝ) (U V : State) :
    interior beta U V=∫ c,∫ Y : Field,density Y*localField.indicator
      (fun h => weight beta (axialState (reduced U)) (axialState (reduced V)) (assemble c h))
      (chartField Y) ∂volume ∂law := by
  rw [interior_root_iterated]
  apply integral_congr_ae
  filter_upwards with c
  exact integral_local _ ((assembled_weight_measurable beta _ _).comp
    (measurable_const.prodMk measurable_id))

private theorem coordinate_rescale (t : ℝ) (ht : 0 < t) (U V : State) (c : SU2) :
    (∫ Y : Field,density Y*localField.indicator
      (fun h => weight (1/t^2) (axialState (reduced U)) (axialState (reduced V)) (assemble c h))
      (chartField Y))=t^21*(∫ Y : Field,scaledDensity t U V c Y) := by
  rw [CubeRelativeChart.integral_rescale _ t ht.ne',abs_of_pos ht]
  congr 1
  apply integral_congr_ae
  filter_upwards with Y
  classical
  by_cases h : chartField (t • Y) ∈ localField
  · have hh : Y ∈ scaledCutoff t := h
    simp only [scaledDensity,Set.indicator_of_mem h,Set.indicator_of_mem hh]
  · have hh : Y ∉ scaledCutoff t := h
    simp only [scaledDensity,Set.indicator_of_notMem h,Set.indicator_of_notMem hh,mul_zero]

/-- Exact t^21-scaled local kernel, retaining the complete free-root Haar average. -/
theorem interior_scaled (t : ℝ) (ht : 0 < t) (U V : State) :
    interior (1/t^2) U V/t^21=∫ c,∫ Y : Field,scaledDensity t U V c Y ∂volume ∂law := by
  apply (div_eq_iff (pow_ne_zero 21 ht.ne')).mpr
  rw [interior_root_chart]
  simp_rw [coordinate_rescale t ht U V]
  rw [integral_const_mul]
  ring

/-- The same identity as one genuinely integrable joint root/Euclidean integral. -/
theorem interior_scaled_joint (t : ℝ) (ht : 0 < t) (U V : State) :
    interior (1/t^2) U V/t^21=
      ∫ p : SU2 × Field,scaledDensity t U V p.1 p.2 ∂law.prod volume := by
  rw [interior_scaled t ht U V,integral_prod _ (scaledDensity_joint_integrable t ht.ne' U V)]


/-- Reduction to the remaining genuine local pointwise limit. The limit is a hypothesis,
not an identified Gaussian Hessian or a spectral conclusion. -/
theorem kernel_limit_of_local_limit (U V : ℝ → State) (L : SU2 × Field → ℝ)
    (hL : ∀ᵐ p ∂law.prod (volume : Measure Field),
      Tendsto (fun t : ℝ => scaledDensity t (U t) (V t) p.1 p.2)
        (𝓝[>] (0 : ℝ)) (𝓝 (L p))) :
    Tendsto (fun t : ℝ => kernel (1/t^2) (U t) (V t)/t^21)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p,L p ∂law.prod volume)) := by
  have hi : Tendsto (fun t : ℝ => ∫ p : SU2 × Field,
      scaledDensity t (U t) (V t) p.1 p.2 ∂law.prod volume)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p,L p ∂law.prod volume)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun p : SU2 × Field => (chartDensity 0)^7*Real.exp (-mass p.2/252))
    · exact Eventually.of_forall (fun t => (scaledDensity_joint_measurable t (U t) (V t)).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards with p
      rw [Real.norm_eq_abs,abs_of_nonneg (scaledDensity_nonnegative t (U t) (V t) p.1 p.2)]
      exact scaledDensity_bound t (ne_of_gt ht) (U t) (V t) p.1 p.2
    · exact (gaussian_integrable.const_mul ((chartDensity 0)^7)).comp_snd law
    · exact hL
  have hI : Tendsto (fun t : ℝ => CubeTemporalExterior.interior (1/t^2) (U t) (V t)/t^21)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p,L p ∂law.prod volume)) := by
    apply hi.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (interior_scaled_joint t ht (U t) (V t)).symm
  have hs := hI.add (scaled_exterior_tendsto_zero U V)
  simp only [add_zero] at hs
  convert hs using 1
  funext t
  rw [kernel_split,add_div]

end OperatorDerivativeRewrite.Foundation.CubeLocalKernel
