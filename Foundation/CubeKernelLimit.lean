import Foundation.CubeChartAction

/-! Actual boundary-chart kernel limit through the actual slab second variation.
The second variation is not yet identified with an explicit diagonalized form. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.CubeKernelLimit
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open CubeTemporalSlab CubeWilsonSlab CubeTemporalRootHaar CubeRelativeChart CubeChartAction
open CubeLocalKernel FourCubePinnedCoercivity
open SU2TraceHessianModel SU2MatrixExponentialBridge SU2ProductCurveHessian
attribute [local irreducible] law relativeHaar gaugeHaar CubeWilsonSlab.kernel

theorem density_continuous : Continuous CubeRelativeChart.density := by
  unfold CubeRelativeChart.density
  exact continuous_finset_prod _ (fun v _ =>
    FourCubeHaarLaplaceDensity.chartDensity_continuous.comp (continuous_apply v))

theorem density_zero : CubeRelativeChart.density (0 : CubeRelativeChart.Field)=(chartDensity 0)^7 := by
  simp only [CubeRelativeChart.density,Pi.zero_apply,Finset.prod_const,Finset.card_univ,relative_count]

theorem density_scaled_tendsto (Z : CubeRelativeChart.Field) :
    Tendsto (fun t : ℝ => CubeRelativeChart.density (t • Z)) (𝓝 0) (𝓝 ((chartDensity 0)^7)) := by
  have hc : Continuous (fun t : ℝ => CubeRelativeChart.density (t • Z)) :=
    density_continuous.comp (continuous_id.smul continuous_const)
  simpa only [zero_smul,density_zero] using hc.tendsto (0 : ℝ)

theorem eventually_scaledCutoff (Z : CubeRelativeChart.Field) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),Z ∈ scaledCutoff t := by
  have hh (v : RelativeIndex) : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      defect (hemisphereChart (t • Z v)) < 1/4 := by
    have hc : Continuous (fun t : ℝ => defect (hemisphereChart (t • Z v))) :=
      continuous_const.sub ((realTraceCLM.continuous.comp (curve_contDiff (Z v)).continuous).div_const 2)
    have hz : defect (hemisphereChart ((0 : ℝ) • Z v)) < 1/4 := by
      simp only [zero_smul,chart_zero,defect_one]
      norm_num
    exact (hc.tendsto (0 : ℝ)).eventually (eventually_lt_nhds hz)
  simpa only [scaledCutoff,Set.mem_setOf_eq,localField,Set.mem_pi,Set.mem_univ,true_implies,
    chartField,Pi.smul_apply,SU2HaarLaplaceUpper.localCut,Set.mem_setOf_eq] using eventually_all.mpr hh

def limitDensity (X Y : Boundary) (p : SU2 × CubeRelativeChart.Field) : ℝ :=
  (chartDensity 0)^7*Real.exp (-secondVariation X Y p.1 p.2/2)

private theorem scaledDensity_eq (t : ℝ) (X Y : Boundary) (c : SU2)
    (Z : CubeRelativeChart.Field) (hZ : Z ∈ scaledCutoff t) :
    scaledDensity t (boundaryRay X t) (boundaryRay Y t) c Z=
      CubeRelativeChart.density (t • Z)*Real.exp (-actionRay X Y c Z t/t^2) := by
  classical
  unfold scaledDensity
  rw [Set.indicator_of_mem hZ]
  simp only [boundaryRay,reduced_axial]
  unfold weight actionRay temporalRay boundaryRay
  congr 2
  ring

theorem scaledDensity_tendsto (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    Tendsto (fun t : ℝ => scaledDensity t (boundaryRay X t) (boundaryRay Y t) c Z)
      (𝓝[>] (0 : ℝ)) (𝓝 (limitDensity X Y (c,Z))) := by
  have hp := (density_scaled_tendsto Z).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have ha := (action_quotient_limit X Y c Z).mono_left
    (nhdsWithin_mono (0 : ℝ) (fun t ht => ne_of_gt ht))
  have he := (Real.continuous_exp.tendsto _).comp ha.neg
  have hh := hp.mul he
  unfold limitDensity
  simp only [neg_div] at *
  apply hh.congr'
  have hc := (eventually_scaledCutoff Z).filter_mono
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  filter_upwards [hc] with t ht
  simpa only [Function.comp_apply,neg_div] using (scaledDensity_eq t X Y c Z ht).symm

theorem limitDensity_nonnegative (X Y : Boundary) (p : SU2 × CubeRelativeChart.Field) :
    0 ≤ limitDensity X Y p := by
  unfold limitDensity
  exact mul_nonneg (pow_nonneg (FourCubeHaarProductCoordinates.chartDensity_nonneg _) 7) (Real.exp_pos _).le

theorem limitDensity_positive (X Y : Boundary) (p : SU2 × CubeRelativeChart.Field) :
    0 < limitDensity X Y p := by
  unfold limitDensity
  exact mul_pos (pow_pos (FourCubeHaarLaplaceDensity.chartDensity_positive _) 7) (Real.exp_pos _)

theorem limitDensity_aestronglyMeasurable (X Y : Boundary) :
    AEStronglyMeasurable (limitDensity X Y) (law.prod volume) := by
  exact aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ))
    (fun t => (scaledDensity_joint_measurable t (boundaryRay X t) (boundaryRay Y t)).aestronglyMeasurable)
    (ae_of_all _ (fun p => scaledDensity_tendsto X Y p.1 p.2))

theorem limitDensity_bound (X Y : Boundary) (p : SU2 × CubeRelativeChart.Field) :
    limitDensity X Y p ≤ (chartDensity 0)^7*Real.exp (-mass p.2/252) := by
  apply le_of_tendsto (scaledDensity_tendsto X Y p.1 p.2)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact scaledDensity_bound t (ne_of_gt ht) (boundaryRay X t) (boundaryRay Y t) p.1 p.2

theorem limitDensity_integrable (X Y : Boundary) :
    Integrable (limitDensity X Y) (law.prod volume) := by
  apply ((gaussian_integrable.const_mul ((chartDensity 0)^7)).comp_snd law).mono'
    (limitDensity_aestronglyMeasurable X Y)
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (limitDensity_nonnegative X Y p)]
  exact limitDensity_bound X Y p


/-- Actual second variation retains coercivity in all seven temporal coordinate triples. -/
theorem secondVariation_lower (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    mass Z/252 ≤ secondVariation X Y c Z/2 := by
  have ha : Tendsto (fun t : ℝ => actionRay X Y c Z t/t^2)
      (𝓝[>] (0 : ℝ)) (𝓝 (secondVariation X Y c Z/2)) :=
    (action_quotient_limit X Y c Z).mono_left
      (nhdsWithin_mono (0 : ℝ) (fun t ht => ne_of_gt ht))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ha
  have hc := (eventually_scaledCutoff Z).filter_mono
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  filter_upwards [self_mem_nhdsWithin,hc] with t ht htZ
  have h := scaled_action_lower t (ne_of_gt ht) (chords X t) (chords Y t) c Z htZ
  convert h using 1
  unfold actionRay boundaryRay temporalRay
  ring

/-- The actual limiting integral is finite and strictly positive for every fixed chart pair. -/
theorem limit_integral_positive (X Y : Boundary) :
    0 < ∫ p,limitDensity X Y p ∂law.prod volume := by
  rw [integral_pos_iff_support_of_nonneg (fun p => limitDensity_nonnegative X Y p)
    (limitDensity_integrable X Y)]
  have hs : Function.support (limitDensity X Y)=Set.univ := by
    ext p
    simp only [Function.mem_support,Set.mem_univ,iff_true]
    exact (limitDensity_positive X Y p).ne'
  rw [hs]
  rw [← Set.univ_prod_univ,Measure.prod_prod]
  simp only [measure_univ,one_mul]
  exact Measure.measure_univ_pos.mpr (NeZero.ne (volume : Measure CubeRelativeChart.Field))

/-- Unconditional fixed-boundary-chart asymptotics for the ACTUAL integrated kernel. -/
theorem kernel_tendsto (X Y : Boundary) :
    Tendsto (fun t : ℝ => kernel (1/t^2) (boundaryRay X t) (boundaryRay Y t)/t^21)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p,limitDensity X Y p ∂law.prod volume)) :=
  kernel_limit_of_local_limit _ _ _ (ae_of_all _ (fun p => scaledDensity_tendsto X Y p.1 p.2))

end OperatorDerivativeRewrite.Foundation.CubeKernelLimit
