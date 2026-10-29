import Foundation.FourCubeMovingActionLimit

/-! Actual full-Haar Laplace limits for fixed moving-boundary amplitudes. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeMovingLaplaceLimit
open QuaternionSU2Representation FourCubePinnedHaar FourCubeHemisphereCoercivity
open FourCubeHaarProductCoordinates FourCubeHaarLaplaceDensity FourCubeHaarPartitionAsymptotic
open FourCubeScaledBoundaryControl FourCubeMovingActionLimit
open FourCubeBoundaryGibbsComparison FourCubeMovingBoundaryConcentration

def limitingDensity (x y z : ℝ) (Y : Field) : ℝ :=
  productDensity 0*Real.exp (-jointQuadratic Y x y z/2)

theorem boundaryScaledDensity_tendsto (x y z : ℝ) (Y : Field) :
    Tendsto (fun t : ℝ => boundaryScaledDensity t x y z Y) (𝓝[≠] 0) (𝓝 (limitingDensity x y z Y)) := by
  have hp : Tendsto (fun t : ℝ => productDensity (t • Y)) (𝓝[≠] 0) (𝓝 (productDensity 0)) := by
    have hs : Continuous (fun t : ℝ => t • Y) := continuous_id.smul continuous_const
    have hh := (productDensity_continuous.comp hs).tendsto (0 : ℝ)
    simpa only [zero_smul,Function.comp_def,Pi.smul_apply,id_eq] using hh.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hh := hp.mul (moving_boltzmann_limit Y x y z)
  apply hh.congr'
  filter_upwards [(eventually_scaledCutoff Y).filter_mono nhdsWithin_le_nhds] with t ht
  change _=(scaledCutoff t).indicator (fun Z => productDensity (t • Z)*
    Real.exp (-movingRay Z x y z t/t^2)) Y
  rw [Set.indicator_of_mem ht]

theorem limitingDensity_bound (x y z : ℝ) (Y : Field) :
    limitingDensity x y z Y ≤ (productDensity 0*Real.exp (216*(x^2+y^2+z^2)))*
      Real.exp (-quadraticMass Y/1116) := by
  apply le_of_tendsto (boundaryScaledDensity_tendsto x y z Y)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact boundaryScaledDensity_bound t ht x y z _ le_rfl Y

theorem limitingDensity_measurable (x y z : ℝ) : Measurable (limitingDensity x y z) := by
  unfold limitingDensity jointQuadratic FourCubeHaarQuadraticLimit.quadraticForm
    FourCubeMovingBoundaryQuadratic.ribbonQuadratic FourCubeMovingBoundaryQuadratic.ribbonVectors
    SU2MatrixExponentialBridge.lengthSq Matrix.mulVec dotProduct
    FourCubePinnedSecondVariation.liftVelocity OneSidedPinnedInterior.lift SU2HemisphereJets.frame
  fun_prop

theorem limitingDensity_integrable (x y z : ℝ) : Integrable (limitingDensity x y z) := by
  apply (broadened_gaussian_integrable.const_mul
    (productDensity 0*Real.exp (216*(x^2+y^2+z^2)))).mono'
      (limitingDensity_measurable x y z).aestronglyMeasurable
  filter_upwards with Y
  have hp : 0 < limitingDensity x y z Y := mul_pos (productDensity_positive 0) (Real.exp_pos _)
  rw [Real.norm_eq_abs,abs_of_pos hp]
  exact limitingDensity_bound x y z Y

theorem limitingDensity_integral_positive (x y z : ℝ) :
    0 < ∫ Y : Field,limitingDensity x y z Y := by
  have hi : Integrable (fun Y : Field => Real.exp (-jointQuadratic Y x y z/2)) := by
    have hh := (limitingDensity_integrable x y z).const_mul ((productDensity 0)⁻¹)
    convert! hh using 1
    funext Y
    simp [limitingDensity,← mul_assoc,(productDensity_positive 0).ne']
  unfold limitingDensity
  rw [integral_const_mul]
  exact mul_pos (productDensity_positive 0) (integral_exp_pos hi)

theorem boundaryScaledDensity_integral_tendsto (x y z : ℝ) :
    Tendsto (fun t : ℝ => ∫ Y : Field,boundaryScaledDensity t x y z Y) (𝓝[≠] 0)
      (𝓝 (∫ Y : Field,limitingDensity x y z Y)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun Y : Field => (productDensity 0*Real.exp (216*(x^2+y^2+z^2)))*
      Real.exp (-quadraticMass Y/1116))
  · exact Filter.Eventually.of_forall (fun t => (boundaryScaledDensity_measurable t x y z).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards with Y
    rw [Real.norm_eq_abs,abs_of_nonneg (boundaryScaledDensity_nonneg t x y z Y)]
    exact boundaryScaledDensity_bound t ht x y z _ le_rfl Y
  · exact broadened_gaussian_integrable.const_mul _
  · exact ae_of_all _ (boundaryScaledDensity_tendsto x y z)

theorem movingLocalPartition_asymptotic (x y z : ℝ) :
    Tendsto (fun t : ℝ => movingLocalPartition t x y z/|t|^93) (𝓝[≠] 0)
      (𝓝 (∫ Y : Field,limitingDensity x y z Y)) := by
  apply (boundaryScaledDensity_integral_tendsto x y z).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [movingLocalPartition_rescale t ht x y z]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero _ (abs_ne_zero.mpr ht))).symm

theorem moving_cutoff_probability (t x y z : ℝ) :
    (law (1/t^2) (movingBoundary t x y z)).real localStateDomain=
      movingLocalPartition t x y z/pinnedPartition (1/t^2) (movingBoundary t x y z) := by
  classical
  have hh := law_integral (1/t^2) (movingBoundary t x y z) (localStateDomain.indicator (1 : PinnedState → ℝ))
  have hi := integral_indicator_one (μ := law (1/t^2) (movingBoundary t x y z)) localStateDomain_measurable
  rw [hi] at hh
  rw [hh]
  congr 1
  rw [movingLocalPartition,← integral_indicator localStateDomain_measurable]
  apply integral_congr_ae
  filter_upwards with U
  by_cases h : U∈localStateDomain
  · simp only [Set.indicator_of_mem h,Pi.one_apply,one_mul]
    congr 1
    ring
  · simp only [Set.indicator_of_notMem h,zero_mul]

theorem moving_cutoff_probability_tendsto_one (x y z : ℝ) :
    Tendsto (fun t : ℝ => (law (1/t^2) (movingBoundary t x y z)).real localStateDomain)
      (𝓝[≠] 0) (𝓝 1) := by
  have hp := moving_outside_tendsto_zero (x^2+y^2+z^2) (fun _ => x) (fun _ => y) (fun _ => z) (fun _ => le_rfl)
  have he (t : ℝ) : (law (1/t^2) (movingBoundary t x y z)).real localStateDomain=
      1-(law (1/t^2) (movingBoundary t x y z)).real localStateDomainᶜ := by
    have hh := measureReal_compl (μ := law (1/t^2) (movingBoundary t x y z)) localStateDomain_measurable
    have h1 : (law (1/t^2) (movingBoundary t x y z)).real Set.univ=1 := by simp
    rw [h1] at hh
    linarith
  simp_rw [he]
  simpa only [sub_zero] using tendsto_const_nhds.sub hp

theorem moving_fullPartition_asymptotic (x y z : ℝ) :
    Tendsto (fun t : ℝ => pinnedPartition (1/t^2) (movingBoundary t x y z)/|t|^93) (𝓝[≠] 0)
      (𝓝 (∫ Y : Field,limitingDensity x y z Y)) := by
  have hp := moving_cutoff_probability_tendsto_one x y z
  have hh := (movingLocalPartition_asymptotic x y z).div hp (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin,hp.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with t ht hprob
  have hz := (pinnedPartition_positive (1/t^2) (movingBoundary t x y z)).ne'
  have hc := moving_cutoff_probability t x y z
  have hl : movingLocalPartition t x y z ≠ 0 := by
    intro he
    rw [he,zero_div] at hc
    exact hprob hc
  simp only [Pi.div_apply]
  rw [hc]
  field_simp [hl,hz,abs_ne_zero.mpr ht]

theorem moving_partition_ratio_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => normalizedPartition (1/t^2) (movingBoundary t x y z)) (𝓝[≠] 0)
      (𝓝 ((∫ Y : Field,limitingDensity x y z Y)/(∫ Y : Field,gaussianDensity Y))) := by
  have hh := (moving_fullPartition_asymptotic x y z).div actual_normalizer_asymptotic
    gaussianDensity_integral_positive.ne'
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change (pinnedPartition (1/t^2) (movingBoundary t x y z)/|t|^93)/
    (FourCubePinnedConcentration.normalizer (1/t^2)/|t|^93)=_
  unfold normalizedPartition
  field_simp [(FourCubePinnedConcentration.normalizer_positive (1/t^2)).ne',abs_ne_zero.mpr ht]

theorem moving_freeEnergy_difference_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => -Real.log (normalizedPartition (1/t^2) (movingBoundary t x y z)))
      (𝓝[≠] 0)
      (𝓝 (-Real.log ((∫ Y : Field,limitingDensity x y z Y)/(∫ Y : Field,gaussianDensity Y)))) := by
  have hp := div_pos (limitingDensity_integral_positive x y z) gaussianDensity_integral_positive
  exact ((Real.continuousAt_log hp.ne').tendsto.comp (moving_partition_ratio_limit x y z)).neg

end OperatorDerivativeRewrite.Foundation.FourCubeMovingLaplaceLimit
