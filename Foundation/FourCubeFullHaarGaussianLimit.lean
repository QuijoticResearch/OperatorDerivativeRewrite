import Foundation.FourCubeFullChartQuadratic

/-! Actual full32 cutoff-Haar Gaussian convergence and bounded observable limits.
This is a cutoff theorem; the off-cutoff and odd-quotient obligations remain separate. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullHaarGaussianLimit
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2MatrixExponentialBridge
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedSourceRows
open FourCubeFullChartOdd FourCubeFullChartQuadratic FourCubeFullHaarCoordinates
open FourCubeFullHaarCutoff

attribute [local irreducible] edges innerFaces upperFaces

def parameters (x y z t : ℝ) : Fin 3 → SU2 := FourCubeCompletedHaar.angles (t*x) (t*y) (t*z)
def thermalDensity (x y z t : ℝ) : Coordinates → ℝ := scaledDensity (parameters x y z t) (1/t^2) t
def gaussianDensity (x y z : ℝ) (Y : Coordinates) : ℝ :=
  productDensity 0*Real.exp (-completedQuadratic Y x y z/2)

theorem completedQuadratic_continuous (x y z : ℝ) :
    Continuous (fun Y : Coordinates => completedQuadratic Y x y z) := by
  have hv (e : FullEdge) : Continuous (fun Y : Coordinates => pauliVelocity Y x y z e) := by
    cases e with
    | inl e => unfold pauliVelocity SU2HemisphereJets.frame; fun_prop
    | inr c => exact continuous_const
  have hp (p : FullFace) : Continuous (fun Y : Coordinates => faceQuadratic Y x y z p) := by
    have h := (((hv (rowEdges p 0)).add (hv (rowEdges p 1))).sub (hv (rowEdges p 2))).sub (hv (rowEdges p 3))
    exact (continuous_finset_sum _ (fun a _ => ((continuous_apply a).comp h).pow 2)).div_const 4
  have hd (e : Interior) : Continuous (fun Y : Coordinates =>
      (FourCubeNegativeCompletion.multiplicity e : ℝ)*SU2HemisphereJets.sizeSq (Y e)) := by
    unfold SU2HemisphereJets.sizeSq
    fun_prop
  exact (continuous_finset_sum _ (fun p _ => hp p)).add (continuous_finset_sum _ (fun e _ => hd e))

theorem gaussianDensity_continuous (x y z : ℝ) : Continuous (gaussianDensity x y z) :=
  continuous_const.mul (Real.continuous_exp.comp ((completedQuadratic_continuous x y z).neg.div_const 2))

theorem eventually_cutoff (Y : Coordinates) : ∀ᶠ t : ℝ in 𝓝 0,t • Y∈coordinateCutoff := by
  have he (e : Interior) : ∀ᶠ t : ℝ in 𝓝 0,chartRate (t • Y e) ≤ 2 := by
    have hc : Continuous (fun t : ℝ => chartRate (t • Y e)) := by unfold chartRate; fun_prop
    have h := hc.continuousAt.tendsto.eventually
      (eventually_lt_nhds (show chartRate ((0 : ℝ) • Y e)<2 by norm_num [chartRate]))
    exact h.mono (fun t ht => ht.le)
  simpa only [coordinateCutoff,Set.mem_setOf_eq,Pi.smul_apply] using eventually_all.mpr he

theorem thermalDensity_tendsto (x y z : ℝ) (Y : Coordinates) :
    Tendsto (fun t : ℝ => thermalDensity x y z t Y) (𝓝[≠] 0) (𝓝 (gaussianDensity x y z Y)) := by
  have hp := (productDensity_scaled_tendsto Y).mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  rw [← productDensity_zero] at hp
  have hh := hp.mul (completed_boltzmann_limit Y x y z)
  change Tendsto _ _ (𝓝 (gaussianDensity x y z Y)) at hh
  apply hh.congr'
  filter_upwards [(eventually_cutoff Y).filter_mono nhdsWithin_le_nhds] with t ht
  unfold thermalDensity scaledDensity density
  rw [Set.indicator_of_mem ht]
  change productDensity (t • Y)*Real.exp (-completedRay Y x y z t/t^2)=
    productDensity (t • Y)*Real.exp (-(1/t^2)*completedRay Y x y z t)
  congr 1
  congr 1
  ring

theorem thermalDensity_nonneg (x y z t : ℝ) (Y : Coordinates) : 0 ≤ thermalDensity x y z t Y :=
  scaledDensity_nonneg _ _ _ _

theorem thermalDensity_bound (x y z t : ℝ) (ht : t≠0) (Y : Coordinates) :
    thermalDensity x y z t Y ≤ productDensity 0*Real.exp (-FourCubeFullChartDomination.mass Y/4) := by
  apply scaledDensity_bound
  · positivity
  · field_simp [ht]

theorem gaussianDensity_bound (x y z : ℝ) (Y : Coordinates) :
    gaussianDensity x y z Y ≤ productDensity 0*Real.exp (-FourCubeFullChartDomination.mass Y/4) := by
  apply le_of_tendsto (thermalDensity_tendsto x y z Y)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact thermalDensity_bound x y z t ht Y

theorem gaussianDensity_positive (x y z : ℝ) (Y : Coordinates) : 0<gaussianDensity x y z Y :=
  mul_pos (productDensity_positive _) (Real.exp_pos _)

theorem gaussianDensity_integrable (x y z : ℝ) : Integrable (gaussianDensity x y z) := by
  apply (gaussian_majorant_integrable.const_mul (productDensity 0)).mono'
    (gaussianDensity_continuous x y z).aestronglyMeasurable
  filter_upwards with Y
  rw [Real.norm_eq_abs,abs_of_pos (gaussianDensity_positive x y z Y)]
  exact gaussianDensity_bound x y z Y

theorem gaussian_integral_positive (x y z : ℝ) : 0<∫ Y : Coordinates,gaussianDensity x y z Y := by
  have he : (∫ Y : Coordinates,gaussianDensity x y z Y)=
      productDensity 0*(∫ Y : Coordinates,Real.exp (-completedQuadratic Y x y z/2)) := integral_const_mul _ _
  have hi : Integrable (fun Y : Coordinates => Real.exp (-completedQuadratic Y x y z/2)) := by
    have h := (gaussianDensity_integrable x y z).const_mul ((productDensity 0)⁻¹)
    convert! h using 1
    funext Y
    simp [gaussianDensity,← mul_assoc,(productDensity_positive 0).ne']
  rw [he]
  exact mul_pos (productDensity_positive 0) (integral_exp_pos hi)

/-- Genuine dominated convergence of the actual rescaled96-dimensional cutoff density. -/
theorem thermal_integral_tendsto (x y z : ℝ) :
    Tendsto (fun t : ℝ => ∫ Y : Coordinates,thermalDensity x y z t Y) (𝓝[≠] 0)
      (𝓝 (∫ Y : Coordinates,gaussianDensity x y z Y)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun Y : Coordinates => productDensity 0*Real.exp (-FourCubeFullChartDomination.mass Y/4))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (scaledDensity_integrable _ _ t ht).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards with Y
    rw [Real.norm_eq_abs,abs_of_nonneg (thermalDensity_nonneg x y z t Y)]
    exact thermalDensity_bound x y z t ht Y
  · exact gaussian_majorant_integrable.const_mul _
  · exact ae_of_all _ (thermalDensity_tendsto x y z)

/-- Actual cutoff-Haar partition, with strictly positive finite Gaussian leading coefficient. -/
theorem actual_cutoff_partition_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => localPartition (parameters x y z t) (1/t^2)/|t|^96) (𝓝[≠] 0)
      (𝓝 (∫ Y : Coordinates,gaussianDensity x y z Y)) := by
  apply (thermal_integral_tendsto x y z).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [localPartition_rescale _ _ t ht]
  have hn : |t|^96≠0 := pow_ne_zero _ (abs_ne_zero.mpr ht)
  change _=(|t|^96*(∫ Y : Coordinates,thermalDensity x y z t Y))/|t|^96
  field_simp [hn,abs_ne_zero.mpr ht]

theorem bounded_test_integral_tendsto (x y z : ℝ) (f : Coordinates → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ Y,|f Y| ≤ M) :
    Tendsto (fun t : ℝ => ∫ Y : Coordinates,f Y*thermalDensity x y z t Y) (𝓝[≠] 0)
      (𝓝 (∫ Y : Coordinates,f Y*gaussianDensity x y z Y)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun Y : Coordinates => M*(productDensity 0*Real.exp (-FourCubeFullChartDomination.mass Y/4)))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact hf.aestronglyMeasurable.mul (scaledDensity_integrable _ _ t ht).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards with Y
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (thermalDensity_nonneg x y z t Y)]
    exact mul_le_mul (hbound Y) (thermalDensity_bound x y z t ht Y) (thermalDensity_nonneg x y z t Y) hM
  · exact (gaussian_majorant_integrable.const_mul (productDensity 0)).const_mul M
  · exact ae_of_all _ (fun Y => (thermalDensity_tendsto x y z Y).const_mul (f Y))

theorem normalized_bounded_test_tendsto (x y z : ℝ) (f : Coordinates → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ Y,|f Y| ≤ M) :
    Tendsto (fun t : ℝ => (∫ Y : Coordinates,f Y*thermalDensity x y z t Y)/
      (∫ Y : Coordinates,thermalDensity x y z t Y)) (𝓝[≠] 0)
      (𝓝 ((∫ Y : Coordinates,f Y*gaussianDensity x y z Y)/(∫ Y : Coordinates,gaussianDensity x y z Y))) :=
  (bounded_test_integral_tendsto x y z f hf M hM hbound).div (thermal_integral_tendsto x y z)
    (gaussian_integral_positive x y z).ne'

end OperatorDerivativeRewrite.Foundation.FourCubeFullHaarGaussianLimit
