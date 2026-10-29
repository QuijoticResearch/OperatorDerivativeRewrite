import Foundation.FourCubeOddEnvelope

/-! Dominated Haar-chart integration of the actual first odd Boltzmann correction. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubeOddIntegral
open FourCubeOddEnvelope FourCubeMovingOddAction FourCubeMovingActionLimit
open FourCubeScaledBoundaryControl FourCubeHaarLaplaceDensity FourCubeHaarProductCoordinates
open FourCubeMovingLaplaceLimit FourCubeHemisphereCoercivity
open OneSidedCapComplex SU2QuaternionOddWord QuaternionSU2Representation SU2TraceHessianModel
attribute [local irreducible] OneSidedBlockIncidence.edges OneSidedBlockIncidence.upperFaces OneSidedBlockIncidence.innerFaces

def oddDensity (t x y z : ℝ) (Y : Coordinates) : ℝ :=
  (boundaryScaledDensity t x y z Y-boundaryScaledDensity (-t) x y z Y)/(2*t)
def firstDensity (x y z : ℝ) (Y : Coordinates) : ℝ :=
  -cubicCoefficient Y x y z*limitingDensity x y z Y

def envelope (x y z : ℝ) (Y : Coordinates) : ℝ :=
  (1728*productDensity 0*Real.exp (216*(x^2+y^2+z^2)))*
    ((budget Y x y z)^3*Real.exp (-quadraticMass Y/1116))

theorem productDensity_even (t : ℝ) (Y : Coordinates) : productDensity ((-t) • Y)=productDensity (t • Y) := by
  unfold productDensity SU2GaussianConeCoordinates.chartDensity SU2GaussianConeCoordinates.chartRate
  simp [Pi.smul_apply,smul_eq_mul]

theorem oddDensity_measurable (t x y z : ℝ) : Measurable (oddDensity t x y z) :=
  ((boundaryScaledDensity_measurable t x y z).sub (boundaryScaledDensity_measurable (-t) x y z)).div_const _

theorem oddDensity_bound (t x y z : ℝ) (ht : t ≠ 0) (Y : Coordinates) :
    |oddDensity t x y z Y| ≤ envelope x y z Y := by
  classical
  by_cases hY : Y∈scaledCutoff t
  · have hn := (cutoff_neg t Y).mpr hY
    have he : oddDensity t x y z Y=productDensity (t • Y)*
        ((Real.exp (-movingRay Y x y z t/t^2)-Real.exp (-movingRay Y x y z (-t)/t^2))/(2*t)) := by
      unfold oddDensity boundaryScaledDensity
      rw [Set.indicator_of_mem hY,Set.indicator_of_mem hn,productDensity_even]
      unfold movingRay
      simp only [neg_sq]
      ring
    rw [he,abs_mul,abs_of_nonneg (productDensity_nonneg _)]
    have hb := actual_boltzmann_odd_bound Y x y z t ht hY
    calc
      _ ≤ productDensity 0*((1728*(budget Y x y z)^3*Real.exp (216*(x^2+y^2+z^2)))*
          Real.exp (-quadraticMass Y/1116)) :=
        mul_le_mul (productDensity_le_zero _) hb (abs_nonneg _) (productDensity_nonneg _)
      _ = _ := by unfold envelope; ring
  · have hn := mt (cutoff_neg t Y).mp hY
    simp only [oddDensity,boundaryScaledDensity,Set.indicator_of_notMem hY,
      Set.indicator_of_notMem hn,sub_self,zero_div,abs_zero]
    unfold envelope
    have hp := (budget_positive Y x y z).le
    have hd := productDensity_nonneg (0 : Coordinates)
    positivity

theorem envelope_integrable (x y z : ℝ) : Integrable (envelope x y z) :=
  (cubic_weight_integrable x y z).const_mul _

theorem oddDensity_tendsto (x y z : ℝ) (Y : Coordinates) :
    Tendsto (fun t : ℝ => oddDensity t x y z Y) (𝓝[≠] 0) (𝓝 (firstDensity x y z Y)) := by
  have hp : Tendsto (fun t : ℝ => productDensity (t • Y)) (𝓝[≠] 0) (𝓝 (productDensity 0)) := by
    have hs : Continuous (fun t : ℝ => t • Y) := continuous_id.smul continuous_const
    have hh := (productDensity_continuous.comp hs).tendsto (0 : ℝ)
    simpa only [zero_smul,Function.comp_def,Pi.smul_apply,id_eq] using
      hh.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  have hh := hp.mul (actual_boltzmann_odd_limit Y x y z)
  have hval : productDensity 0*(-cubicCoefficient Y x y z*Real.exp (-jointQuadratic Y x y z/2))=
      firstDensity x y z Y := by unfold firstDensity limitingDensity; ring
  rw [hval] at hh
  apply hh.congr'
  filter_upwards [(eventually_scaledCutoff Y).filter_mono nhdsWithin_le_nhds] with t hY
  have hn := (cutoff_neg t Y).mpr hY
  unfold oddDensity boundaryScaledDensity
  rw [Set.indicator_of_mem hY,Set.indicator_of_mem hn,productDensity_even]
  unfold movingRay
  simp only [neg_sq]
  ring

theorem cubicCoefficient_measurable (x y z : ℝ) : Measurable (fun Y : Coordinates => cubicCoefficient Y x y z) := by
  have halg : Measurable SU2MatrixExponentialBridge.algebraElement := by
    have hc : Continuous SU2MatrixExponentialBridge.algebraElement := by
      unfold SU2MatrixExponentialBridge.algebraElement
      fun_prop
    exact hc.measurable
  have hframe : Measurable SU2HemisphereJets.frame := by
    apply measurable_pi_iff.mpr
    intro a
    fin_cases a <;> simp only [SU2HemisphereJets.frame] <;> fun_prop
  have hlift (e : OneSidedBlockRank.Interior) :
      Measurable (fun Y : Coordinates => FourCubePinnedSecondVariation.liftVelocity Y e) := by
    by_cases hp : e=OneSidedPinnedInterior.pole
    · subst e
      simp only [FourCubePinnedSecondVariation.liftVelocity_pole]
      exact measurable_const
    · have he : (fun Y : Coordinates => FourCubePinnedSecondVariation.liftVelocity Y e)=
          (fun Y : Coordinates => Y (⟨e,hp⟩ : OneSidedPinnedInterior.Free)) :=
        funext (fun Y => FourCubePinnedSecondVariation.liftVelocity_free Y ⟨e,hp⟩)
      rw [he]
      exact measurable_pi_apply _
  have hv (e : FullEdge) : Measurable (fun Y : Coordinates => velocity Y x y z e) := by
    cases e with
    | inl e => exact halg.comp (hframe.comp (hlift e))
    | inr c => exact measurable_const
  have him : Measurable (fun M : M2 => imagVector (recover M)) := by
    apply measurable_pi_iff.mpr
    intro a
    have hh := (coordinateCLM a.succ).continuous.measurable
    fin_cases a <;> convert! hh using 1 <;>
      simp [imagVector,recover,coordinateCLM,coordinateLinear,SU2QuaternionOddWord.coordinate]
  unfold cubicCoefficient
  apply Finset.measurable_sum
  intro p _
  have hs (i : Fin 4) : Measurable (fun Y : Coordinates => slopes (velocity Y x y z) p i) := by
    fin_cases i
    · exact hv _
    · exact hv _
    · exact FourCubeAmbientAction.adjointCLM.continuous.measurable.comp (hv _)
    · exact FourCubeAmbientAction.adjointCLM.continuous.measurable.comp (hv _)
  have hm : Measurable (fun Y : Coordinates =>
      (fun i => imagVector (recover (slopes (velocity Y x y z) p i)))) :=
    measurable_pi_iff.mpr (fun i => him.comp (hs i))
  have hc := weightedCubic_continuous.measurable.comp
    ((measurable_const : Measurable (fun _ : Coordinates => (fun _ : Fin 4 => (1 : ℝ)))).prodMk hm)
  exact hc

theorem firstDensity_measurable (x y z : ℝ) : Measurable (firstDensity x y z) :=
  (cubicCoefficient_measurable x y z).neg.mul (limitingDensity_measurable x y z)

theorem firstDensity_bound (x y z : ℝ) (Y : Coordinates) :
    |firstDensity x y z Y| ≤ envelope x y z Y := by
  apply le_of_tendsto (oddDensity_tendsto x y z Y).abs
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact oddDensity_bound t x y z ht Y

theorem firstDensity_integrable (x y z : ℝ) : Integrable (firstDensity x y z) := by
  apply (envelope_integrable x y z).mono' (firstDensity_measurable x y z).aestronglyMeasurable
  exact ae_of_all _ (fun Y => by rw [Real.norm_eq_abs]; exact firstDensity_bound x y z Y)

theorem oddDensity_integrable (t x y z : ℝ) (ht : t ≠ 0) : Integrable (oddDensity t x y z) :=
  ((boundaryScaledDensity_integrable t ht x y z).sub
    (boundaryScaledDensity_integrable (-t) (neg_ne_zero.mpr ht) x y z)).div_const _
theorem oddDensity_integral_tendsto (x y z : ℝ) :
    Tendsto (fun t : ℝ => ∫ Y : Coordinates,oddDensity t x y z Y) (𝓝[≠] 0)
      (𝓝 (∫ Y : Coordinates,firstDensity x y z Y)) := by
  apply tendsto_integral_filter_of_dominated_convergence (envelope x y z)
  · exact Filter.Eventually.of_forall (fun t => (oddDensity_measurable t x y z).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ae_of_all _ (fun Y => by rw [Real.norm_eq_abs]; exact oddDensity_bound t x y z ht Y)
  · exact envelope_integrable x y z
  · exact ae_of_all _ (oddDensity_tendsto x y z)

theorem scaled_density_integral_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => ((∫ Y : Coordinates,boundaryScaledDensity t x y z Y)-
      (∫ Y : Coordinates,boundaryScaledDensity (-t) x y z Y))/(2*t)) (𝓝[≠] 0)
      (𝓝 (∫ Y : Coordinates,firstDensity x y z Y)) := by
  apply (oddDensity_integral_tendsto x y z).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [oddDensity,integral_div]
  rw [integral_sub (boundaryScaledDensity_integrable t ht x y z)
    (boundaryScaledDensity_integrable (-t) (neg_ne_zero.mpr ht) x y z)]

theorem actual_cutoff_partition_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => (movingLocalPartition t x y z-movingLocalPartition (-t) x y z)/
      (2*t*|t|^93)) (𝓝[≠] 0) (𝓝 (∫ Y : Coordinates,firstDensity x y z Y)) := by
  apply (scaled_density_integral_odd_limit x y z).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [movingLocalPartition_rescale t ht,movingLocalPartition_rescale (-t) (neg_ne_zero.mpr ht),abs_neg]
  field_simp [ht,abs_ne_zero.mpr ht] <;> ring

end OperatorDerivativeRewrite.Foundation.FourCubeOddIntegral
