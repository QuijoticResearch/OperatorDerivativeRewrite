import Foundation.IBMFourierClockGraph
import Foundation.GaussianBrownianPRP
import Foundation.GaussianFiniteHorizonAdjoint

/-! Genuine Brownian-clock Clark--Ocone for completed actual multitime IBM
source means. Predictability is for the hidden Brownian clock, not the observed
IBM filtration. The original derivative and Ito integral are unchanged. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFourierClockClarkOcone
open InfiniteGaussian GaussianTimeProcess GaussianBrownianGeneratedSpace
open GaussianPredictableFull GaussianPredictableAdjoint
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

variable {ι : Type*} [Fintype ι] (a : ℕ → ι → ℝ) (β w : ℕ → ℝ)

theorem mean_value_continuous (hv : Summable (fun k => |w k|)) :
    Continuous (IBMFourierClockMeanRegularity.value a β w) := by
  change Continuous (fun x : ι → ℝ => ∑' k, IBMFourierClockMeanRegularity.term a β w k x)
  apply continuous_tsum (fun k => ?_) hv (IBMFourierClockMeanRegularity.term_bound a β w)
  unfold IBMFourierClockMeanRegularity.term IBMFourierClockMeanRegularity.damping
  simp only [IBMFoldedSourceCovariance.variance_expansion]
  fun_prop

theorem clockMean_brownian (r : ι → ℝ≥0) (hv : Summable (fun k => |w k|)) :
    IBMFourierSourceMeanCalculus.clockMean a β w r ∈ brownianL2 := by
  have hm : Measurable[brownianSigma] (fun Y =>
      IBMFourierClockMeanRegularity.value a β w (fun i => process (r i) Y)) := by
    letI : MeasurableSpace SampleSpace := brownianSigma
    exact (mean_value_continuous a β w hv).measurable.comp
      (Measurable.of_eval fun i => process_brownian_measurable (r i))
  exact hm.stronglyMeasurable.aestronglyMeasurable.congr
    (IBMFourierClockMeanRegularity.clockMean_actual a β w r hv).symm

theorem clockMean_past (r : ι → ℝ≥0) (T : ℝ≥0) (hr : ∀ i, r i ≤ T)
    (hv : Summable (fun k => |w k|)) :
    IBMFourierSourceMeanCalculus.clockMean a β w r ∈ GaussianConditionalIto.pastL2 T := by
  have hm : Measurable[naturalFiltration T] (fun Y =>
      IBMFourierClockMeanRegularity.value a β w (fun i => process (r i) Y)) := by
    letI : MeasurableSpace SampleSpace := naturalFiltration T
    exact (mean_value_continuous a β w hv).measurable.comp
      (Measurable.of_eval fun i => ((process_stronglyAdapted (r i)).mono
        (naturalFiltration.mono (hr i))).measurable)
  exact hm.stronglyMeasurable.aestronglyMeasurable.congr
    (IBMFourierClockMeanRegularity.clockMean_actual a β w r hv).symm

def coefficient (r : ι → ℝ≥0) : fullPredictable :=
  predictableAdjoint (IBMFourierSourceMeanCalculus.clockMean a β w r)

theorem coefficient_supported (r : ι → ℝ≥0) (T : ℝ≥0) (hr : ∀ i, r i ≤ T)
    (hv : Summable (fun k => |w k|)) :
    GaussianPredictableCutoff.predictableCut T (coefficient a β w r) = coefficient a β w r :=
  GaussianConditionalClarkOcone.past_representer_supported T _
    (clockMean_past a β w r T hr hv)

theorem finite_reconstruction (r : ι → ℝ≥0) (T : ℝ≥0) (hr : ∀ i, r i ≤ T)
    (hv : Summable (fun k => |w k|)) :
    GaussianPredictableHorizon.itoIntegral T
      (GaussianFiniteHorizonAdjoint.finiteAdjoint T
        (IBMFourierSourceMeanCalculus.clockMean a β w r)) =
      IBMFourierSourceMeanCalculus.clockMean a β w r -
        (∫ Y, IBMFourierSourceMeanCalculus.clockMean a β w r Y ∂gaussianProduct) • gaussianOne :=
  GaussianFiniteHorizonAdjoint.finiteAdjoint_representation T _
    (clockMean_past a β w r T hr hv)

theorem stochastic_reconstruction (r : ι → ℝ≥0)
    (hv : Summable (fun k => |w k|)) :
    itoIntegral (coefficient a β w r) = IBMFourierSourceMeanCalculus.clockMean a β w r -
      (∫ Y, IBMFourierSourceMeanCalculus.clockMean a β w r Y ∂gaussianProduct) • gaussianOne :=
  GaussianBrownianPRP.brownian_representation _ (clockMean_brownian a β w r hv)

theorem coefficient_unique (r : ι → ℝ≥0) (hv : Summable (fun k => |w k|))
    (u : fullPredictable)
    (hu : itoIntegral u = IBMFourierSourceMeanCalculus.clockMean a β w r -
      (∫ Y, IBMFourierSourceMeanCalculus.clockMean a β w r Y ∂gaussianProduct) • gaussianOne) :
    u = coefficient a β w r :=
  itoIntegral.injective (hu.trans (stochastic_reconstruction a β w r hv).symm)

theorem projected_actual_derivative (r : ι → ℝ≥0)
    (hv : Summable (fun k => |w k|))
    (hc : Summable (IBMFourierCylinderSeries.curvatureCost a w)) :
    ∃ G : GaussianVectorL2,
      (IBMFourierSourceMeanCalculus.clockMean a β w r, G) ∈
        closedCylindricalDerivative.graph ∧
      G =ᵐ[gaussianProduct] (fun Y => ∑' k,
        (w k * Real.cos (β k)) • IBMMultitimeClockVarianceGraph.dampingGradient (a k) r Y) ∧
      coefficient a β w r = predictableProjection G := by
  obtain ⟨G, hg, hGa, _⟩ := IBMFourierClockGraph.multitime_clock_graph a β w hv hc r
  let F : closedCylindricalDerivative.domain :=
    ⟨_, LinearPMap.mem_domain_of_mem_graph hg⟩
  have he : closedCylindricalDerivative F = G :=
    closedCylindricalDerivative.mem_graph_snd_inj (closedCylindricalDerivative.mem_graph F) hg rfl
  refine ⟨G, hg, hGa, ?_⟩
  have h := predictableAdjoint_eq_projected_derivative F
  rwa [he] at h

theorem coefficient_stability (r : ι → ℝ≥0) (a' : ℕ → ι → ℝ) (β' w' : ℕ → ℝ) :
    ‖coefficient a β w r - coefficient a' β' w' r‖ ≤
      ‖IBMFourierSourceMeanCalculus.clockMean a β w r -
        IBMFourierSourceMeanCalculus.clockMean a' β' w' r‖ := by
  have hn : ‖predictableAdjoint‖ ≤ 1 := by
    rw [predictableAdjoint, ContinuousLinearMap.adjoint.norm_map]
    exact itoIntegral.norm_toContinuousLinearMap_le
  rw [coefficient, coefficient, ← map_sub]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (norm_nonneg _))

theorem coefficient_zero_of_cos_zero (r : ι → ℝ≥0)
    (hv : Summable (fun k => |w k|)) (hβ : ∀ k, Real.cos (β k) = 0) :
    coefficient a β w r = 0 := by
  have hm : IBMFourierSourceMeanCalculus.clockMean a β w r = 0 := by
    apply Lp.ext
    filter_upwards [IBMFourierClockMeanRegularity.clockMean_actual a β w r hv,
      Lp.coeFn_zero ℝ 2 gaussianProduct] with Y hM h0
    rw [hM, h0]
    simp [IBMFourierClockMeanRegularity.value, IBMFourierClockMeanRegularity.term, hβ]
  simp only [coefficient, hm, map_zero]

end OperatorDerivativeRewrite.Foundation.IBMFourierClockClarkOcone
