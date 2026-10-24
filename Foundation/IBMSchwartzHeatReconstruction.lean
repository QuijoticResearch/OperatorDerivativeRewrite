import Foundation.IBMSchwartzHeatCanonical

/-! Actual native nonlinear clock reconstruction for the explicit finite-energy
heat score. The entire initial scenery remains a parameter, not IBM time0 data. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatReconstruction
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianPredictableFull
open GaussianPredictableAdjoint IBMSchwartzHeatCanonical IBMSchwartzHeatPredictable
open IBMSchwartzHalfHolderHeat IBMSchwartzHeatDerivative IBMTimeAveragedObservable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local irreducible] curve heatScore GaussianHalfHolderScore.score
  IBMSchwartzHeatPredictable.nativeField value input raw scalarInput
  IBMIntrinsicOperators.clockDerivative

theorem scalar_reconstruction (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (L : GaussianL2 →L[ℝ] ℝ) :
    L.compLpL 2 gaussianProduct (GaussianSourceClockIto.integral T (input g a T)) =
      terminal g a T L - (∫ Y, terminal g a T L Y ∂gaussianProduct) • gaussianOne := by
  have hh : (full g a T L : TimeProbabilityL2) =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z => L ((input g a T).val z)) := by
    have hu : (fun z => L (raw g a T z)) =ᵐ[BrownianClockWeightedEnergy.base T]
        fun z => L ((input g a T).val z) :=
      (input_ae g a T).symm.mono fun z hz => congrArg L hz
    exact (full_ae g a T L).trans
      ((ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp hu)
  rw [GaussianSourceClockIto.scalarization_full T L (input g a T) (full g a T L) hh,
    full_eq_adjoint]
  exact GaussianBrownianPRP.brownian_representation _
    (GaussianConditionalClarkOcone.past_mem_brownian T (terminal_past g a T L))

theorem source_reconstruction (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    GaussianSourceClockIto.integral T (input g a T) =
      IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T -
        Lp.const 2 gaussianProduct
          (∫ Y, IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T Y ∂gaussianProduct) := by
  let U := GaussianSourceClockIto.integral T (input g a T)
  let E := IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T
  let m : GaussianL2 := ∫ Y, E Y ∂gaussianProduct
  have hscalar (L : GaussianL2 →L[ℝ] ℝ) :
      L.compLpL 2 gaussianProduct U = L.compLpL 2 gaussianProduct E - L m • gaussianOne := by
    have h := scalar_reconstruction g a T L
    change L.compLpL 2 gaussianProduct U = L.compLpL 2 gaussianProduct E -
      (∫ Y, L.compLpL 2 gaussianProduct E Y ∂gaussianProduct) • gaussianOne at h
    have hm : (∫ Y, L.compLpL 2 gaussianProduct E Y ∂gaussianProduct) = L m := by
      calc
        _ = ∫ Y, L (E Y) ∂gaussianProduct := integral_congr_ae (L.coeFn_compLpL E)
        _ = _ := L.integral_comp_comm ((Lp.memLp E).integrable (by norm_num))
    rw [hm] at h
    exact h
  have hz : (fun Y => U Y-(E Y-m)) =ᵐ[gaussianProduct] 0 := by
    apply ae_eq_zero_of_forall_dual ℝ
    intro L
    filter_upwards [L.coeFn_compLpL U,L.coeFn_compLpL E,
      Lp.coeFn_sub (L.compLpL 2 gaussianProduct E) (L m • gaussianOne),
      Lp.coeFn_smul (L m) gaussianOne,gaussianOne_coeFn] with Y hU hE hsub hsm hone
    have h := congrArg (fun F : GaussianL2 => F Y) (hscalar L)
    rw [hU,hsub,Pi.sub_apply,hE,hsm,Pi.smul_apply,hone,smul_eq_mul,mul_one] at h
    change L (U Y-(E Y-m)) = 0
    rw [map_sub,map_sub,h]
    ring
  apply Lp.ext
  filter_upwards [hz,Lp.coeFn_sub E (Lp.const 2 gaussianProduct m),
    Lp.coeFn_const 2 gaussianProduct m] with Y hY hsub hc
  change U Y = (E-Lp.const 2 gaussianProduct m) Y
  rw [hsub,Pi.sub_apply,hc]
  exact sub_eq_zero.mp hY

theorem initial_mean (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    (∫ Y, IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T Y ∂gaussianProduct) =
      heatMean g a 0 T := by
  have he : IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T =ᵐ[gaussianProduct]
      fun Y => curve g a (process T Y) := by
    filter_upwards [IBMSchwartzPhysicalPrimitiveClock.endpointLimit_ae g a T,
      IBMConstructedSources.clockPath_coordinate_ae T] with Y hY hc
    rw [hY,hc]
    simp only [curve]
  calc
    _ = ∫ Y, curve g a (process T Y) ∂gaussianProduct := integral_congr_ae he
    _ = ∫ x, curve g a x ∂ProbabilityTheory.gaussianReal 0 T :=
      (process_hasLaw T).integral_comp (curve_continuous g a).aestronglyMeasurable
    _ = _ := by simpa only [zero_add] using (heatMean_gaussian g a 0 T).symm

theorem native_reconstruction (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    value g a T = jointRealization
      (IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T -
        Lp.const 2 gaussianProduct (heatMean g a 0 T)) := by
  unfold value scalarInput
  rw [IBMSchwartzNativeJointIto.integral_agreement,source_reconstruction,initial_mean]

theorem native_adjoint_reconstruction (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∃ hi : nativeField g a T ∈ IBMIntrinsicOperators.clockDerivative.adjoint.domain,
      IBMIntrinsicOperators.clockDerivative.adjoint ⟨nativeField g a T,hi⟩ = jointRealization
        (IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T -
          Lp.const 2 gaussianProduct (heatMean g a 0 T)) := by
  unfold IBMSchwartzHeatPredictable.nativeField
  refine ⟨IBMSceneryNativeAdjoint.clock_mem T (scalarInput g a T),?_⟩
  exact (IBMSceneryNativeAdjoint.clock_value T (scalarInput g a T)).trans
    (by simpa only [value] using native_reconstruction g a T)

theorem native_actual (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    value g a T =ᵐ[IBMSourceLaws.jointMeasure] fun p =>
      g (a+IBMConstructedSources.ibmValue T p) - heatMean g a 0 T p.1 := by
  rw [native_reconstruction]
  apply jointRealization_ae_of_sections
  · exact (g.continuous.measurable.comp
      (measurable_const.add (IBMConstructedSources.ibmValue_jointly_measurable.comp
        (measurable_const.prodMk measurable_id)))).sub
      ((Lp.stronglyMeasurable (heatMean g a 0 T)).measurable.comp measurable_fst)
  · filter_upwards [IBMSchwartzPhysicalPrimitiveClock.endpointLimit_actual_sections g a T,
      Lp.coeFn_sub (IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T)
        (Lp.const 2 gaussianProduct (heatMean g a 0 T)),
      Lp.coeFn_const 2 gaussianProduct (heatMean g a 0 T)] with Y he hsub hc
    rw [hsub,Pi.sub_apply,hc]
    simp only [Function.const_apply]
    filter_upwards [he,Lp.coeFn_sub
      (IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T Y) (heatMean g a 0 T)] with X hX hs
    rw [hs,Pi.sub_apply,hX]

theorem actual_native_sections (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ X ∂gaussianProduct, GaussianPredictableHorizon.itoIntegral T
      (IBMSceneryClockIto.sectionPredictable T (scalarInput g a T) X) =ᵐ[gaussianProduct]
        fun Y => g (a+IBMConstructedSources.ibmValue T (X,Y)) - heatMean g a 0 T X := by
  have h : ∀ᵐ p ∂gaussianProduct.prod gaussianProduct, value g a T p =
      g (a+IBMConstructedSources.ibmValue T p) - heatMean g a 0 T p.1 := native_actual g a T
  filter_upwards [native_sections g a T,Measure.ae_ae_of_ae_prod h] with X hN hA
  exact hN.symm.trans hA

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatReconstruction
