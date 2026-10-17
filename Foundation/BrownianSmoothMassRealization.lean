import Foundation.BrownianSmoothMassPath
import Foundation.BochnerL2RepresentativeFubini

/-! The pathwise curvature integrals realize the independently constructed
Bochner-L2 drifts. Smooth compensated paths realize actual Ito integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianSmoothMassRealization
open InfiniteGaussian GaussianTimeProcess IBMConstructedSources
open SmoothAbsoluteApproximation RealSteklovApprox BrownianTanakaResidual
open BrownianTanakaApproximation BrownianSmoothMassPath GaussianPredictableFull

theorem curvatureValue_coeFn {e : ℝ} (he : 0 < e) (t : ℝ≥0) :
    curvatureValue he t =ᵐ[gaussianProduct] fun ω => curvature e (clockPath ω t) := by
  filter_upwards [GaussianC2Ito.curvatureValue_coeFn (radius e) (radius_smooth he 2)
    (curvatureConstant he) (second_bound he) t, clockPath_coordinate_ae t] with ω hv hc
  change curvatureValue he t ω = _ at hv
  rw [hv, radius_second_deriv he, hc]

theorem approximateMass_coeFn (n : ℕ) (T : ℝ≥0) :
    approximateMass n T =ᵐ[gaussianProduct] fun ω => path n ω T := by
  have hc := (GaussianC2TimeWeighted.curvature_continuous (radius (width n))
    (radius_smooth (width_pos n) 2) (curvatureConstant (width_pos n))
      (second_bound (width_pos n))).comp continuous_real_toNNReal
  change Continuous (fun t : ℝ => curvatureValue (width_pos n) t.toNNReal) at hc
  have h := BochnerL2RepresentativeFubini.integral_coeFn_ae
    (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := gaussianProduct)
    (fun t : ℝ => curvatureValue (width_pos n) t.toNNReal)
    ((hc.intervalIntegrable 0 (T : ℝ)).1)
    (fun z : ℝ × SampleSpace => rate (width n) z.2 z.1)
    ((rate_joint (width_pos n)).stronglyMeasurable.aestronglyMeasurable) (by
      exact Eventually.of_forall (fun t => curvatureValue_coeFn (width_pos n) t.toNNReal))
  change ((1 / 2 : ℝ) • ∫ t in 0..(T : ℝ), curvatureValue (width_pos n) t.toNNReal)
    =ᵐ[gaussianProduct] _
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  filter_upwards [h, Lp.coeFn_smul (1 / 2 : ℝ)
    (∫ t in Ioc 0 (T : ℝ), curvatureValue (width_pos n) t.toNNReal)] with ω hf hs
  rw [hs, Pi.smul_apply, smul_eq_mul, hf]
  simp only [path, ContinuousMap.coe_mk, primitive,
    intervalIntegral.integral_of_le T.coe_nonneg]

theorem path_memLp (n : ℕ) (T : ℝ≥0) : MemLp (fun ω => path n ω T) 2 gaussianProduct :=
  (Lp.memLp (approximateMass n T)).ae_eq (approximateMass_coeFn n T)

def pathClass (n : ℕ) (T : ℝ≥0) : GaussianL2 := (path_memLp n T).toLp _

theorem pathClass_eq (n : ℕ) (T : ℝ≥0) : pathClass n T = approximateMass n T := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp (path_memLp n T)).trans (approximateMass_coeFn n T).symm

theorem pathClass_tendsto (T : ℝ≥0) :
    Tendsto (fun n => pathClass n T) atTop (𝓝 (mass T)) := by
  simpa only [pathClass_eq] using approximateMass_tendsto T

def compensatedPath (n : ℕ) (ω : SampleSpace) : C(ℝ≥0, ℝ) :=
  ⟨fun t => radius (width n) (clockPath ω t) - width n - path n ω t,
    (((radius_smooth (width_pos n) 2).continuous.comp (clockPath ω).continuous).sub
      continuous_const).sub (path n ω).continuous⟩

theorem compensatedPath_coeFn (n : ℕ) (T : ℝ≥0) :
    itoIntegral (approximateField n T) =ᵐ[gaussianProduct] fun ω => compensatedPath n ω T := by
  have h : itoIntegral (approximateField n T) =
      GaussianLipschitzIntegrands.valueL2 (functionLip (width_pos n)) T -
        width n • gaussianOne - approximateMass n T := by
    have hi := approximateMass_identity n T
    linear_combination (norm := module) hi
  rw [h]
  filter_upwards [Lp.coeFn_sub
    (GaussianLipschitzIntegrands.valueL2 (functionLip (width_pos n)) T - width n • gaussianOne)
    (approximateMass n T),
    Lp.coeFn_sub (GaussianLipschitzIntegrands.valueL2 (functionLip (width_pos n)) T)
      (width n • gaussianOne), Lp.coeFn_smul (width n) gaussianOne, gaussianOne_coeFn,
    GaussianLipschitzIntegrands.valueL2_coeFn (functionLip (width_pos n)) T,
    clockPath_coordinate_ae T, approximateMass_coeFn n T] with ω hs ht hc ho hv hb hm
  simp only [hs, Pi.sub_apply, ht, hc, Pi.smul_apply, smul_eq_mul, ho, mul_one, hv, hm]
  simp only [compensatedPath, ContinuousMap.coe_mk, hb]

theorem compensatedPath_coordinate_measurable (n : ℕ) (T : ℝ≥0) :
    Measurable (fun ω => compensatedPath n ω T) :=
  ((((radius_smooth (width_pos n) 2).continuous.measurable.comp
    ((ContinuousMap.measurable_eval T).comp clockPath_measurable)).sub_const (width n)).sub
      (path_coordinate_measurable n T))

theorem compensatedPath_measurable (n : ℕ) : Measurable (compensatedPath n) :=
  ContinuousMap.measurable_iff_eval.mpr (compensatedPath_coordinate_measurable n)

theorem compensated_conditional (n : ℕ) (S T : ℝ≥0) (hST : S ≤ T) :
    gaussianProduct[(fun ω => compensatedPath n ω T) | naturalFiltration S]
      =ᵐ[gaussianProduct] fun ω => compensatedPath n ω S := by
  have h := GaussianConditionalIto.pastProjection_ae S (itoIntegral (approximateField n T))
  rw [GaussianConditionalIto.pastProjection_integral,
    show GaussianPredictableCutoff.predictableCut S (approximateField n T) =
      approximateField n (min S T) from GaussianSmoothConditional.cut_integrand _ S T,
    min_eq_left hST] at h
  exact ((condExp_congr_ae (compensatedPath_coeFn n T)).symm.trans h.symm).trans
    (compensatedPath_coeFn n S)

end OperatorDerivativeRewrite.Foundation.BrownianSmoothMassRealization
