import Foundation.GaussianC2TimeWeighted
import Foundation.GaussianSmoothConditional
import Foundation.BochnerL2RepresentativeFubini
import Foundation.BrownianAugmentedMartingales
import Foundation.BrownianClockWeightedEnergy

/-! Continuous actual C2 Brownian compensated paths, identified with the
existing predictable integral. The drift is an actual pathwise time integral. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianC2MartingaleRealization
open InfiniteGaussian GaussianTimeProcess IBMConstructedSources GaussianPredictableFull
open GaussianC2Ito BrownianMassClockStoppingTime BrownianAugmentedMartingales
set_option backward.isDefEq.respectTransparency false
variable (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K0 K1 : ℝ≥0)
  (h0 : ∀ x, ‖deriv f x‖₊ ≤ K0) (h1 : ∀ x, ‖deriv (deriv f) x‖₊ ≤ K1)

def rate (ω : SampleSpace) (s : ℝ) : ℝ := deriv (deriv f) (clockPath ω s.toNNReal)

include hf in
theorem rate_continuous (ω : SampleSpace) : Continuous (rate f ω) :=
  (second_continuous f hf).comp ((clockPath ω).continuous.comp continuous_real_toNNReal)

include hf in
theorem rate_joint : Measurable (fun z : ℝ × SampleSpace => rate f z.2 z.1) :=
  (second_continuous f hf).measurable.comp BrownianClockWeightedEnergy.sigma_measurable

def primitive (ω : SampleSpace) (t : ℝ) : ℝ := (1/2 : ℝ)*∫ s in 0..t, rate f ω s

include hf in
theorem primitive_hasDerivAt (ω : SampleSpace) (t : ℝ) :
    HasDerivAt (primitive f ω) ((1/2 : ℝ)*rate f ω t) t := by
  have hc := rate_continuous f hf ω
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul (1/2 : ℝ)

include hf in
theorem primitive_continuous (ω : SampleSpace) : Continuous (primitive f ω) :=
  continuous_iff_continuousAt.mpr (fun t => (primitive_hasDerivAt f hf ω t).continuousAt)

include hf in
theorem primitive_coordinate_measurable (T : ℝ≥0) :
    Measurable (fun ω => primitive f ω T) := by
  have hm : StronglyMeasurable (fun z : SampleSpace × ℝ => rate f z.1 z.2) :=
    ((rate_joint f hf).comp measurable_swap).stronglyMeasurable
  have hi := hm.integral_prod_right' (ν := volume.restrict (Ioc 0 (T : ℝ)))
  unfold primitive
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact hi.measurable.const_mul (1/2 : ℝ)

theorem primitive_coeFn (T : ℝ≥0) :
    ((1/2 : ℝ) • (∫ s in 0..(T : ℝ), curvatureValue f hf K1 h1 s.toNNReal) : GaussianL2)
      =ᵐ[gaussianProduct] fun ω => primitive f ω T := by
  have hc := (GaussianC2TimeWeighted.curvature_continuous f hf K1 h1).comp continuous_real_toNNReal
  have hr (s : ℝ) : curvatureValue f hf K1 h1 s.toNNReal =ᵐ[gaussianProduct] (fun ω => rate f ω s) := by
    filter_upwards [curvatureValue_coeFn f hf K1 h1 s.toNNReal,
      clockPath_coordinate_ae s.toNNReal] with ω hω hb
    change curvatureValue f hf K1 h1 s.toNNReal ω = _ at hω
    rw [hω,← hb]
    rfl
  have h := BochnerL2RepresentativeFubini.integral_coeFn_ae
    (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := gaussianProduct)
    (fun s : ℝ => curvatureValue f hf K1 h1 s.toNNReal) ((hc.intervalIntegrable 0 (T : ℝ)).1)
    (fun z : ℝ × SampleSpace => rate f z.2 z.1)
    (rate_joint f hf).stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall hr)
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  filter_upwards [h, Lp.coeFn_smul (1/2 : ℝ)
    (∫ s in Ioc 0 (T : ℝ), curvatureValue f hf K1 h1 s.toNNReal)] with ω hω hs
  rw [hs, Pi.smul_apply, smul_eq_mul, hω]
  simp only [primitive, intervalIntegral.integral_of_le T.coe_nonneg]

def compensatedPath (ω : SampleSpace) : C(ℝ≥0, ℝ) :=
  ⟨fun t => f (clockPath ω t)-f 0-primitive f ω t,
    ((hf.continuous.comp (clockPath ω).continuous).sub continuous_const).sub
      ((primitive_continuous f hf ω).comp NNReal.continuous_coe)⟩

theorem compensated_coordinate_measurable (T : ℝ≥0) :
    Measurable (fun ω => compensatedPath f hf ω T) :=
  ((hf.continuous.measurable.comp (brownian_coordinate_measurable T)).sub_const (f 0)).sub
    (primitive_coordinate_measurable f hf T)

theorem compensatedPath_measurable : Measurable (compensatedPath f hf) :=
  ContinuousMap.measurable_iff_eval.mpr (compensated_coordinate_measurable f hf)

include K0 K1 h0 h1

theorem integral_coeFn (T : ℝ≥0) :
    itoIntegral (GaussianLipschitzIntegrands.integrand (derivativeLip f hf K1 h1) T)
      =ᵐ[gaussianProduct] fun ω => compensatedPath f hf ω T := by
  filter_upwards [c2_ito_ae f hf K0 K1 h0 h1 T, primitive_coeFn f hf K1 h1 T,
    clockPath_coordinate_ae T, Lp.coeFn_smul (1/2 : ℝ)
      (∫ s in 0..(T : ℝ), curvatureValue f hf K1 h1 s.toNNReal)] with ω hi hp hb hs
  rw [← hb] at hi
  rw [hs, Pi.smul_apply, smul_eq_mul] at hp
  change _ = f (clockPath ω T)-f 0-primitive f ω T
  linarith

theorem compensated_integrable (T : ℝ≥0) :
    Integrable (fun ω => compensatedPath f hf ω T) gaussianProduct :=
  ((Lp.memLp (itoIntegral (GaussianLipschitzIntegrands.integrand (derivativeLip f hf K1 h1) T))).integrable
    (by norm_num)).congr (integral_coeFn f hf K0 K1 h0 h1 T)

theorem compensated_conditional (S T : ℝ≥0) (hST : S ≤ T) :
    gaussianProduct[(fun ω => compensatedPath f hf ω T) | naturalFiltration S]
      =ᵐ[gaussianProduct] fun ω => compensatedPath f hf ω S := by
  have h := GaussianConditionalIto.pastProjection_ae S
    (itoIntegral (GaussianLipschitzIntegrands.integrand (derivativeLip f hf K1 h1) T))
  rw [GaussianConditionalIto.pastProjection_integral, GaussianSmoothConditional.cut_integrand,
    min_eq_left hST] at h
  exact ((condExp_congr_ae (integral_coeFn f hf K0 K1 h0 h1 T)).symm.trans h.symm).trans
    (integral_coeFn f hf K0 K1 h0 h1 S)

theorem compensated_stronglyAdapted :
    StronglyAdapted augmentedPast (fun t ω => compensatedPath f hf ω t) := by
  intro t
  have hraw := GaussianConditionalIto.integral_cut_mem_past t
    (GaussianLipschitzIntegrands.integrand (derivativeLip f hf K1 h1) t)
  rw [GaussianSmoothConditional.cut_integrand, min_self] at hraw
  change AEStronglyMeasurable[naturalFiltration t]
    (itoIntegral (GaussianLipschitzIntegrands.integrand (derivativeLip f hf K1 h1) t)) gaussianProduct at hraw
  exact (AmbientNullAugmentation.measurable_of_raw_aestronglyMeasurable
    (naturalFiltration t) gaussianProduct (compensated_coordinate_measurable f hf t)
    (hraw.congr (integral_coeFn f hf K0 K1 h0 h1 t))).stronglyMeasurable

theorem compensated_martingale :
    Martingale (fun t ω => compensatedPath f hf ω t) augmentedPast gaussianProduct := by
  refine ⟨compensated_stronglyAdapted f hf K0 K1 h0 h1, ?_⟩
  intro s t hst
  exact (condExp_unchanged s _ (compensated_integrable f hf K0 K1 h0 h1 t)).symm.trans
    (compensated_conditional f hf K0 K1 h0 h1 s t hst)

end OperatorDerivativeRewrite.Foundation.BrownianC2MartingaleRealization
