import Foundation.IBMSineAverageClockDomain
import Foundation.IBMBochnerTimeQuadrature

/-! The actual nonlinear IBM time average has a source derivative as well.
Finite native graph quadratures avoid assuming time measurability or strong
convergence of the point derivative field. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMSineAverageSourceDomain
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMActualSineDomainObstruction IBMBochnerTimeQuadrature IBMContinuousQuadrature
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem slopeField_norm_le (f : JointL2) (g : IBMIntrinsicChainRule.JointVectorL2) :
    ‖IBMClockWeakChain.slopeField sineTest f g‖ ≤ ‖g‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [IBMClockWeakChain.slopeField_ae sineTest f g] with p hp
  rw [hp, norm_smul]
  exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _)).trans_eq (one_mul _)

theorem sourceGradient_norm_le (t : ℝ≥0) :
    ‖sineSourceGradient t‖ ≤ ‖IBMRandomTimeHilbert.randomSourceL2 t‖ := by
  let f : JointL2 := ProductL2Curry.swap gaussianProduct gaussianProduct (intrinsicCurve t : JointL2)
  calc
    _ = ‖IBMClockWeakChain.slopeField sineTest f
        (IBMIntrinsicChainRule.uncurryField (IBMUnmollifiedSourceDerivative.gradient t))‖ :=
      (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).norm_map _
    _ ≤ ‖IBMIntrinsicChainRule.uncurryField (IBMUnmollifiedSourceDerivative.gradient t)‖ :=
      slopeField_norm_le _ _
    _ = _ := (IBMIntrinsicChainRule.uncurryField_norm _).trans
      (IBMUnmollifiedSourceDerivative.gradient_norm t)

theorem sourceGradient_bounded (T : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ≥0) T, ‖sineSourceGradient t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).exists_bound_of_continuousOn
    source_time_continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (sourceGradient_norm_le t).trans ((hC t ht).trans (le_max_left _ _))

def valueCurve (t : ℝ) : ScalarFieldSpace := sourceUnitary (sinePoint t.toNNReal : JointL2)

theorem valueCurve_continuous : Continuous valueCurve :=
  sourceUnitary.continuous.comp (IntrinsicSpace.subtypeL.continuous.comp
    (sinePoint_continuous.comp continuous_real_toNNReal))

def gradientSum (T : ℝ≥0) (n : ℕ) : FieldSpace :=
  ∑ i ∈ Finset.range (n + 1), ((T : ℝ) / (n + 1 : ℕ)) •
    sineSourceGradient (time T (n + 1) (i + 1)).toNNReal

theorem quadrature_graph (T : ℝ≥0) (n : ℕ) :
    (rightSum valueCurve T (n + 1), gradientSum T n) ∈ IBMClockGraphDualLimit.Clock.graph := by
  unfold rightSum gradientSum
  rw [prod_mk_sum]
  apply IBMClockGraphDualLimit.Clock.graph.sum_mem
  intro i hi
  exact IBMClockGraphDualLimit.Clock.graph.smul_mem ((T : ℝ) / (n + 1 : ℕ))
    (sinePoint_source_graph _)

theorem gradientSum_norm_le (T : ℝ≥0) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ t ∈ Icc (0 : ℝ≥0) T, ‖sineSourceGradient t‖ ≤ C) (n : ℕ) :
    ‖gradientSum T n‖ ≤ (T : ℝ) * C := by
  have hstep : 0 ≤ (T : ℝ) / (n + 1 : ℕ) := div_nonneg T.property (by positivity)
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ‖((T : ℝ) / (n + 1 : ℕ)) • sineSourceGradient (time T (n + 1) (i + 1)).toNNReal‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (n + 1), ((T : ℝ) / (n + 1 : ℕ)) * C := by
      apply Finset.sum_le_sum
      intro i hi
      have ht := time_mem T.property (by omega : 0 < n + 1)
        (by have hi' := Finset.mem_range.mp hi; omega : i + 1 ≤ n + 1)
      have hm : (time T (n + 1) (i + 1)).toNNReal ∈ Icc (0 : ℝ≥0) T :=
        ⟨by positivity, (Real.toNNReal_le_iff_le_coe).mpr ht.2⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hstep]
      exact mul_le_mul_of_nonneg_left (hb _ hm) hstep
    _ = (T : ℝ) * C := by simp; field_simp

theorem valueCurve_integral (T : ℝ≥0) :
    (∫ t in (0 : ℝ)..(T : ℝ), valueCurve t) =
      sourceUnitary (IBMSineAverageSimpson.average T : JointL2) := by
  have he (t : ℝ) : (sinePoint t.toNNReal : JointL2) = IBMSineAverageClockDomain.point t := rfl
  have hv : Integrable (fun t : ℝ => (sinePoint t.toNNReal : JointL2)) (IBMClockOverlapEnergy.window T) := by
    simpa only [he] using IBMSineAverageClockDomain.point_integrable T
  have hm : (∫ t, valueCurve t ∂IBMClockOverlapEnergy.window T) =
      sourceUnitary (∫ t, (sinePoint t.toNNReal : JointL2) ∂IBMClockOverlapEnergy.window T) :=
    sourceUnitary.toLinearIsometry.toContinuousLinearMap.integral_comp_comm hv
  calc
    _ = (∫ t, valueCurve t ∂IBMClockOverlapEnergy.window T) :=
      intervalIntegral.integral_of_le T.property
    _ = _ := hm
    _ = _ := by
      congr 1
      simp_rw [he]
      exact IBMSineAverageClockDomain.limitAverage_eq_actual T

theorem actual_average_source_domain (T : ℝ≥0) :
    sourceUnitary (IBMSineAverageSimpson.average T : JointL2) ∈ IBMClockGraphDualLimit.Clock.domain := by
  obtain ⟨C, hC, hb⟩ := sourceGradient_bounded T
  have hu := rightSum_tendsto valueCurve valueCurve_continuous T.property
  have hu' : Tendsto (fun n => rightSum valueCurve T (n + 1)) atTop
      (𝓝 (sourceUnitary (IBMSineAverageSimpson.average T : JointL2))) :=
    (valueCurve_integral T) ▸ hu
  exact ClosedOperatorEscapeEnergy.mem_domain_of_frequently_bounded_graph
    IBMClockGraphDualLimit.Clock IBMClockGraphDualLimit.clock_closed IBMClockGraphDualLimit.clock_dense
    (quadrature_graph T) hu' ((T : ℝ) * C)
    (Eventually.of_forall (gradientSum_norm_le T hC hb)).frequently

theorem actual_average_in_sourceDomain (T : ℝ≥0) :
    (IBMSineAverageSimpson.average T : JointL2) ∈ IBMFiniteAverageCore.sourceDomain :=
  actual_average_source_domain T

end OperatorDerivativeRewrite.Foundation.IBMSineAverageSourceDomain
