import Foundation.IBMClockBochnerConverse
import Foundation.IBMClockLinearDivergence

/-! The ACTUAL unmollified IBM point coordinate is outside the ORIGINAL native
clock derivative domain at every positive time. Its scenery partial derivative
remains valid; this does not exclude other calculi or regularized observables. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPointClockDomainObstruction
open InfiniteGaussian IBMClockLinearDivergence IBMClockBochnerConverse
open IBMTimeAveragedObservable IBMClockObservationGraph
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

theorem timeDirection_norm_sq (t : ℝ≥0) : ‖timeDirection t‖ ^ 2 = (t : ℝ) := by
  rw [timeDirection, (SeparableHilbertEmbedding.hilbertEmbedding
    GaussianTimeHilbert.TimeHilbert).norm_map, GaussianTimeHilbert.timeVector_norm_sq]

theorem timeDirection_norm_pos (t : ℝ≥0) (ht : 0 < t) : 0 < ‖timeDirection t‖ := by
  have hn := timeDirection_norm_sq t
  have hp : (0 : ℝ) < t := ht
  nlinarith [norm_nonneg (timeDirection t)]

def unitClock (t : ℝ≥0) : CoefficientSpace := ‖timeDirection t‖⁻¹ • timeDirection t

theorem unitClock_norm (t : ℝ≥0) (ht : 0 < t) : ‖unitClock t‖ = 1 := by
  rw [unitClock, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (timeDirection_norm_pos t ht), inv_mul_cancel₀ (timeDirection_norm_pos t ht).ne']

theorem clock_scaling (t : ℝ≥0) (ht : 0 < t) :
    (fun ω => ‖timeDirection t‖ * firstChaosEmbedding (unitClock t) ω) =ᵐ[gaussianProduct]
      GaussianTimeProcess.process t := by
  have hscale : ‖timeDirection t‖ • firstChaosEmbedding (unitClock t) =
      GaussianTimeProcess.wienerL2 t := by
    rw [← map_smul, unitClock, smul_smul,
      mul_inv_cancel₀ (timeDirection_norm_pos t ht).ne', one_smul]
    rfl
  have hs := Lp.coeFn_smul ‖timeDirection t‖ (firstChaosEmbedding (unitClock t))
  rw [hscale] at hs
  exact hs.symm

/-- Equality of the actual original Bochner classes, with the clock/scenery
factor order and normalized clock observation explicitly identified. -/
theorem point_pullback (t : ℝ≥0) (ht : 0 < t) :
    fieldPullback (unitClock t) (unitClock_norm t ht)
      (IBMClockWeakGraphObstruction.sectionClass ‖timeDirection t‖) =
        IBMRandomTimeHilbert.randomSourceL2 t := by
  apply Lp.ext
  have hmp := observation_measurePreserving (unitClock t) (unitClock_norm t ht)
  have hc := hmp.quasiMeasurePreserving.ae_eq_comp
      (IBMClockWeakGraphObstruction.sectionClass_ae ‖timeDirection t‖)
  filter_upwards [fieldPullback_ae (unitClock t) (unitClock_norm t ht)
      (IBMClockWeakGraphObstruction.sectionClass ‖timeDirection t‖), hc,
    (IBMRandomTimeHilbert.randomSourceClass_memLp t).coeFn_toLp, clock_scaling t ht]
    with ω hp hc hu hs
  dsimp only [Function.comp_def] at hc
  change IBMRandomTimeHilbert.randomSourceL2 t ω = IBMRandomTimeHilbert.randomSourceClass t ω at hu
  rw [hp, hc, hu]
  rw [hs]
  rfl

theorem actual_point_not_partial_clock (t : ℝ≥0) (ht : 0 < t) :
    ProductL2Curry.flip gaussianProduct gaussianProduct (IBMRandomTimeHilbert.randomSourceL2 t) ∉
      (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).domain := by
  rw [← point_pullback t ht]
  exact positive_section_not_clock_domain (unitClock t) (unitClock_norm t ht)
    ‖timeDirection t‖ (timeDirection_norm_pos t ht)

theorem actual_point_not_clockDomain (t : ℝ≥0) (ht : 0 < t) :
    jointRealization (IBMRandomTimeHilbert.randomSourceL2 t) ∉ IBMFiniteAverageCore.clockDomain := by
  change ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
    (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t)) ∉
      (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).domain
  exact actual_point_not_partial_clock t ht

theorem actual_point_in_sourceDomain (t : ℝ≥0) :
    jointRealization (IBMRandomTimeHilbert.randomSourceL2 t) ∈ IBMFiniteAverageCore.sourceDomain := by
  change ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
    (ProductL2Curry.swap gaussianProduct gaussianProduct
      (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t))) ∈
        (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).domain
  have hs : ProductL2Curry.swap gaussianProduct gaussianProduct
      (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t)) =
        (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
          (IBMRandomTimeHilbert.randomSourceL2 t) :=
    IBMNonlinearAverageGraph.swap_swap _
  rw [hs, LinearIsometryEquiv.apply_symm_apply]
  exact IBMUnmollifiedSourceDerivative.randomSource_domain t

theorem actual_point_not_joint_domain (t : ℝ≥0) (ht : 0 < t) :
    intrinsicCurve t ∉ IBMJointIntrinsicDerivative.jointDerivative.domain := by
  intro hf
  have hc := (IBMJointIntrinsicDerivative.joint_domain_iff _).mp hf
  have hm := (IBMFiniteAverageCore.mem_intrinsicCore_iff _).mp hc
  exact actual_point_not_clockDomain t ht hm.2.1

/-- The existing mollified clock gradients cannot have a strong L² limit.
Value convergence alone cannot pass these actual clock graphs to the point. -/
theorem mollified_clock_gradients_no_limit (t : ℝ≥0) (ht : 0 < t)
    (V : Lp GaussianVectorL2 2 gaussianProduct) :
    ¬ Tendsto (fun n => IBMFirstSourceClockGraph.clockGradient n t) atTop (𝓝 V) := by
  intro hV
  have hu := (ProductL2Curry.flip gaussianProduct gaussianProduct).continuous.tendsto
    (IBMRandomTimeHilbert.randomSourceL2 t) |>.comp (IBMRandomTimeHilbert.randomMollifiedL2_tendsto t)
  have hm := (BochnerClosedOperator.lift_isClosed gaussianProduct closedCylindricalDerivative
    closedCylindricalDerivative_isClosed).mem_of_tendsto (hu.prodMk_nhds hV)
    (Eventually.of_forall (fun n => IBMFirstSourceClockGraph.mollified_clock_graph n t ht))
  exact actual_point_not_partial_clock t ht (LinearPMap.mem_domain_of_mem_graph hm)

end OperatorDerivativeRewrite.Foundation.IBMPointClockDomainObstruction
