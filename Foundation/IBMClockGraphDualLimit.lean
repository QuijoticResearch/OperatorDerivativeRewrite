import Foundation.ClosedOperatorGraphDualDerivative
import Foundation.IBMPointClockDomainObstruction

/-! Actual IBM clock gradients: their L² norms escape to infinity, while their
canonical embeddings converge strongly in the dual of the full adjoint graph.
The limiting functional has the actual IBM stochastic pairing on EVERY test. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockGraphDualLimit
open InfiniteGaussian IBMTimeAveragedObservable IBMPointClockDomainObstruction
open ClosedOperatorGraphDualDerivative
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable

abbrev Clock := IBMFiniteAverageCore.partialDerivative

theorem clock_closed : Clock.IsClosed :=
  BochnerClosedOperator.lift_isClosed gaussianProduct closedCylindricalDerivative
    closedCylindricalDerivative_isClosed

theorem clock_dense : Dense (Clock.domain : Set (Lp GaussianL2 2 gaussianProduct)) :=
  BochnerClosedOperator.lift_dense_domain gaussianProduct closedCylindricalDerivative
    closedCylindricalDerivative_dense_domain

def point (t : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  ProductL2Curry.flip gaussianProduct gaussianProduct (IBMRandomTimeHilbert.randomSourceL2 t)

def pointDerivative (t : ℝ≥0) : StrongDual ℝ (Tests Clock clock_dense) :=
  derivative Clock clock_dense (point t)

theorem clock_gradient_norm_escape (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun n => ‖IBMFirstSourceClockGraph.clockGradient n t‖) atTop atTop := by
  apply ClosedOperatorEscapeEnergy.output_norm_tendsto_atTop Clock clock_closed clock_dense
    (fun n => IBMFirstSourceClockGraph.mollified_clock_graph n t ht) _
    (actual_point_not_partial_clock t ht)
  exact (ProductL2Curry.flip gaussianProduct gaussianProduct).continuous.tendsto
    (IBMRandomTimeHilbert.randomSourceL2 t) |>.comp (IBMRandomTimeHilbert.randomMollifiedL2_tendsto t)

theorem clock_gradient_dual_limit (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun n => embed Clock clock_dense (IBMFirstSourceClockGraph.clockGradient n t))
      atTop (𝓝 (pointDerivative t)) := by
  apply graph_limit Clock clock_dense
    (fun n => IBMFirstSourceClockGraph.mollified_clock_graph n t ht)
  exact (ProductL2Curry.flip gaussianProduct gaussianProduct).continuous.tendsto
    (IBMRandomTimeHilbert.randomSourceL2 t) |>.comp (IBMRandomTimeHilbert.randomMollifiedL2_tendsto t)

theorem clock_gradient_dual_error (n : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    ‖embed Clock clock_dense (IBMFirstSourceClockGraph.clockGradient n t) - pointDerivative t‖ ≤
      ‖IBMRandomTimeHilbert.randomMollifiedL2 n t - IBMRandomTimeHilbert.randomSourceL2 t‖ := by
  have he := graph_error_bound Clock clock_dense
    (IBMFirstSourceClockGraph.mollified_clock_graph n t ht) (point t)
  change ‖embed Clock clock_dense (IBMFirstSourceClockGraph.clockGradient n t) - pointDerivative t‖ ≤
    ‖ProductL2Curry.flip gaussianProduct gaussianProduct (IBMRandomTimeHilbert.randomMollifiedL2 n t) -
      ProductL2Curry.flip gaussianProduct gaussianProduct (IBMRandomTimeHilbert.randomSourceL2 t)‖ at he
  simpa only [← map_sub,
    (ProductL2Curry.flip gaussianProduct gaussianProduct).norm_map] using he

theorem clock_gradient_dual_radius (n : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    ‖embed Clock clock_dense (IBMFirstSourceClockGraph.clockGradient n t) - pointDerivative t‖ ≤
      Real.sqrt (IBMMollifier.bump n).rOut :=
  (clock_gradient_dual_error n t ht).trans (IBMRandomTimeHilbert.randomMollifiedL2_error_le n t)

theorem pointDerivative_not_L2 (t : ℝ≥0) (ht : 0 < t) :
    ¬ ∃ V : Lp GaussianVectorL2 2 gaussianProduct, embed Clock clock_dense V = pointDerivative t := by
  intro h
  exact actual_point_not_partial_clock t ht
    ((representable_iff_domain Clock clock_closed clock_dense (point t)).mp h)

theorem pointDerivative_apply_test (t : ℝ≥0) (v : Clock.adjoint.domain) :
    pointDerivative t (testOf Clock clock_dense v) = inner ℝ (point t) (Clock.adjoint v) := rfl

/-- The weak derivative is paired with the ACTUAL constructed IBM value under
its original joint Gaussian probability law; no independent symbolic process. -/
theorem actual_stochastic_pairing (t : ℝ≥0) (v : Clock.adjoint.domain) :
    pointDerivative t (testOf Clock clock_dense v) =
      ∫ ω, IBMConstructedSources.ibmValue t ω *
        (IBMIntrinsicOperators.clockUnitary.symm (Clock.adjoint v)) ω
        ∂IBMSourceLaws.jointMeasure := by
  rw [pointDerivative_apply_test]
  have hi := IBMIntrinsicOperators.clockUnitary.inner_map_map
    (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t))
    (IBMIntrinsicOperators.clockUnitary.symm (Clock.adjoint v))
  rw [IBMIntrinsicOperators.clockUnitary.apply_symm_apply] at hi
  change inner ℝ (point t) (Clock.adjoint v) = _ at hi
  rw [hi, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [joint_point_actual_ae t] with ω hω
  rw [hω, Real.inner_apply]

theorem actual_pairing_integrable (t : ℝ≥0) (v : Clock.adjoint.domain) :
    Integrable (fun ω => IBMConstructedSources.ibmValue t ω *
      (IBMIntrinsicOperators.clockUnitary.symm (Clock.adjoint v)) ω)
      IBMSourceLaws.jointMeasure := by
  have hi := (Lp.memLp (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t))).integrable_mul
    (Lp.memLp (IBMIntrinsicOperators.clockUnitary.symm (Clock.adjoint v)))
  apply hi.congr
  filter_upwards [joint_point_actual_ae t] with ω hω
  simp only [Pi.mul_apply, hω]

theorem pointDerivative_continuous : Continuous pointDerivative :=
  (derivative Clock clock_dense).continuous.comp
    ((ProductL2Curry.flip gaussianProduct gaussianProduct).continuous.comp source_time_continuous)

theorem pointDerivative_ne_zero (t : ℝ≥0) (ht : 0 < t) : pointDerivative t ≠ 0 := by
  exact derivative_ne_zero_of_not_domain Clock clock_closed clock_dense
    (actual_point_not_partial_clock t ht)

end OperatorDerivativeRewrite.Foundation.IBMClockGraphDualLimit
