import Foundation.IBMNonlinearClockAverageGraph
import Foundation.IBMSineAverageSimpson

/-! Clock-domain membership of the ACTUAL nonlinear IBM time average.
This is int sin(Zt) dt, not sin(int Zt dt). No strong convergence of the
mollified derivative fields or joint intrinsic-domain assertion is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineAverageClockDomain
open InfiniteGaussian IBMTimeAveragedObservable IBMClockOverlapEnergy
open IBMIntrinsicOperators IBMNonlinearClockAverageGraph
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def point (t : ℝ) : JointL2 :=
  IBMClockWeakChain.value IBMActualSineDomainObstruction.sineTest
    (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t.toNNReal))

theorem point_continuous : Continuous point :=
  (IBMClockWeakChain.value_L2_lipschitz IBMActualSineDomainObstruction.sineTest).continuous.comp
    (jointRealization.continuous.comp (source_time_continuous.comp continuous_real_toNNReal))

theorem point_integrable (T : ℝ) : Integrable point (window T) :=
  point_continuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem point_actual_ae (t : ℝ) : point t =ᵐ[IBMSourceLaws.jointMeasure]
    fun p => Real.sin (IBMConstructedSources.ibmValue t.toNNReal p) := by
  filter_upwards [IBMClockWeakChain.value_ae IBMActualSineDomainObstruction.sineTest
    (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t.toNNReal)),
    joint_point_actual_ae t.toNNReal] with p hs hi
  change point t p = _ at hs
  rw [hs, hi]
  rfl

def limitAverage (T : ℝ) : JointL2 := ∫ t, point t ∂window T

theorem average_error (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖IBMNonlinearClockAverageGraph.average n T - limitAverage T‖ ≤
      T * Real.sqrt (IBMMollifier.bump n).rOut := by
  rw [IBMNonlinearClockAverageGraph.average, limitAverage,
    ← integral_sub (sineValue_integrable n T) (point_integrable T)]
  have hb (t : ℝ) : ‖sineValue n t - point t‖ ≤ Real.sqrt (IBMMollifier.bump n).rOut := by
    have h := IBMClockWeakChain.value_error IBMActualSineDomainObstruction.sineTest
      (IBMNonlinearClockGraph.input n t.toNNReal)
      (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t.toNNReal))
    have he : ‖IBMNonlinearClockGraph.input n t.toNNReal -
        jointRealization (IBMRandomTimeHilbert.randomSourceL2 t.toNNReal)‖ =
        ‖IBMRandomTimeHilbert.randomMollifiedL2 n t.toNNReal -
          IBMRandomTimeHilbert.randomSourceL2 t.toNNReal‖ := by
      change ‖jointRealization (IBMRandomTimeHilbert.randomMollifiedL2 n t.toNNReal) -
        jointRealization (IBMRandomTimeHilbert.randomSourceL2 t.toNNReal)‖ = _
      rw [← map_sub, jointRealization.norm_map]
    rw [he] at h
    exact h.trans (by simpa only [IBMActualSineDomainObstruction.sineTest, one_mul] using
      IBMRandomTimeHilbert.randomMollifiedL2_error_le n t.toNNReal)
  have h := norm_integral_le_of_norm_le_const (ae_of_all (window T) hb)
  simpa [window, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hT, mul_comm] using h

theorem average_tendsto {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => IBMNonlinearClockAverageGraph.average n T) atTop (𝓝 (limitAverage T)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr : Tendsto (fun n : ℕ => T * Real.sqrt (IBMMollifier.bump n).rOut) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp IBMMollifier.bump_outer_tendsto_zero).const_mul T
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => average_error n hT) hr

attribute [local irreducible] point IBMConstructedSources.ibmValue

theorem integrand_measurable : Measurable (fun p : ℝ × IBMSourceLaws.JointSample =>
    Real.sin (IBMConstructedSources.ibmValue p.1.toNNReal p.2)) := by
  have hm : Measurable (fun p : ℝ × IBMSourceLaws.JointSample => (p.1.toNNReal, p.2)) :=
    (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
  exact Real.continuous_sin.measurable.comp
    (IBMConstructedSources.ibmValue_jointly_measurable.comp hm)

theorem limitAverage_actual_ae (T : ℝ) : limitAverage T =ᵐ[IBMSourceLaws.jointMeasure]
    fun p => ∫ t, Real.sin (IBMConstructedSources.ibmValue t.toNNReal p) ∂window T := by
  apply BochnerL2RepresentativeFubini.integral_coeFn_ae point (point_integrable T)
    (fun p : ℝ × IBMSourceLaws.JointSample =>
      Real.sin (IBMConstructedSources.ibmValue p.1.toNNReal p.2))
  · exact integrand_measurable.aestronglyMeasurable
  · exact ae_of_all _ point_actual_ae

theorem limitAverage_eq_actual (T : ℝ≥0) :
    limitAverage T = (IBMSineAverageSimpson.average T : JointL2) := by
  apply Lp.ext
  filter_upwards [limitAverage_actual_ae T, IBMSineAverageSimpson.average_actual_ae T] with p hl ha
  rw [hl, ha]
  exact (intervalIntegral.integral_of_le T.property).symm

theorem actual_average_clock_domain (T : ℝ≥0) :
    clockUnitary (IBMSineAverageSimpson.average T : JointL2) ∈ IBMClockGraphDualLimit.Clock.domain := by
  rw [← limitAverage_eq_actual]
  apply ClosedOperatorEscapeEnergy.mem_domain_of_frequently_bounded_graph
    IBMClockGraphDualLimit.Clock IBMClockGraphDualLimit.clock_closed IBMClockGraphDualLimit.clock_dense
    (fun n => average_clock_graph n T.property)
    (clockUnitary.continuous.continuousAt.tendsto.comp (average_tendsto T.property))
    (Real.sqrt (8 * IBMFoldedTransitionBound.peak 1 * (T : ℝ) ^ 2 * Real.sqrt T + 4 * (T : ℝ) ^ 3))
  exact (Eventually.of_forall fun n => averageGradient_norm_bound n T.property).frequently

theorem actual_average_in_clockDomain (T : ℝ≥0) :
    (IBMSineAverageSimpson.average T : JointL2) ∈ IBMFiniteAverageCore.clockDomain :=
  actual_average_clock_domain T

end OperatorDerivativeRewrite.Foundation.IBMSineAverageClockDomain
