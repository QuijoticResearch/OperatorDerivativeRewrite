import Foundation.IBMSineClockSectionObstruction
import Foundation.IBMClockWeakChain
import Foundation.IBMIntrinsicGraphDual
import Foundation.IBMPastEndpointCore
import Foundation.IBMIntrinsicPoincare

/-! A concrete bounded smooth function of ACTUAL IBM is outside the ORIGINAL
clock and joint domains at every positive time, but remains scenery-Sobolev. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMActualSineDomainObstruction
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMPointClockDomainObstruction IBMClockBochnerConverse IBMNonlinearFirstSource
open IBMSineClockSectionObstruction IBMJointIntrinsicDerivative
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def sineTest : IBMClockWeakChain.TestFunction where
  value := Real.sin
  slope := Real.cos
  valueBound := 1
  slopeBound := 1
  hasDeriv := Real.hasDerivAt_sin
  continuous_slope := Real.continuous_cos
  value_le := Real.abs_sin_le_one
  slope_le := Real.abs_cos_le_one

def sinePoint (t : ℝ≥0) : IntrinsicSpace :=
  ⟨IBMClockWeakChain.value sineTest (intrinsicCurve t : JointL2),
    IBMIntrinsicChainRule.composition_observable (intrinsicCurve t) _ Real.sin
      Real.continuous_sin (IBMClockWeakChain.value_ae sineTest _)⟩

theorem sinePoint_actual_ae (t : ℝ≥0) :
    (sinePoint t : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => Real.sin (IBMConstructedSources.ibmValue t ω) := by
  filter_upwards [IBMClockWeakChain.value_ae sineTest (intrinsicCurve t : JointL2),
    joint_point_actual_ae t] with ω hv hx
  exact hv.trans (congrArg Real.sin hx)

theorem sinePoint_memLp_top (t : ℝ≥0) :
    MemLp ((sinePoint t : JointL2) : IBMSourceLaws.JointSample → ℝ) ∞
      IBMSourceLaws.jointMeasure := by
  apply MemLp.of_bound (Lp.aestronglyMeasurable _) 1
  filter_upwards [sinePoint_actual_ae t] with ω hx
  rw [hx]
  exact Real.abs_sin_le_one _

theorem sinePoint_zero : sinePoint 0 = 0 := by
  apply Subtype.ext
  apply Lp.ext
  have hz : (intrinsicCurve 0 : JointL2) = 0 := by
    change jointRealization (IBMRandomTimeHilbert.randomSourceL2 0) = 0
    rw [IBMPastEndpointCore.randomSource_zero, map_zero]
  filter_upwards [IBMClockWeakChain.value_ae sineTest (intrinsicCurve 0 : JointL2),
    Lp.coeFn_zero ℝ 2 IBMSourceLaws.jointMeasure] with ω hv h0
  have hx : (intrinsicCurve 0 : JointL2) ω = 0 := by rw [hz]; exact h0
  change IBMClockWeakChain.value sineTest (intrinsicCurve 0 : JointL2) ω = _
  calc
    _ = Real.sin ((intrinsicCurve 0 : JointL2) ω) := hv
    _ = 0 := by rw [hx, Real.sin_zero]
    _ = _ := h0.symm

theorem sinePoint_continuous : Continuous sinePoint :=
  ((IBMClockWeakChain.value_L2_lipschitz sineTest).continuous.comp
    (IntrinsicSpace.subtypeL.continuous.comp intrinsicCurve_continuous)).subtype_mk _

theorem pullback_actual_ae (t : ℝ≥0) (ht : 0 < t) :
    jointRealization (fieldPullback (unitClock t) (unitClock_norm t ht)
      (sectionClass ‖IBMClockLinearDivergence.timeDirection t‖))
      =ᵐ[IBMSourceLaws.jointMeasure] fun ω => Real.sin (IBMConstructedSources.ibmValue t ω) := by
  apply jointRealization_ae_of_sections _ _
    (Real.continuous_sin.measurable.comp
      (IBMConstructedSources.ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)))
  have hm := IBMClockObservationGraph.observation_measurePreserving (unitClock t) (unitClock_norm t ht)
  have hc := hm.quasiMeasurePreserving.ae_eq_comp
    (sectionClass_ae ‖IBMClockLinearDivergence.timeDirection t‖)
  filter_upwards [fieldPullback_ae (unitClock t) (unitClock_norm t ht)
    (sectionClass ‖IBMClockLinearDivergence.timeDirection t‖), hc,
    clock_scaling t ht, IBMUnmollifiedSourceDerivative.actual_section_ae t]
    with ωY hp hs hc ha
  dsimp only [Function.comp_def] at hs
  rw [hp, hs]
  change scenerySine |‖IBMClockLinearDivergence.timeDirection t‖ *
    firstChaosEmbedding (unitClock t) ωY| =ᵐ[gaussianProduct] _
  rw [hc]
  filter_upwards [scenerySine_ae |GaussianTimeProcess.process t ωY|, ha] with ωX hsin hx
  exact hsin.trans (congrArg Real.sin hx.symm)

theorem sinePoint_pullback (t : ℝ≥0) (ht : 0 < t) :
    jointRealization (fieldPullback (unitClock t) (unitClock_norm t ht)
      (sectionClass ‖IBMClockLinearDivergence.timeDirection t‖)) = (sinePoint t : JointL2) :=
  Lp.ext ((pullback_actual_ae t ht).trans (sinePoint_actual_ae t).symm)

theorem sinePoint_not_clockDomain (t : ℝ≥0) (ht : 0 < t) :
    (sinePoint t : JointL2) ∉ IBMFiniteAverageCore.clockDomain := by
  rw [← sinePoint_pullback t ht]
  change ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
    (jointRealization (fieldPullback (unitClock t) (unitClock_norm t ht)
      (sectionClass ‖IBMClockLinearDivergence.timeDirection t‖))) ∉
        (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).domain
  exact section_not_native_clock_domain (unitClock t) (unitClock_norm t ht)
    ‖IBMClockLinearDivergence.timeDirection t‖ (timeDirection_norm_pos t ht)

theorem sinePoint_not_joint_domain (t : ℝ≥0) (ht : 0 < t) :
    sinePoint t ∉ jointDerivative.domain := by
  intro hd
  have h := (IBMFiniteAverageCore.mem_intrinsicCore_iff _).mp ((joint_domain_iff _).mp hd)
  exact sinePoint_not_clockDomain t ht h.2.1

def sineSourceGradient (t : ℝ≥0) : FieldSpace :=
  IBMClockWeakChain.chainField sineTest
    (ProductL2Curry.swap gaussianProduct gaussianProduct (intrinsicCurve t : JointL2))
    (IBMUnmollifiedSourceDerivative.gradient t)

theorem sinePoint_source_graph (t : ℝ≥0) :
    (sourceUnitary (sinePoint t : JointL2), sineSourceGradient t) ∈
      IBMFiniteAverageCore.partialDerivative.graph := by
  let q : JointL2 := (intrinsicCurve t : JointL2)
  have hq : ProductL2Curry.swap gaussianProduct gaussianProduct q =
      clockUnitary.symm (IBMRandomTimeHilbert.randomSourceL2 t) :=
    IBMNonlinearAverageGraph.swap_swap _
  have hg : (clockUnitary (ProductL2Curry.swap gaussianProduct gaussianProduct q),
      IBMUnmollifiedSourceDerivative.gradient t) ∈ IBMFiniteAverageCore.partialDerivative.graph := by
    rw [hq, clockUnitary.apply_symm_apply]
    exact IBMUnmollifiedSourceDerivative.randomSource_graph t
  have hc := IBMClockWeakChain.chain_graph sineTest
    (ProductL2Curry.swap gaussianProduct gaussianProduct q)
    (IBMUnmollifiedSourceDerivative.gradient t) hg
  have he := IBMIntrinsicChainRule.swap_composition_eq q (sinePoint t : JointL2)
    (IBMClockWeakChain.value sineTest (ProductL2Curry.swap gaussianProduct gaussianProduct q))
    Real.sin (IBMClockWeakChain.value_ae sineTest q) (IBMClockWeakChain.value_ae sineTest _)
  change (clockUnitary (ProductL2Curry.swap gaussianProduct gaussianProduct (sinePoint t : JointL2)),
    sineSourceGradient t) ∈ IBMFiniteAverageCore.partialDerivative.graph
  rw [he]
  exact hc

theorem sinePoint_sourceDomain (t : ℝ≥0) :
    (sinePoint t : JointL2) ∈ IBMFiniteAverageCore.sourceDomain :=
  LinearPMap.mem_domain_of_mem_graph (sinePoint_source_graph t)

def sineDerivative (t : ℝ≥0) : StrongDual ℝ IBMIntrinsicGraphDual.Tests :=
  IBMIntrinsicGraphDual.weakDerivative (sinePoint t)

theorem sineDerivative_continuous : Continuous sineDerivative :=
  IBMIntrinsicGraphDual.weakDerivative.continuous.comp sinePoint_continuous

attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative

theorem sinePoint_not_constant (t : ℝ≥0) (ht : 0 < t) (a : ℝ) :
    sinePoint t ≠ a • IBMCenteredSourceRepresentation.intrinsicOne := by
  intro he
  apply sinePoint_not_joint_domain t ht
  rw [he]
  exact jointDerivative.domain.smul_mem a IBMIntrinsicPoincare.oneElement.property

theorem sineDerivative_not_representable (t : ℝ≥0) (ht : 0 < t) :
    ¬ ∃ V : JointFieldSpace, IBMIntrinsicGraphDual.embed V = sineDerivative t := by
  intro h
  exact sinePoint_not_joint_domain t ht ((IBMIntrinsicGraphDual.representable_iff_domain _).mp h)

theorem sineDerivative_ne_zero (t : ℝ≥0) (ht : 0 < t) : sineDerivative t ≠ 0 :=
  ClosedOperatorGraphDualDerivative.derivative_ne_zero_of_not_domain jointDerivative
    jointDerivative_closed jointDerivative_dense (sinePoint_not_joint_domain t ht)

theorem sine_graph_norm_escape (t : ℝ≥0) (ht : 0 < t)
    (u : ℕ → jointDerivative.domain)
    (hu : Tendsto (fun n => (u n : IntrinsicSpace)) atTop (𝓝 (sinePoint t))) :
    Tendsto (fun n => ‖jointDerivative (u n)‖) atTop atTop :=
  ClosedOperatorEscapeEnergy.output_norm_tendsto_atTop jointDerivative jointDerivative_closed
    jointDerivative_dense (fun n => jointDerivative.mem_graph (u n)) hu
      (sinePoint_not_joint_domain t ht)

theorem observable_sine_graph_approximation (t : ℝ≥0) (ht : 0 < t) :
    ∃ u : ℕ → jointDerivative.domain,
      Tendsto (fun n => (u n : IntrinsicSpace)) atTop (𝓝 (sinePoint t)) ∧
      Tendsto (fun n => IBMIntrinsicGraphDual.embed (jointDerivative (u n))) atTop
        (𝓝 (sineDerivative t)) ∧
      Tendsto (fun n => ‖jointDerivative (u n)‖) atTop atTop := by
  exact (IBMIntrinsicGraphDual.domain_approximation (sinePoint t)).imp fun u hu =>
    ⟨hu, IBMIntrinsicGraphDual.graph_dual_limit (sinePoint t) u hu, sine_graph_norm_escape t ht u hu⟩

theorem sineDerivative_actual_pairing (t : ℝ≥0) (v : jointDivergence.domain) :
    sineDerivative t (IBMIntrinsicGraphDual.testOf v) =
      ∫ ω, Real.sin (IBMConstructedSources.ibmValue t ω) *
        ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂IBMSourceLaws.jointMeasure :=
  IBMIntrinsicGraphDual.actual_pairing (sinePoint t) _ (sinePoint_actual_ae t) v

theorem sineDerivative_actual_integrable (t : ℝ≥0) (v : jointDivergence.domain) :
    Integrable (fun ω => Real.sin (IBMConstructedSources.ibmValue t ω) *
      ((jointDivergence v : IntrinsicSpace) : JointL2) ω) IBMSourceLaws.jointMeasure :=
  IBMIntrinsicGraphDual.actual_pairing_integrable (sinePoint t) _ (sinePoint_actual_ae t) v

end OperatorDerivativeRewrite.Foundation.IBMActualSineDomainObstruction
