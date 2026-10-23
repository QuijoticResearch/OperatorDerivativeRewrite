import Foundation.IBMTimeWeightedSineClock

/-! Actual joint intrinsic derivatives and divergence IBP for EVERY rough L2
deterministic time weight. Source integrals are exact; native clock convergence
is asserted only in the proved weak-pairing topology here. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTimeWeightedSineCalculus
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMActualSineDomainObstruction IBMClockOverlapEnergy IBMTimeWeightedSineValue
open IBMTimeWeightedSineClock
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem source_integrable (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    Integrable (fun t => g t • sineSourceGradient t.toNNReal) (window T) := by
  obtain ⟨C,_,hb⟩ := IBMSineAverageSourceDomain.sourceGradient_bounded T
  apply ((hg.integrable (by norm_num)).norm.mul_const C).mono'
    (hg.aestronglyMeasurable.smul
      IBMSineAverageStrongJoint.sourceGradient_continuous.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  change ‖g t • sineSourceGradient t.toNNReal‖ ≤ ‖g t‖*C
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (hb t.toNNReal ⟨by positivity,Real.toNNReal_le_iff_le_coe.mpr ht.2⟩) (norm_nonneg _)

def nativeSource (g : ℝ → ℝ) (T : ℝ≥0) : FieldSpace :=
  ∫ t, g t • sineSourceGradient t.toNNReal ∂window T

theorem actual_source_graph (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    (sourceUnitary (actual g T : JointL2),nativeSource g T) ∈
      IBMClockGraphDualLimit.Clock.graph := by
  let u : ℝ → ScalarFieldSpace := fun t => sourceUnitary (g t • (sinePoint t.toNNReal : JointL2))
  let v : ℝ → FieldSpace := fun t => g t • sineSourceGradient t.toNNReal
  have hu : Integrable u (window T) :=
    sourceUnitary.toLinearIsometry.toContinuousLinearMap.integrable_comp (joint_integrable g T hg)
  have hv : Integrable v (window T) := source_integrable g T hg
  have ha : ∀ᵐ t ∂window T, (u t,v t) ∈ IBMClockGraphDualLimit.Clock.graph := by
    exact ae_of_all _ fun t => by
      change (sourceUnitary (g t • (sinePoint t.toNNReal : JointL2)),
        g t • sineSourceGradient t.toNNReal) ∈ IBMClockGraphDualLimit.Clock.graph
      rw [map_smul]
      exact IBMClockGraphDualLimit.Clock.graph.smul_mem (g t) (sinePoint_source_graph _)
  have hm := IBMNonlinearClockAverageGraph.integral_clock_graph u v hu hv ha
  have hU : (∫ t, u t ∂window T) = sourceUnitary (actual g T : JointL2) := by
    exact (sourceUnitary.toLinearIsometry.toContinuousLinearMap.integral_comp_comm
      (joint_integrable g T hg)).trans (congrArg sourceUnitary (actual_coe g T hg).symm)
  have he : (∫ t, u t ∂window T,∫ t, v t ∂window T) =
      (sourceUnitary (actual g T : JointL2),nativeSource g T) := Prod.ext hU rfl
  exact he ▸ hm

theorem actual_joint_domain (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    actual g T ∈ jointDerivative.domain := by
  apply (joint_domain_iff _).mpr
  apply (IBMFiniteAverageCore.mem_intrinsicCore_iff _).mpr
  exact ⟨(actual g T).property,actual_clock_domain g T hg,
    LinearPMap.mem_domain_of_mem_graph (actual_source_graph g T hg)⟩

def domainValue (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) : jointDerivative.domain :=
  ⟨actual g T,actual_joint_domain g T hg⟩

def gradient (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) : JointFieldSpace :=
  jointDerivative (domainValue g T hg)

theorem gradient_represents (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    IBMIntrinsicGraphDual.embed (gradient g T hg) =
      IBMIntrinsicGraphDual.weakDerivative (actual g T) :=
  IBMIntrinsicGraphDual.original_graph (domainValue g T hg)

theorem gradient_congr_ae (g k : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T))
    (hk : MemLp k 2 (window T)) (he : g =ᵐ[window T] k) : gradient g T hg = gradient k T hk := by
  have hv : domainValue g T hg = domainValue k T hk :=
    Subtype.ext (actual_congr_ae g k T he)
  exact congrArg jointDerivative hv

theorem source_formula (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    gradient g T hg 0 = nativeSource g T :=
  IBMClockGraphDualLimit.Clock.mem_graph_snd_inj
    (IBMIntrinsicChainRule.source_partial_graph (domainValue g T hg))
    (actual_source_graph g T hg) rfl

theorem clock_graph (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T)) :
    (clockUnitary (actual g T : JointL2),gradient g T hg 1) ∈ IBMClockGraphDualLimit.Clock.graph :=
  IBMIntrinsicChainRule.clock_partial_graph (domainValue g T hg)

attribute [local irreducible] gradient domainValue actual
  IBMIntrinsicGraphDual.embed IBMIntrinsicGraphDual.weakDerivative

theorem actual_integration_by_parts (g : ℝ → ℝ) (T : ℝ≥0) (hg : MemLp g 2 (window T))
    (v : jointDivergence.domain) :
    inner ℝ (gradient g T hg) (v : JointFieldSpace) =
      ∫ p, (∫ t, g t * Real.sin (IBMConstructedSources.ibmValue t.toNNReal p) ∂window T) *
        ((jointDivergence v : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure := by
  have h := congrArg (fun L : StrongDual ℝ IBMIntrinsicGraphDual.Tests =>
    L (IBMIntrinsicGraphDual.testOf v)) (gradient_represents g T hg)
  have he : IBMIntrinsicGraphDual.embed (gradient g T hg) (IBMIntrinsicGraphDual.testOf v) =
      inner ℝ (gradient g T hg) (v : JointFieldSpace) := by
    unfold IBMIntrinsicGraphDual.embed IBMIntrinsicGraphDual.testOf
    rfl
  exact he.symm.trans
    (h.trans (IBMIntrinsicGraphDual.actual_pairing (actual g T) _ (actual_actual_ae g T hg) v))

theorem actual_adjoint_product_integrable (g : ℝ → ℝ) (T : ℝ≥0)
    (hg : MemLp g 2 (window T)) (v : jointDivergence.domain) :
    Integrable (fun p =>
      (∫ t, g t * Real.sin (IBMConstructedSources.ibmValue t.toNNReal p) ∂window T) *
        ((jointDivergence v : IntrinsicSpace) : JointL2) p) IBMSourceLaws.jointMeasure :=
  IBMIntrinsicGraphDual.actual_pairing_integrable (actual g T) _ (actual_actual_ae g T hg) v

theorem native_clock_pairing_tendsto (g : ℝ → ℝ) (T : ℝ≥0)
    (hg : MemLp g 2 (window T)) (w : FieldSpace) :
    Tendsto (fun n => inner ℝ (nativeGradient n g T) w) atTop
      (𝓝 (inner ℝ (gradient g T hg 1) w)) :=
  ClosedOperatorWeakGraphLimit.pairing_tendsto IBMClockGraphDualLimit.Clock
    IBMClockGraphDualLimit.clock_closed IBMClockGraphDualLimit.clock_dense
    (fun n => mollified_clock_graph n g T hg)
    (clock_graph g T hg)
    (clockUnitary.continuous.continuousAt.tendsto.comp (mollified_tendsto g T hg))
    (Real.sqrt (energy g T)) (Real.sqrt_nonneg _) (fun n => native_norm_bound n g T hg) w

end OperatorDerivativeRewrite.Foundation.IBMTimeWeightedSineCalculus
