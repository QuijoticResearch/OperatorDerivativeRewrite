import Foundation.IBMSchwartzHeatReconstruction
import Foundation.GaussianDivergenceRecovery
import Foundation.BochnerLiftAdjointInclusion
import Foundation.IBMIntrinsicChainRule

/-! Explicit source-chaos recovery of the initial scenery mean combined with
the verified nonlinear native clock heat integral. The centered SUM is an
actual IBM observable; separate channels need not be observed processes. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHybridReconstruction
open InfiniteGaussian IBMTimeAveragedObservable IBMFiniteAverageCore IBMIntrinsicOperators
open IBMJointIntrinsicDerivative IBMSchwartzHeatDerivative IBMSchwartzHeatReconstruction
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] sourceDerivative clockDerivative jointDerivative pairField
  IBMSchwartzHeatPredictable.nativeField IBMSchwartzHeatPredictable.value
  IBMSchwartzHeatPredictable.scalarInput
  jointRealization IBMSchwartzPhysicalPrimitiveClock.endpointLimit

theorem source_curry_const (v : GaussianL2) :
    sourceUnitary (jointRealization (Lp.const 2 gaussianProduct v)) =
      BochnerClosedOperator.tensor gaussianProduct gaussianOne v := by
  unfold jointRealization
  change ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
    (ProductL2Curry.swap gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct
        ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
          (Lp.const 2 gaussianProduct v)))) = _
  have he := IBMNonlinearAverageGraph.swap_swap
    ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm (Lp.const 2 gaussianProduct v))
  refine ((congrArg (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct) he).trans
    (LinearIsometryEquiv.apply_symm_apply _ _)).trans ?_
  apply Lp.ext
  filter_upwards [Lp.coeFn_const 2 gaussianProduct v,
    BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne v,gaussianOne_coeFn]
    with Y hc ht ho
  rw [hc,ht,ho,one_smul]
  rfl

def sourceField (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : FieldSpace :=
  BochnerClosedOperator.tensor gaussianProduct gaussianOne
    (GaussianDivergenceRecovery.recovery (heatMean g a 0 T))

def initialCenter (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : JointL2 :=
  jointRealization (Lp.const 2 gaussianProduct
    (heatMean g a 0 T-GaussianNumberSectors.projection 0 (heatMean g a 0 T)))

theorem source_partial_graph (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    (sourceField g a T,BochnerClosedOperator.tensor gaussianProduct gaussianOne
      (heatMean g a 0 T-GaussianNumberSectors.projection 0 (heatMean g a 0 T))) ∈
        partialDerivative.adjoint.graph := by
  have hg := BochnerClosedOperator.tensor_graph gaussianProduct hilbertDivergence
    gaussianOne _ _ (GaussianDivergenceRecovery.recovery_graph (heatMean g a 0 T))
  exact LinearPMap.le_graph_of_le
    (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct closedCylindricalDerivative
      closedCylindricalDerivative_dense_domain) hg

theorem source_mem (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    sourceField g a T ∈ sourceDerivative.adjoint.domain := by
  rw [source_adjoint_domain]
  exact LinearPMap.mem_domain_of_mem_graph (source_partial_graph g a T)

theorem source_value (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    sourceDerivative.adjoint ⟨sourceField g a T,source_mem g a T⟩ = initialCenter g a T := by
  have hp := LinearPMap.mem_domain_of_mem_graph (source_partial_graph g a T)
  have hv := ((partialDerivative.adjoint.image_iff hp).mpr (source_partial_graph g a T)).symm
  rw [source_adjoint_apply _ (source_mem g a T) hp,hv]
  change sourceUnitary.symm _ = jointRealization (Lp.const 2 gaussianProduct _)
  rw [← source_curry_const,LinearIsometryEquiv.symm_apply_apply]

attribute [local irreducible] sourceField

def terminal (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : JointL2 :=
  jointRealization (IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T)

theorem terminal_actual (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    terminal g a T =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => g (a+IBMConstructedSources.ibmValue T p) := by
  have ht : Measurable (fun p : IBMSourceLaws.JointSample => (T,p)) :=
    measurable_const.prodMk measurable_id
  have hB : Measurable (fun p : IBMSourceLaws.JointSample => IBMConstructedSources.ibmValue T p) := by
    simpa only [Function.comp_def] using IBMConstructedSources.ibmValue_jointly_measurable.comp ht
  have hm : Measurable (fun p : IBMSourceLaws.JointSample =>
      g (a+IBMConstructedSources.ibmValue T p)) :=
    g.continuous.measurable.comp (measurable_const.add hB)
  exact jointRealization_ae_of_sections
    (IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T) _ hm
    (IBMSchwartzPhysicalPrimitiveClock.endpointLimit_actual_sections g a T)

theorem terminal_observable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    terminal g a T ∈ IntrinsicSpace := by
  apply IBMIntrinsicChainRule.composition_observable (intrinsicCurve T) _
    (fun x => g (a+x)) (g.continuous.comp (continuous_const.add continuous_id))
  exact (terminal_actual g a T).trans
    ((joint_point_actual_ae T).symm.fun_comp (fun x => g (a+x)))

def meanValue (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : JointL2 :=
  jointRealization (Lp.const 2 gaussianProduct
    (GaussianNumberSectors.projection 0 (heatMean g a 0 T)))

theorem meanValue_actual (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    meanValue g a T =ᵐ[IBMSourceLaws.jointMeasure]
      fun _ => inner ℝ gaussianOne (heatMean g a 0 T) := by
  unfold meanValue
  apply jointRealization_ae_of_sections
  · exact measurable_const
  · filter_upwards [Lp.coeFn_const 2 gaussianProduct
      (GaussianNumberSectors.projection 0 (heatMean g a 0 T))] with Y hc
    rw [hc]
    simp only [Function.const_apply,GaussianNumberSectors.projection_zero]
    filter_upwards [Lp.coeFn_smul (inner ℝ gaussianOne (heatMean g a 0 T)) gaussianOne,
      gaussianOne_coeFn] with X hs ho
    rw [hs,Pi.smul_apply,ho,smul_eq_mul,mul_one]

theorem meanValue_observable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    meanValue g a T ∈ IntrinsicSpace :=
  aestronglyMeasurable_const.congr (meanValue_actual g a T).symm

def centered (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : IntrinsicSpace :=
  ⟨terminal g a T-meanValue g a T,
    IntrinsicSpace.sub_mem (terminal_observable g a T) (meanValue_observable g a T)⟩

def integrand (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : JointFieldSpace :=
  pairField (sourceField g a T) (IBMSchwartzHeatPredictable.nativeField g a T)

theorem ambient_sum (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    sourceDerivative.adjoint ⟨sourceField g a T,source_mem g a T⟩ +
      IBMSchwartzHeatPredictable.value g a T = (centered g a T : JointL2) := by
  rw [source_value,native_reconstruction]
  have he : Lp.const 2 gaussianProduct
      (heatMean g a 0 T-GaussianNumberSectors.projection 0 (heatMean g a 0 T)) =
      Lp.const 2 gaussianProduct (heatMean g a 0 T) -
        Lp.const 2 gaussianProduct (GaussianNumberSectors.projection 0 (heatMean g a 0 T)) :=
    (Lp.constL 2 gaussianProduct ℝ).map_sub _ _
  change jointRealization (Lp.const 2 gaussianProduct _) + jointRealization _ =
    jointRealization _-jointRealization _
  rw [he,map_sub,map_sub]
  abel

attribute [local irreducible] integrand centered

private theorem clock_mem (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    IBMSchwartzHeatPredictable.nativeField g a T ∈ clockDerivative.adjoint.domain :=
  (native_adjoint_reconstruction g a T).choose

private theorem clock_value (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    clockDerivative.adjoint ⟨IBMSchwartzHeatPredictable.nativeField g a T,clock_mem g a T⟩ =
      IBMSchwartzHeatPredictable.value g a T :=
  (native_adjoint_reconstruction g a T).choose_spec.trans (native_reconstruction g a T).symm

theorem reconstruction (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∃ hi : integrand g a T ∈ jointDivergence.domain,
      jointDivergence ⟨integrand g a T,hi⟩ = centered g a T := by
  unfold integrand
  obtain ⟨hi,hd⟩ := ambient_pair_divergence ⟨sourceField g a T,source_mem g a T⟩
    ⟨IBMSchwartzHeatPredictable.nativeField g a T,clock_mem g a T⟩
  refine ⟨hi,?_⟩
  rw [hd,clock_value,ambient_sum]
  exact IntrinsicSpace.orthogonalProjectionOnto_mem_subspace_eq_self (centered g a T)

theorem terminal_duality (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (F : jointDerivative.domain) :
    inner ℝ (centered g a T) (F : IntrinsicSpace) =
      inner ℝ (integrand g a T) (jointDerivative F) := by
  obtain ⟨hi,hv⟩ := reconstruction g a T
  have h := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense
    ⟨integrand g a T,hi⟩ F
  rw [hv] at h
  exact h

theorem global_mean (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    (∫ p, g (a+IBMConstructedSources.ibmValue T p) ∂IBMSourceLaws.jointMeasure) =
      inner ℝ gaussianOne (heatMean g a 0 T) := by
  let E := IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T
  let A : JointL2 := jointRealization (Lp.const 2 gaussianProduct gaussianOne)
  have hA : A =ᵐ[IBMSourceLaws.jointMeasure] fun _ => (1 : ℝ) := by
    apply jointRealization_ae_of_sections
    · exact measurable_const
    · filter_upwards [Lp.coeFn_const 2 gaussianProduct gaussianOne] with Y hY
      rw [hY]
      simp only [Function.const_apply]
      exact gaussianOne_coeFn
  have hl : inner ℝ A (terminal g a T) =
      ∫ p, terminal g a T p ∂IBMSourceLaws.jointMeasure := by
    rw [L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [hA] with p hp
    rw [hp,Real.inner_apply,one_mul]
  have hr : inner ℝ (Lp.const 2 gaussianProduct gaussianOne) E =
      inner ℝ gaussianOne (∫ Y, E Y ∂gaussianProduct) := by
    rw [L2.inner_def]
    calc
      _ = ∫ Y, inner ℝ gaussianOne (E Y) ∂gaussianProduct := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_const 2 gaussianProduct gaussianOne] with Y hY
        rw [hY]
        rfl
      _ = _ := integral_inner ((Lp.memLp E).integrable (by norm_num)) gaussianOne
  have hi : inner ℝ A (terminal g a T) = inner ℝ (Lp.const 2 gaussianProduct gaussianOne) E :=
    jointRealization.inner_map_map (Lp.const 2 gaussianProduct gaussianOne) E
  rw [hl,hr] at hi
  calc
    _ = ∫ p, terminal g a T p ∂IBMSourceLaws.jointMeasure :=
      integral_congr_ae (terminal_actual g a T).symm
    _ = inner ℝ gaussianOne (∫ Y, E Y ∂gaussianProduct) := hi
    _ = _ := by
      change inner ℝ gaussianOne
        (∫ Y, IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T Y ∂gaussianProduct) = _
      rw [initial_mean]

theorem centered_actual (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    (centered g a T : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] fun p =>
      g (a+IBMConstructedSources.ibmValue T p) -
        ∫ q, g (a+IBMConstructedSources.ibmValue T q) ∂IBMSourceLaws.jointMeasure := by
  unfold centered
  change terminal g a T-meanValue g a T =ᵐ[IBMSourceLaws.jointMeasure] _
  filter_upwards [Lp.coeFn_sub (terminal g a T) (meanValue g a T),
    terminal_actual g a T,meanValue_actual g a T] with p hs ht hm
  rw [hs,Pi.sub_apply,ht,hm,global_mean]

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHybridReconstruction
