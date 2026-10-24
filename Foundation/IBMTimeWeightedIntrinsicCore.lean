import Foundation.IBMTimeWeightedGraphOperator

/-! Actual finite combinations of original IBM sine averages approximate
every rough weighted observable TOGETHER with its full intrinsic derivative. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTimeWeightedIntrinsicCore
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMClockOverlapEnergy IBMTimeWeightedClockOperator IBMTimeWeightedClockDensity
open IBMTimeWeightedSineValue IBMTimeWeightedSineCalculus IBMTimeWeightedGraphOperator
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance (T : ℝ≥0) : FrechetUrysohnSpace (TimeL2 T) := inferInstance
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem actual_one (T : ℝ≥0) : actual (fun _ => (1:ℝ)) T = IBMSineAverageSimpson.average T := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [actual_actual_ae (fun _ => (1:ℝ)) T (memLp_const _),
    IBMSineAverageSimpson.average_actual_ae T] with p ha hb
  rw [ha,hb]
  simp_rw [one_mul]
  exact (intervalIntegral.integral_of_le T.property).symm

theorem value_indicator (T : ℝ≥0) (s : Set ℝ) (hs : MeasurableSet s) :
    valueOperator T (indicatorConstLp 2 hs (measure_ne_top (window T) s) (1:ℝ)) =
      ∫ t in s, IBMActualSineDomainObstruction.sinePoint t.toNNReal ∂window T := by
  change actual _ T = _
  have he : (indicatorConstLp 2 hs (measure_ne_top (window T) s) (1:ℝ) : ℝ → ℝ)
      =ᵐ[window T] s.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  rw [actual_congr_ae _ _ T he]
  unfold actual
  have hi : (fun t => s.indicator (fun _ => (1:ℝ)) t •
      IBMActualSineDomainObstruction.sinePoint t.toNNReal) =
      s.indicator (fun t => IBMActualSineDomainObstruction.sinePoint t.toNNReal) := by
    funext t
    by_cases ht : t ∈ s <;> simp [ht]
  rw [hi,integral_indicator hs]

theorem value_prefix (T : ℝ≥0) (a : ℝ) : valueOperator T
    (indicatorConstLp 2 measurableSet_Iic (measure_ne_top (window T) (Iic a)) (1:ℝ)) =
      IBMSineAverageSimpson.average (min a (T:ℝ)).toNNReal := by
  rw [value_indicator,← actual_one]
  unfold window actual
  simp only [one_smul]
  rw [Measure.restrict_restrict measurableSet_Iic,IBMTimeWeightedClockStrong.prefix_intersection]
  rfl

theorem graph_prefix (T : ℝ≥0) (a : ℝ) : graphOperator T
    (indicatorConstLp 2 measurableSet_Iic (measure_ne_top (window T) (Iic a)) (1:ℝ)) =
      (IBMSineAverageSimpson.average (min a (T:ℝ)).toNNReal,
        IBMSineAverageIntrinsicCalculus.gradient (min a (T:ℝ)).toNNReal) := by
  apply Prod.ext
  · exact value_prefix T a
  · change jointDerivative (domainLinear T _) =
      jointDerivative (IBMSineAverageIntrinsicCalculus.domainAverage _)
    have hd : domainLinear T
        (indicatorConstLp 2 measurableSet_Iic (measure_ne_top (window T) (Iic a)) (1:ℝ)) =
        IBMSineAverageIntrinsicCalculus.domainAverage (min a (T:ℝ)).toNNReal := by
      apply Subtype.ext
      exact value_prefix T a
    exact congrArg jointDerivative hd

theorem univ_prefix_class (T : ℝ≥0) :
    indicatorConstLp 2 MeasurableSet.univ (measure_ne_top (window T) univ) (1:ℝ) =
      indicatorConstLp 2 measurableSet_Iic (measure_ne_top (window T) (Iic (T:ℝ))) (1:ℝ) := by
  apply Lp.ext
  have hu : (indicatorConstLp 2 MeasurableSet.univ
      (measure_ne_top (window T) univ) (1:ℝ) : ℝ → ℝ) =ᵐ[window T]
      univ.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  have hp : (indicatorConstLp 2 measurableSet_Iic
      (measure_ne_top (window T) (Iic (T:ℝ))) (1:ℝ) : ℝ → ℝ) =ᵐ[window T]
      (Iic (T:ℝ)).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  filter_upwards [hu,hp,ae_restrict_mem measurableSet_Ioc] with t hu hp ht
  rw [hu,hp]
  rw [indicator_univ]
  exact (indicator_of_mem (show t ∈ Iic (T:ℝ) from ht.2) (fun _ => (1:ℝ))).symm

def averageGraphSpan (T : ℝ≥0) : Submodule ℝ (IntrinsicSpace × JointFieldSpace) :=
  Submodule.span ℝ {z | ∃ a : ℝ,
    z = (IBMSineAverageSimpson.average (min a (T:ℝ)).toNNReal,
      IBMSineAverageIntrinsicCalculus.gradient (min a (T:ℝ)).toNNReal)}

theorem graph_prefix_span (T : ℝ≥0) (g : TimeL2 T)
    (hg : g ∈ generatingIndicatorSpan (window T) prefixSets) :
    graphOperator T g ∈ averageGraphSpan T := by
  have hle : generatingIndicatorSpan (window T) prefixSets ≤
      (averageGraphSpan T).comap (graphOperator T).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro g ⟨s,hs,hm,rfl⟩
    rcases hs with rfl | ⟨a,rfl⟩
    · change graphOperator T _ ∈ averageGraphSpan T
      rw [univ_prefix_class,graph_prefix]
      exact Submodule.subset_span ⟨(T:ℝ),rfl⟩
    · change graphOperator T _ ∈ averageGraphSpan T
      rw [graph_prefix]
      exact Submodule.subset_span ⟨a,rfl⟩
  exact hle hg

attribute [local irreducible] graphOperator actual gradient domainValue averageGraphSpan
  jointDerivative IBMSineAverageSimpson.average IBMSineAverageIntrinsicCalculus.gradient

theorem finite_average_graph_approximation (T : ℝ≥0) (g : TimeL2 T) :
    ∃ u : ℕ → TimeL2 T,
      (∀ n, graphOperator T (u n) ∈ averageGraphSpan T ∧
        graphOperator T (u n) ∈ jointDerivative.graph) ∧
      Tendsto (fun n => graphOperator T (u n)) atTop (𝓝 (graphOperator T g)) := by
  have hg : g ∈ closure (generatingIndicatorSpan (window T) prefixSets : Set (TimeL2 T)) := by
    change g ∈ (generatingIndicatorSpan (window T) prefixSets).topologicalClosure
    rw [prefix_span_dense]
    trivial
  have hs : ∃ u : ℕ → TimeL2 T,
      (∀ n, u n ∈ generatingIndicatorSpan (window T) prefixSets) ∧
      Tendsto u atTop (𝓝 g) :=
    (mem_closure_iff_seq_limit (X := TimeL2 T)
      (s := (generatingIndicatorSpan (window T) prefixSets : Set (TimeL2 T))) (a := g)).mp hg
  obtain ⟨u,hu,ht⟩ := hs
  exact ⟨u,fun n => ⟨graph_prefix_span T (u n) (hu n),graphOperator_mem T (u n)⟩,
    (graphOperator T).continuous.continuousAt.tendsto.comp ht⟩

theorem actual_graph_in_average_closure (T : ℝ≥0) (g : TimeL2 T) :
    (actual g T,gradient g T (Lp.memLp g)) ∈
      closure (averageGraphSpan T : Set (IntrinsicSpace × JointFieldSpace)) := by
  obtain ⟨u,hu,ht⟩ := finite_average_graph_approximation T g
  have hm : graphOperator T g ∈ closure (averageGraphSpan T : Set (IntrinsicSpace × JointFieldSpace)) :=
    mem_closure_of_tendsto ht (Eventually.of_forall fun n => (hu n).1)
  exact (graphOperator_eq T g) ▸ hm

theorem common_intrinsic_graph_approximation (T : ℝ≥0) (g : TimeL2 T) :
    ∃ f : ℕ → jointDerivative.domain,
      (∀ n, ((f n : IntrinsicSpace),jointDerivative (f n)) ∈ averageGraphSpan T) ∧
      Tendsto (fun n => ((f n : IntrinsicSpace),jointDerivative (f n))) atTop
        (𝓝 (actual g T,gradient g T (Lp.memLp g))) := by
  obtain ⟨u,hu,ht⟩ := finite_average_graph_approximation T g
  have he (n : ℕ) : ((domainLinear T (u n) : IntrinsicSpace),
      jointDerivative (domainLinear T (u n))) = graphOperator T (u n) := by
    unfold graphOperator
    rfl
  refine ⟨fun n => domainLinear T (u n),fun n => ?_,?_⟩
  · exact (he n).symm ▸ (hu n).1
  · simpa only [he,graphOperator_eq] using ht

end OperatorDerivativeRewrite.Foundation.IBMTimeWeightedIntrinsicCore
