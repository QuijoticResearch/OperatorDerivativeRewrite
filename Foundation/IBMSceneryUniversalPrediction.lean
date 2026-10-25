import Foundation.GaussianSingleObservationTotal
import Foundation.IBMJointForecastGerm
import Foundation.IBMGlobalVacuum

/-! Vanishing linear scenery predictions imply strong Gaussian and actual
joint IBM predictions for ALL L2 inputs, without a one-ridge restriction. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSceneryUniversalPrediction
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianVanishingPrediction IBMSceneryGaussianGerm

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

variable (δ : ℕ → ℝ≥0)

def linearConvergenceSpace : Submodule ℝ CoefficientSpace where
  carrier := {u | Tendsto (fun n => sourceProjection (history (δ n)) u) atTop (𝓝 0)}
  zero_mem' := by
    change Tendsto (fun n => sourceProjection (history (δ n)) (0 : CoefficientSpace)) _ _
    simpa only [map_zero] using (tendsto_const_nhds (x := (0 : CoefficientSpace)))
  add_mem' := by
    intro u v hu hv
    change Tendsto (fun n => sourceProjection (history (δ n)) (u+v)) _ _
    simpa only [map_add,zero_add] using hu.add hv
  smul_mem' := by
    intro c u hu
    change Tendsto (fun n => sourceProjection (history (δ n)) (c • u)) _ _
    simpa only [map_smul,smul_zero] using hu.const_smul c

theorem linearConvergenceSpace_closed : IsClosed (linearConvergenceSpace δ : Set CoefficientSpace) := by
  have he : Equicontinuous (fun n => sourceProjection (history (δ n))) :=
    (LipschitzWith.uniformEquicontinuous (fun n => sourceProjection (history (δ n))) 1
      (fun n => (sourceSpan (history (δ n))).lipschitzWith_starProjection)).equicontinuous
  exact he.isClosed_setOfPred_tendsto continuous_const

theorem sourceSpan_le_convergence (hδ : Tendsto δ atTop (𝓝 0)) :
    sourceSpan direction ≤ linearConvergenceSpace δ := by
  apply (Submodule.span ℝ (range direction)).topologicalClosure_minimal
    ?_ (linearConvergenceSpace_closed δ)
  apply Submodule.span_le.mpr
  rintro _ ⟨r,rfl⟩
  exact source_prediction_tendsto r δ hδ

theorem history_sourceSpan_le (d : ℝ≥0) : sourceSpan (history d) ≤ sourceSpan direction := by
  apply (Submodule.span ℝ (range (history d))).topologicalClosure_minimal
    ?_ (Submodule.isClosed_topologicalClosure _)
  apply Submodule.span_le.mpr
  rintro _ ⟨r,rfl⟩
  exact (Submodule.span ℝ (range direction)).le_topologicalClosure
    (Submodule.subset_span ⟨min r d,rfl⟩)

theorem source_prediction_all (hδ : Tendsto δ atTop (𝓝 0)) (u : CoefficientSpace) :
    Tendsto (fun n => sourceProjection (history (δ n)) u) atTop (𝓝 0) := by
  have ht := sourceSpan_le_convergence δ hδ
    ((sourceSpan direction).starProjection_apply_mem u)
  change Tendsto (fun n => sourceProjection (history (δ n)) (sourceProjection direction u)) _ _ at ht
  have he (n : ℕ) : sourceProjection (history (δ n)) (sourceProjection direction u) =
      sourceProjection (history (δ n)) u := by
    have hh := Submodule.starProjection_comp_starProjection_of_le (history_sourceSpan_le (δ n))
    exact congrArg (fun L : CoefficientSpace →L[ℝ] CoefficientSpace => L u) hh
  simpa only [he] using ht

theorem gaussian_prediction_all (hδ : Tendsto δ atTop (𝓝 0)) (F : GaussianL2) :
    Tendsto (fun n => conditionalProjection (history (δ n)) F) atTop
      (𝓝 (meanProjection F)) := by
  exact GaussianSingleObservationTotal.prediction_all (fun n => history (δ n))
    (source_prediction_all δ hδ) F

theorem joint_prediction_all (hδ : Tendsto δ atTop (𝓝 0))
    (F : IBMTimeAveragedObservable.JointL2) :
    Tendsto (fun n => IBMJointSceneryForecast.forecast (δ n) F) atTop
      (𝓝 (IBMNativeSourceRecovery.sourceVacuum F)) := by
  rw [← IBMJointSceneryForecast.sourceMean_eq_sourceVacuum]
  apply IBMJointSceneryForecast.forecast_tendsto
  exact ae_of_all _ fun Y => gaussian_prediction_all δ hδ _


theorem initial_channel_eq_vacuum (F : IBMTimeAveragedObservable.JointL2) :
    IBMObservedTerminalMartingale.channelClass F 0 =
      IBMObservedTerminalMartingale.channelClass (IBMNativeSourceRecovery.sourceVacuum F) 0 := by
  have ht := joint_prediction_all (IBMIntrinsicRightApproach.approach 0)
    (IBMIntrinsicRightApproach.approach_tendsto 0) F
  rw [← IBMJointSceneryForecast.sourceMean_eq_sourceVacuum] at ht
  have hz := IBMJointForecastGerm.initial_centered_channel_zero F
    (IBMIntrinsicRightApproach.approach 0) (IBMIntrinsicRightApproach.approach_positive 0) ht
  rw [IBMJointSceneryForecast.sourceMean_eq_sourceVacuum] at hz
  change (IBMIntrinsicRightGerm.rightPast 0).starProjection (_-_) = 0 at hz
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

theorem sourceVacuum_inner (F G : IBMTimeAveragedObservable.JointL2) :
    inner ℝ (IBMNativeSourceRecovery.sourceVacuum F) G =
      inner ℝ F (IBMNativeSourceRecovery.sourceVacuum G) := by
  let d := IBMIntrinsicRightApproach.approach 0
  have hd := IBMIntrinsicRightApproach.approach_tendsto 0
  have hl : Tendsto (fun n => inner ℝ (IBMJointSceneryForecast.forecast (d n) F) G)
      atTop (𝓝 (inner ℝ (IBMNativeSourceRecovery.sourceVacuum F) G)) :=
    (joint_prediction_all d hd F).inner tendsto_const_nhds
  have hr : Tendsto (fun n => inner ℝ F (IBMJointSceneryForecast.forecast (d n) G))
      atTop (𝓝 (inner ℝ F (IBMNativeSourceRecovery.sourceVacuum G))) :=
    (tendsto_const_nhds (x := F)).inner (joint_prediction_all d hd G)
  have he : (fun n => inner ℝ (IBMJointSceneryForecast.forecast (d n) F) G) =
      fun n => inner ℝ F (IBMJointSceneryForecast.forecast (d n) G) :=
    funext fun n => IBMJointSceneryForecast.forecast_inner (d n) F G
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

theorem germ_sourceVacuum_fixed (G : IBMTimeAveragedObservable.JointL2)
    (hG : G ∈ IBMIntrinsicRightGerm.rightPast 0) :
    IBMNativeSourceRecovery.sourceVacuum G = G := by
  apply ext_inner_left ℝ
  intro F
  rw [← sourceVacuum_inner]
  have h1 := (IBMIntrinsicRightGerm.rightPast 0).starProjection_inner_eq_zero F G hG
  have h2 := (IBMIntrinsicRightGerm.rightPast 0).starProjection_inner_eq_zero
    (IBMNativeSourceRecovery.sourceVacuum F) G hG
  rw [inner_sub_left] at h1 h2
  have he := initial_channel_eq_vacuum F
  change (IBMIntrinsicRightGerm.rightPast 0).starProjection F =
    (IBMIntrinsicRightGerm.rightPast 0).starProjection (IBMNativeSourceRecovery.sourceVacuum F) at he
  rw [he] at h1
  linarith

/-- Every initial-germ class has an explicit clock-only tensor in the original joint space. -/
theorem germ_clock_tensor (G : IBMTimeAveragedObservable.JointL2)
    (hG : G ∈ IBMIntrinsicRightGerm.rightPast 0) :
    IBMIntrinsicOperators.clockUnitary G = BochnerClosedOperator.tensor gaussianProduct gaussianOne
      (IBMGlobalVacuum.factorMean (IBMIntrinsicOperators.sourceUnitary G)) := by
  have hs : IBMIntrinsicOperators.sourceUnitary G =
      BochnerClosedOperator.tensor gaussianProduct
        (IBMGlobalVacuum.factorMean (IBMIntrinsicOperators.sourceUnitary G)) gaussianOne := by
    calc
      _ = IBMIntrinsicOperators.sourceUnitary (IBMNativeSourceRecovery.sourceVacuum G) :=
        congrArg IBMIntrinsicOperators.sourceUnitary (germ_sourceVacuum_fixed G hG).symm
      _ = (GaussianNumberSectors.projection 0).compLpL 2 gaussianProduct
          (IBMIntrinsicOperators.sourceUnitary G) :=
        IBMIntrinsicOperators.sourceUnitary.apply_symm_apply _
      _ = _ := IBMGlobalVacuum.factor_vacuum_tensor _
  calc
    _ = ProductL2Curry.flip gaussianProduct gaussianProduct
        (IBMIntrinsicOperators.sourceUnitary G) := IBMGlobalVacuum.clock_source_flip G
    _ = ProductL2Curry.flip gaussianProduct gaussianProduct
        (BochnerClosedOperator.tensor gaussianProduct
          (IBMGlobalVacuum.factorMean (IBMIntrinsicOperators.sourceUnitary G)) gaussianOne) :=
      congrArg (ProductL2Curry.flip gaussianProduct gaussianProduct) hs
    _ = _ := ProductL2Curry.flip_tensor _ _ _ _

theorem germ_joint_tensor (G : IBMTimeAveragedObservable.JointL2)
    (hG : G ∈ IBMIntrinsicRightGerm.rightPast 0) :
    G = ProductL2Curry.productTensor gaussianProduct gaussianProduct gaussianOne
      (IBMGlobalVacuum.factorMean (IBMIntrinsicOperators.sourceUnitary G)) := by
  apply IBMIntrinsicOperators.clockUnitary.injective
  rw [germ_clock_tensor G hG]
  exact (ProductL2Curry.curry_productTensor gaussianProduct gaussianProduct gaussianOne _).symm

theorem germ_clock_actual (G : IBMTimeAveragedObservable.JointL2)
    (hG : G ∈ IBMIntrinsicRightGerm.rightPast 0) :
    G =ᵐ[IBMSourceLaws.jointMeasure] fun p =>
      IBMGlobalVacuum.factorMean (IBMIntrinsicOperators.sourceUnitary G) p.2 := by
  have he := ProductL2Curry.productTensor_coeFn gaussianProduct gaussianProduct gaussianOne
    (IBMGlobalVacuum.factorMean (IBMIntrinsicOperators.sourceUnitary G))
  have hfst := measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)
  have ho := hfst.quasiMeasurePreserving.ae_eq_comp gaussianOne_coeFn
  filter_upwards [he,ho] with p hp hone
  calc
    G p = ProductL2Curry.productTensor gaussianProduct gaussianProduct gaussianOne
        (IBMGlobalVacuum.factorMean (IBMIntrinsicOperators.sourceUnitary G)) p :=
      congrArg (fun F : IBMTimeAveragedObservable.JointL2 => F p) (germ_joint_tensor G hG)
    _ = _ := by
      change gaussianOne p.1 = 1 at hone
      simpa only [hone,one_smul] using hp

theorem observable_target_reconstruction (f : IBMTimeAveragedObservable.IntrinsicSpace) :
    let F : IBMTimeAveragedObservable.JointL2 := f
    IBMFullPredictableIntegral.integral F
      ((IBMFullPredictableIntegral.integral F).toContinuousLinearMap.adjoint F) =
      F-IBMObservedTerminalMartingale.channelClass (IBMNativeSourceRecovery.sourceVacuum F) 0 := by
  dsimp only
  rw [← initial_channel_eq_vacuum]
  exact IBMTerminalSelfRepresentation.target_indexed_reconstruction f

end OperatorDerivativeRewrite.Foundation.IBMSceneryUniversalPrediction
