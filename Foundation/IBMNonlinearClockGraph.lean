import Foundation.IBMClockVectorTranspose
import Foundation.IBMActualSineDomainObstruction
import Foundation.IBMNonlinearClockEnergy

/-! Identification of the nonlinear candidate with the original closed clock
graph, using actual representatives and the correct parameter transposition. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearClockGraph
open InfiniteGaussian IBMTimeAveragedObservable IBMConstructedSources
open IBMFirstSourceClockGraph IBMIntrinsicOperators
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : MeasurableSpace CoefficientSpace := borel CoefficientSpace
local instance : BorelSpace CoefficientSpace := ⟨rfl⟩
attribute [local irreducible] clockPath scalarTensor IBMFirstSourceClockGraph.flip
  IBMClockAverageCandidate.direction

def input (n : ℕ) (t : ℝ≥0) : JointL2 :=
  jointRealization (IBMRandomTimeHilbert.randomMollifiedL2 n t)

theorem input_ae (n : ℕ) (t : ℝ≥0) :
    input n t =ᵐ[IBMSourceLaws.jointMeasure] mollifiedValue n 0 t := by
  apply jointRealization_ae_of_sections _ _
    ((mollifiedValue_jointly_measurable n 0).comp (measurable_const.prodMk measurable_id))
  filter_upwards [(IBMRandomTimeHilbert.randomMollifiedClass_memLp n t).coeFn_toLp,
    clockPath_coordinate_ae t] with Y hu hc
  change IBMRandomTimeHilbert.randomMollifiedL2 n t Y =
    IBMRandomTimeHilbert.randomMollifiedClass n t Y at hu
  rw [hu]
  change IBMContinuousScenery.wholeLineScenery (IBMMollifier.kernel n)
    |GaussianTimeProcess.process t Y| =ᵐ[gaussianProduct]
      fun X => IBMDyadicExtension.field n 0 X |clockPath Y t|
  rw [hc]
  have he := (IBMPointwiseEvaluation.field_memLp n 0 |GaussianTimeProcess.process t Y|).coeFn_toLp
  rw [IBMPointwiseEvaluation.field_toLp_eq] at he
  simpa only [IBMJointMollifierGaussian.derivativeKernel, ite_true] using he

theorem input_clock_graph (n : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    (clockUnitary (input n t), clockGradient n t) ∈ IBMClockGraphDualLimit.Clock.graph := by
  have h := mollified_clock_graph n t ht
  unfold IBMFirstSourceClockGraph.flip at h
  exact h

theorem uncurry_gradient_ae (h : CoefficientSpace) (u : ScalarSpace) :
    IBMIntrinsicChainRule.uncurryField (gradientMap h u) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm u) p • h := by
  let v := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm u
  let w := IBMIntrinsicChainRule.uncurryField (gradientMap h u)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (Lp.stronglyMeasurable w).measurable
    ((Lp.stronglyMeasurable v).measurable.smul measurable_const))).mpr
  filter_upwards [ProductL2Curry.curryEquiv_symm_coeFn gaussianProduct gaussianProduct
      (gradientMap h u),
    ProductL2Curry.curryEquiv_symm_coeFn gaussianProduct gaussianProduct u,
    (IBMClockAverageCandidate.tensorBilinear h).coeFn_compLpL u] with X hw hv hg
  change gradientMap h u X = IBMClockAverageCandidate.tensorBilinear h (u X) at hg
  rw [hg, IBMClockAverageCandidate.tensorBilinear_eq] at hw
  filter_upwards [hw, hv, scalarTensor_coeFn h (u X)] with Y hw hv ht
  exact hw.symm.trans (ht.trans (congrArg (fun r : ℝ => r • h) hv))

theorem signed_input_ae (n : ℕ) (t : ℝ≥0) :
    jointRealization (signedSource n t) =ᵐ[IBMSourceLaws.jointMeasure] fun p =>
      BrownianSignIntegral.signum (clockPath p.2 t) * mollifiedValue n 1 t p := by
  apply jointRealization_ae_of_sections _ _
    ((BrownianSignIntegral.signum_measurable.comp
      (((ContinuousMap.measurable_eval t).comp clockPath_measurable).comp measurable_snd)).mul
      ((mollifiedValue_jointly_measurable n 1).comp (measurable_const.prodMk measurable_id)))
  filter_upwards [signedSource_ae n t] with Y hu
  rw [hu]
  filter_upwards [Lp.coeFn_smul (BrownianSignIntegral.signum (clockPath Y t))
      (IBMClockAverageCandidate.sourceColumn n |clockPath Y t|),
    IBMClockAverageCandidate.sourceColumn_actual_ae n |clockPath Y t|] with X hs ha
  change (BrownianSignIntegral.signum _ • IBMClockAverageCandidate.sourceColumn n _) X = _
  rw [hs, Pi.smul_apply, ha]
  rfl

theorem clockGradient_actual_ae (n : ℕ) (t : ℝ≥0) :
    IBMIntrinsicChainRule.uncurryField (clockGradient n t) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => (BrownianSignIntegral.signum (clockPath p.2 t) * mollifiedValue n 1 t p) •
        IBMClockAverageCandidate.direction t := by
  have h := uncurry_gradient_ae (IBMClockAverageCandidate.direction t) (flip (signedSource n t))
  have he : (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
      (flip (signedSource n t)) = jointRealization (signedSource n t) := by
    unfold IBMFirstSourceClockGraph.flip
    exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm_apply_apply _
  rw [he] at h
  filter_upwards [h, signed_input_ae n t] with p hg hs
  exact hg.trans (congrArg (fun r : ℝ => r • IBMClockAverageCandidate.direction t) hs)

def actualField (n : ℕ) (t : ℝ) (p : IBMSourceLaws.JointSample) : CoefficientSpace :=
  (BrownianSignIntegral.signum (clockPath p.2 t.toNNReal) *
    Real.cos (mollifiedValue n 0 t.toNNReal p) * mollifiedValue n 1 t.toNNReal p) •
      IBMClockAverageCandidate.direction t

theorem actualField_measurable (n : ℕ) (t : ℝ) : Measurable (actualField n t) := by
  exact (((BrownianSignIntegral.signum_measurable.comp
    (((ContinuousMap.measurable_eval t.toNNReal).comp clockPath_measurable).comp measurable_snd)).mul
    (Real.continuous_cos.measurable.comp ((mollifiedValue_jointly_measurable n 0).comp
      (measurable_const.prodMk measurable_id)))).mul
    ((mollifiedValue_jointly_measurable n 1).comp (measurable_const.prodMk measurable_id))).smul
      measurable_const

theorem candidate_actual_ae (n : ℕ) (t : ℝ) :
    IBMClockVectorTranspose.realize (IBMNonlinearClockField.field n t)
      =ᵐ[IBMSourceLaws.jointMeasure] actualField n t := by
  apply IBMClockVectorTranspose.realize_ae_of_sections _ _ (actualField_measurable n t)
  filter_upwards [IBMNonlinearClockField.field_ae n t] with Y hY
  rw [hY]
  exact IBMNonlinearClockField.section_actual_ae n t Y

theorem chainField_eq (n : ℕ) (t : ℝ≥0) :
    IBMClockWeakChain.chainField IBMActualSineDomainObstruction.sineTest
      (input n t) (clockGradient n t) =
        IBMClockVectorTranspose.clockField (IBMNonlinearClockField.field n t) := by
  apply (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.injective
  change IBMIntrinsicChainRule.uncurryField
    (IBMClockWeakChain.chainField IBMActualSineDomainObstruction.sineTest
      (input n t) (clockGradient n t)) = IBMIntrinsicChainRule.uncurryField
        (IBMClockVectorTranspose.clockField (IBMNonlinearClockField.field n t))
  rw [IBMClockVectorTranspose.uncurry_clockField]
  have he := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm_apply_apply
    (IBMClockWeakChain.slopeField IBMActualSineDomainObstruction.sineTest
      (input n t) (IBMIntrinsicChainRule.uncurryField (clockGradient n t)))
  apply he.trans
  apply Lp.ext
  filter_upwards [IBMClockWeakChain.slopeField_ae IBMActualSineDomainObstruction.sineTest
      (input n t) (IBMIntrinsicChainRule.uncurryField (clockGradient n t)),
    input_ae n t, clockGradient_actual_ae n t, candidate_actual_ae n t] with p hs hi hg hc
  rw [hs, hi, hg, hc]
  change Real.cos _ • ((_ * _) • _) = (_ * Real.cos _ * _) • _
  rw [smul_smul]
  congr 1
  simp only [Real.toNNReal_coe]
  ring

theorem sine_clock_graph (n : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    (clockUnitary (IBMClockWeakChain.value IBMActualSineDomainObstruction.sineTest (input n t)),
      IBMClockVectorTranspose.clockField (IBMNonlinearClockField.field n t)) ∈
        IBMClockGraphDualLimit.Clock.graph := by
  rw [← chainField_eq]
  exact IBMClockWeakChain.chain_graph _ _ _ (input_clock_graph n t ht)

end OperatorDerivativeRewrite.Foundation.IBMNonlinearClockGraph
