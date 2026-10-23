import Foundation.IBMSineAverageWeakGradient

/-! Actual joint representatives for the nonlinear source gradient, with the
clock parameter outside and scenery parameter inside as in the original source graph. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineSourceField
open InfiniteGaussian IBMTimeAveragedObservable IBMConstructedSources
open IBMActualSineDomainObstruction IBMIntrinsicOperators
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
  FractionalSpectralKernel.spectralSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : MeasurableSpace CoefficientSpace := borel CoefficientSpace
local instance : BorelSpace CoefficientSpace := ⟨rfl⟩
attribute [local irreducible] clockPath ibmValue

def direction (r : ℝ) : CoefficientSpace :=
  SeparableHilbertEmbedding.hilbertEmbedding FractionalSpectralKernel.SpectralSpace
    (IBMFiniteScenerySmoothing.direction r)

theorem direction_continuous : Continuous direction :=
  (SeparableHilbertEmbedding.hilbertEmbedding FractionalSpectralKernel.SpectralSpace).continuous.comp
    IBMContinuousScenery.direction_continuous

def linearField (t : ℝ) (p : IBMSourceLaws.JointSample) : CoefficientSpace :=
  direction |clockPath p.1 t.toNNReal|

def value (t : ℝ) (p : IBMSourceLaws.JointSample) : CoefficientSpace :=
  Real.cos (ibmValue t.toNNReal (p.2, p.1)) • linearField t p

theorem linearField_jointly_measurable :
    Measurable (Function.uncurry linearField) := by
  exact direction_continuous.measurable.comp (continuous_abs.measurable.comp
    (BrownianClockWeightedEnergy.sigma_measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))))

theorem value_jointly_measurable : Measurable (Function.uncurry value) := by
  have harg : Measurable (fun p : ℝ × IBMSourceLaws.JointSample =>
      (p.1.toNNReal, (p.2.2, p.2.1))) :=
    (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
  exact (Real.continuous_cos.measurable.comp (ibmValue_jointly_measurable.comp harg)).smul
    linearField_jointly_measurable

attribute [local irreducible] direction linearField

theorem linear_gradient_ae (t : ℝ≥0) :
    IBMIntrinsicChainRule.uncurryField (IBMUnmollifiedSourceDerivative.gradient t)
      =ᵐ[IBMSourceLaws.jointMeasure] linearField t := by
  let g := IBMIntrinsicChainRule.uncurryField (IBMUnmollifiedSourceDerivative.gradient t)
  have hm : Measurable (linearField (t : ℝ)) :=
    linearField_jointly_measurable.comp (measurable_const.prodMk measurable_id)
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.stronglyMeasurable g).measurable hm)).mpr
  filter_upwards [ProductL2Curry.curryEquiv_symm_coeFn gaussianProduct gaussianProduct
      (IBMUnmollifiedSourceDerivative.gradient t),
    IBMUnmollifiedSourceDerivative.gradient_ae t, clockPath_coordinate_ae t] with Y hc hg hy
  rw [hg] at hc
  filter_upwards [hc, Lp.coeFn_const (p := 2) (μ := gaussianProduct)
    (c := direction |GaussianTimeProcess.process t Y|)] with X hc hk
  change g (Y, X) = linearField (t : ℝ) (Y, X)
  unfold linearField
  rw [Real.toNNReal_coe, hy]
  unfold direction at hk
  unfold direction
  exact hc.symm.trans hk

theorem swapped_point_ae (t : ℝ≥0) :
    ProductL2Curry.swap gaussianProduct gaussianProduct (intrinsicCurve t : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure] fun p => ibmValue t (p.2, p.1) := by
  have ha := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp (joint_point_actual_ae t)
  filter_upwards [ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct (intrinsicCurve t : JointL2), ha]
    with p hs hi
  exact hs.trans hi

theorem source_gradient_ae (t : ℝ≥0) :
    IBMIntrinsicChainRule.uncurryField (sineSourceGradient t)
      =ᵐ[IBMSourceLaws.jointMeasure] value t := by
  have he := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm_apply_apply
    (IBMClockWeakChain.slopeField sineTest
      (ProductL2Curry.swap gaussianProduct gaussianProduct (intrinsicCurve t : JointL2))
      (IBMIntrinsicChainRule.uncurryField (IBMUnmollifiedSourceDerivative.gradient t)))
  have ha := IBMClockWeakChain.slopeField_ae sineTest
    (ProductL2Curry.swap gaussianProduct gaussianProduct (intrinsicCurve t : JointL2))
    (IBMIntrinsicChainRule.uncurryField (IBMUnmollifiedSourceDerivative.gradient t))
  have hb : IBMIntrinsicChainRule.uncurryField (sineSourceGradient t) =
      IBMClockWeakChain.slopeField sineTest
        (ProductL2Curry.swap gaussianProduct gaussianProduct (intrinsicCurve t : JointL2))
        (IBMIntrinsicChainRule.uncurryField (IBMUnmollifiedSourceDerivative.gradient t)) := he
  rw [hb]
  filter_upwards [ha, swapped_point_ae t, linear_gradient_ae t] with p hs hf hg
  have h1 := congrArg (fun a : ℝ => sineTest.slope a •
    IBMIntrinsicChainRule.uncurryField (IBMUnmollifiedSourceDerivative.gradient t) p) hf
  have h2 := congrArg (fun b : CoefficientSpace => sineTest.slope (ibmValue t (p.2, p.1)) • b) hg
  exact hs.trans (h1.trans (h2.trans (by simp only [value, Real.toNNReal_coe, sineTest])))

theorem value_memLp (t : ℝ) : MemLp (value t) 2 IBMSourceLaws.jointMeasure := by
  have ha := source_gradient_ae t.toNNReal
  have he : value (t.toNNReal : ℝ) = value t := by
    funext p
    simp only [value, linearField, Real.toNNReal_coe]
  rw [he] at ha
  exact (Lp.memLp _).ae_eq ha

def flat (t : ℝ) : IBMIntrinsicChainRule.JointVectorL2 :=
  ProductL2Sections.sectionL2 IBMSourceLaws.jointMeasure (Function.uncurry value) t

theorem flat_ae (t : ℝ) : flat t =ᵐ[IBMSourceLaws.jointMeasure] value t :=
  ProductL2Sections.sectionL2_coeFn _ _ t (value_memLp t)

theorem flat_stronglyMeasurable : StronglyMeasurable flat :=
  ProductL2Sections.sectionL2_stronglyMeasurable _ _ value_jointly_measurable.stronglyMeasurable

theorem flat_eq (t : ℝ) : flat t = IBMIntrinsicChainRule.uncurryField (sineSourceGradient t.toNNReal) := by
  apply Lp.ext
  have he : value (t.toNNReal : ℝ) = value t := by
    funext p
    simp only [value, linearField, Real.toNNReal_coe]
  exact (flat_ae t).trans (he ▸ (source_gradient_ae t.toNNReal)).symm

theorem sourceGradient_stronglyMeasurable :
    StronglyMeasurable (fun t : ℝ => sineSourceGradient t.toNNReal) := by
  have he (t : ℝ) : sineSourceGradient t.toNNReal =
      ProductL2Curry.curryEquiv gaussianProduct gaussianProduct (flat t) := by
    rw [flat_eq]
    exact ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).apply_symm_apply _).symm
  simp_rw [he]
  exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).continuous.comp_stronglyMeasurable
    flat_stronglyMeasurable

end OperatorDerivativeRewrite.Foundation.IBMSineSourceField
