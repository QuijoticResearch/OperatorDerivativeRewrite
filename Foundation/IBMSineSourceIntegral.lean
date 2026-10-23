import Foundation.IBMSineSourceField

/-! Actual Bochner-L2 source-gradient formula for the IBM sine time average.
Native joint representatives are identified at every fixed time; no pointwise
interchange of an unbounded L2 evaluation map and integration is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineSourceIntegral
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMActualSineDomainObstruction IBMClockOverlapEnergy IBMClockGraphDualLimit
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem gradient_integrable (T : ℝ≥0) :
    Integrable (fun t : ℝ => sineSourceGradient t.toNNReal) (window T) := by
  obtain ⟨C, hC, hb⟩ := IBMSineAverageSourceDomain.sourceGradient_bounded T
  apply Integrable.of_bound IBMSineSourceField.sourceGradient_stronglyMeasurable.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hb t.toNNReal ⟨by positivity, Real.toNNReal_le_iff_le_coe.mpr ht.2⟩

theorem flat_integrable (T : ℝ≥0) : Integrable IBMSineSourceField.flat (window T) := by
  have h := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.toLinearIsometry.toContinuousLinearMap.integrable_comp
    (gradient_integrable T)
  have he : (fun t : ℝ => (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
      (sineSourceGradient t.toNNReal)) = IBMSineSourceField.flat :=
    funext fun t => (IBMSineSourceField.flat_eq t).symm
  exact he ▸ h

def sourceIntegral (T : ℝ≥0) : FieldSpace := ∫ t, sineSourceGradient t.toNNReal ∂window T

theorem integral_graph (T : ℝ≥0) :
    (sourceUnitary (IBMSineAverageSimpson.average T : JointL2), sourceIntegral T) ∈ Clock.graph := by
  have hu : Integrable IBMSineAverageSourceDomain.valueCurve (window T) :=
    IBMSineAverageSourceDomain.valueCurve_continuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hg := IBMNonlinearClockAverageGraph.integral_clock_graph
    IBMSineAverageSourceDomain.valueCurve (fun t : ℝ => sineSourceGradient t.toNNReal) hu
    (gradient_integrable T) (ae_of_all _ fun t => sinePoint_source_graph t.toNNReal)
  have he : (∫ t, IBMSineAverageSourceDomain.valueCurve t ∂window T) =
      sourceUnitary (IBMSineAverageSimpson.average T : JointL2) := by
    calc
      _ = ∫ t in (0 : ℝ)..(T : ℝ), IBMSineAverageSourceDomain.valueCurve t :=
        (intervalIntegral.integral_of_le T.property).symm
      _ = _ := IBMSineAverageSourceDomain.valueCurve_integral T
  exact he ▸ hg

theorem sourceIntegral_eq_gradient (T : ℝ≥0) :
    sourceIntegral T = IBMSineAverageIntrinsicCalculus.gradient T 0 :=
  Clock.mem_graph_snd_inj (integral_graph T) (IBMSineAverageWeakGradient.source_graph T) rfl

def flatIntegral (T : ℝ≥0) : IBMIntrinsicChainRule.JointVectorL2 :=
  ∫ t, IBMSineSourceField.flat t ∂window T

theorem flatIntegral_eq (T : ℝ≥0) :
    flatIntegral T = IBMIntrinsicChainRule.uncurryField (IBMSineAverageIntrinsicCalculus.gradient T 0) := by
  let U : FieldSpace →L[ℝ] IBMIntrinsicChainRule.JointVectorL2 :=
    (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.toLinearIsometry.toContinuousLinearMap
  have he : flatIntegral T = ∫ t, U (sineSourceGradient t.toNNReal) ∂window T := by
    apply integral_congr_ae
    exact ae_of_all _ fun t => IBMSineSourceField.flat_eq t
  have hi : (∫ t, U (sineSourceGradient t.toNNReal) ∂window T) = U (sourceIntegral T) :=
    U.integral_comp_comm (gradient_integrable T)
  exact he.trans (hi.trans (congrArg U (sourceIntegral_eq_gradient T)))

def nativeField (t : ℝ) : IBMIntrinsicChainRule.JointVectorL2 :=
  IBMClockVectorTranspose.swap (IBMSineSourceField.flat t)

theorem nativeField_ae (t : ℝ) : nativeField t =ᵐ[IBMSourceLaws.jointMeasure] fun p =>
    Real.cos (IBMConstructedSources.ibmValue t.toNNReal p) •
      IBMSineSourceField.direction |IBMConstructedSources.clockPath p.2 t.toNNReal| := by
  have ha := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    (IBMSineSourceField.flat_ae t)
  filter_upwards [IBMClockVectorTranspose.swap_ae (IBMSineSourceField.flat t), ha] with p hs ha
  exact hs.trans ha

theorem nativeField_stronglyMeasurable : StronglyMeasurable nativeField :=
  IBMClockVectorTranspose.swap.continuous.comp_stronglyMeasurable IBMSineSourceField.flat_stronglyMeasurable

theorem nativeField_integrable (T : ℝ≥0) : Integrable nativeField (window T) :=
  IBMClockVectorTranspose.swap.toContinuousLinearMap.integrable_comp (flat_integrable T)

theorem native_source_formula (T : ℝ≥0) :
    IBMClockVectorTranspose.realize (IBMSineAverageIntrinsicCalculus.gradient T 0) =
      ∫ t, nativeField t ∂window T := by
  have hi : (∫ t, nativeField t ∂window T) = IBMClockVectorTranspose.swap (flatIntegral T) :=
    IBMClockVectorTranspose.swap.toContinuousLinearMap.integral_comp_comm (flat_integrable T)
  calc
    _ = IBMClockVectorTranspose.swap
        (IBMIntrinsicChainRule.uncurryField (IBMSineAverageIntrinsicCalculus.gradient T 0)) := rfl
    _ = IBMClockVectorTranspose.swap (flatIntegral T) :=
      congrArg IBMClockVectorTranspose.swap (flatIntegral_eq T).symm
    _ = _ := hi.symm

theorem actual_product_integrable (t : ℝ) (V : IBMIntrinsicChainRule.JointVectorL2) :
    Integrable (fun p => Real.cos (IBMConstructedSources.ibmValue t.toNNReal p) *
      inner ℝ (IBMSineSourceField.direction |IBMConstructedSources.clockPath p.2 t.toNNReal|) (V p))
        IBMSourceLaws.jointMeasure := by
  apply (L2.integrable_inner (𝕜 := ℝ) (nativeField t) V).congr
  filter_upwards [nativeField_ae t] with p hp
  rw [hp, real_inner_smul_left]

theorem actual_pairing (t : ℝ) (V : IBMIntrinsicChainRule.JointVectorL2) :
    inner ℝ (nativeField t) V = ∫ p, Real.cos (IBMConstructedSources.ibmValue t.toNNReal p) *
      inner ℝ (IBMSineSourceField.direction |IBMConstructedSources.clockPath p.2 t.toNNReal|) (V p)
        ∂IBMSourceLaws.jointMeasure := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [nativeField_ae t] with p hp
  rw [hp, real_inner_smul_left]

theorem actual_time_pairing_integrable (T : ℝ≥0) (V : IBMIntrinsicChainRule.JointVectorL2) :
    Integrable (fun t => ∫ p, Real.cos (IBMConstructedSources.ibmValue t.toNNReal p) *
      inner ℝ (IBMSineSourceField.direction |IBMConstructedSources.clockPath p.2 t.toNNReal|) (V p)
        ∂IBMSourceLaws.jointMeasure) (window T) := by
  have h := (innerSL ℝ V).integrable_comp (nativeField_integrable T)
  apply h.congr
  apply ae_of_all
  intro t
  have he : inner ℝ V (nativeField t) = inner ℝ (nativeField t) V := real_inner_comm _ _
  exact he.trans (actual_pairing t V)

theorem actual_source_pairing (T : ℝ≥0) (V : IBMIntrinsicChainRule.JointVectorL2) :
    inner ℝ (IBMClockVectorTranspose.realize (IBMSineAverageIntrinsicCalculus.gradient T 0)) V =
      ∫ t, ∫ p, Real.cos (IBMConstructedSources.ibmValue t.toNNReal p) *
        inner ℝ (IBMSineSourceField.direction |IBMConstructedSources.clockPath p.2 t.toNNReal|) (V p)
          ∂IBMSourceLaws.jointMeasure ∂window T := by
  calc
    _ = inner ℝ (∫ t, nativeField t ∂window T) V :=
      congrArg (fun F : IBMIntrinsicChainRule.JointVectorL2 => inner ℝ F V) (native_source_formula T)
    _ = inner ℝ V (∫ t, nativeField t ∂window T) := real_inner_comm _ _
    _ = ∫ t, inner ℝ V (nativeField t) ∂window T := (integral_inner (nativeField_integrable T) V).symm
    _ = ∫ t, inner ℝ (nativeField t) V ∂window T := by
      apply integral_congr_ae
      exact ae_of_all _ fun _ => real_inner_comm _ _
    _ = _ := integral_congr_ae (ae_of_all _ fun t => actual_pairing t V)

end OperatorDerivativeRewrite.Foundation.IBMSineSourceIntegral
