import Foundation.IBMSineSourceStrongQuadrature

/-! Actual samplewise vector-integral realization from compatible strong-L2
and pathwise native quadratures, without treating L2 evaluation as continuous. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineSourcePathIntegral
open InfiniteGaussian IBMTimeAveragedObservable IBMJointIntrinsicDerivative
open IBMBochnerTimeQuadrature IBMContinuousQuadrature IBMSineSourceStrongQuadrature
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : MeasurableSpace CoefficientSpace := borel CoefficientSpace
local instance : BorelSpace CoefficientSpace := ⟨rfl⟩

def sampleField (t : ℝ) (p : IBMSourceLaws.JointSample) : CoefficientSpace :=
  IBMSineSourceField.value t (p.2, p.1)

section
attribute [local irreducible] IBMSineSourceField.value IBMSineSourceField.linearField
  IBMSineSourceField.direction
theorem sampleField_jointly_measurable : Measurable (Function.uncurry sampleField) :=
  IBMSineSourceField.value_jointly_measurable.comp
    (measurable_fst.prodMk (measurable_swap.comp measurable_snd))
end

theorem sampleField_continuous (p : IBMSourceLaws.JointSample) :
    Continuous (fun t => sampleField t p) := IBMSineSourceContinuity.value_continuous (p.2, p.1)

def sampleSum (T : ℝ≥0) (n : ℕ) (p : IBMSourceLaws.JointSample) : CoefficientSpace :=
  rightSum (fun t => sampleField t p) T (n + 1)

theorem nativeSum_actual_ae (T : ℝ≥0) (n : ℕ) :
    nativeSum T n =ᵐ[IBMSourceLaws.jointMeasure] sampleSum T n := by
  let N := n + 1
  let a : ℝ := (T : ℝ) / N
  let f : ℕ → IBMIntrinsicChainRule.JointVectorL2 := fun i =>
    IBMSineSourceIntegral.nativeField (time T N (i + 1))
  have ha := ae_all_iff.mpr (fun i : ℕ => IBMSineSourceIntegral.nativeField_ae (time T N (i + 1)))
  have hb := ae_all_iff.mpr (fun i : ℕ => Lp.coeFn_smul a (f i))
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range N) (fun i => a • f i), ha, hb]
    with p hs ha hb
  change (∑ i ∈ Finset.range N, a • f i) p = ∑ i ∈ Finset.range N, a • sampleField (time T N (i + 1)) p
  rw [hs]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hb i, Pi.smul_apply]
  exact congrArg (fun v : CoefficientSpace => a • v) (ha i)

def sampleIntegral (T : ℝ≥0) (p : IBMSourceLaws.JointSample) : CoefficientSpace :=
  ∫ t in (0 : ℝ)..(T : ℝ), sampleField t p

theorem sampleIntegral_stronglyMeasurable (T : ℝ≥0) : StronglyMeasurable (sampleIntegral T) := by
  have h : StronglyMeasurable (fun p => ∫ t, sampleField t p ∂IBMClockOverlapEnergy.window T) :=
    sampleField_jointly_measurable.stronglyMeasurable.integral_prod_left
  have he : sampleIntegral T = fun p => ∫ t, sampleField t p ∂IBMClockOverlapEnergy.window T :=
    funext fun p => intervalIntegral.integral_of_le T.property
  exact he.symm ▸ h

theorem sampleField_intervalIntegrable (T : ℝ≥0) (p : IBMSourceLaws.JointSample) :
    IntervalIntegrable (fun t => sampleField t p) volume 0 T :=
  (sampleField_continuous p).intervalIntegrable _ _

theorem sampleSum_tendsto (T : ℝ≥0) (p : IBMSourceLaws.JointSample) :
    Tendsto (fun n => sampleSum T n p) atTop (𝓝 (sampleIntegral T p)) :=
  rightSum_tendsto _ (sampleField_continuous p) T.property

theorem nativeSum_ae_tendsto (T : ℝ≥0) :
    ∀ᵐ p ∂IBMSourceLaws.jointMeasure,
      Tendsto (fun n => nativeSum T n p) atTop (𝓝 (sampleIntegral T p)) := by
  filter_upwards [ae_all_iff.mpr (fun n => nativeSum_actual_ae T n)] with p hp
  have he : (fun n => nativeSum T n p) = fun n => sampleSum T n p := funext hp
  exact he ▸ sampleSum_tendsto T p

theorem actual_source_integral_ae (T : ℝ≥0) :
    IBMClockVectorTranspose.realize (IBMSineAverageIntrinsicCalculus.gradient T 0)
      =ᵐ[IBMSourceLaws.jointMeasure] sampleIntegral T :=
  tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_Lp (nativeSum_tendsto T))
    (tendstoInMeasure_of_tendsto_ae (fun n => Lp.aestronglyMeasurable (nativeSum T n))
      (nativeSum_ae_tendsto T))

theorem sampleIntegral_memLp (T : ℝ≥0) : MemLp (sampleIntegral T) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp _).ae_eq (actual_source_integral_ae T)

end OperatorDerivativeRewrite.Foundation.IBMSineSourcePathIntegral
