import Foundation.IBMSchwartzNativeAverage
import Foundation.IBMActualTaylorChain
import Foundation.IBMCenteredSourceRepresentation

/-! Actual first-three-channel forward Taylor convergence to an ORIGINAL native
joint divergence plus the necessary deterministic mean correction. The random
quartic drift is represented using the verified actual Schwartz time average. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzNativeTaylor
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMCorrectionStein IBMSchwartzHeatDerivative IBMClockOverlapEnergy
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] jointDerivative IBMSchwartzHybridReconstruction.integrand
  IBMSchwartzHybridReconstruction.centered IBMSchwartzNativeAverage.observable
  IBMSchwartzNativeAverage.field heatMean IBMSchwartzHalfHolderHeat.curve

def mean (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : ℝ :=
  inner ℝ gaussianOne (heatMean g a 0 T)

theorem mean_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Integrable (fun t : ℝ => mean g a t.toNNReal) (window T) :=
  (continuous_const.inner ((IBMSchwartzHybridTime.initial_continuous g a).comp
    continuous_real_toNNReal)).integrableOn_Icc.mono_set Ioc_subset_Icc_self

def drift (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (p : IBMSourceLaws.JointSample) : ℝ :=
  IBMContinuousWeightedQuartic.timeIntegral T (shiftedJet g a 4) p

theorem drift_path_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (p : IBMSourceLaws.JointSample) :
    Integrable (fun t : ℝ => (jet g 4) (a+IBMConstructedSources.ibmValue t.toNNReal p))
      (window T) :=
  (IBMContinuousWeightedQuartic.weight_continuous (shiftedJet g a 4)
    (shiftedJet_smooth g a 4).continuous p).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem average_actual_split (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    (IBMSchwartzNativeAverage.observable (jet g 4) a T : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure] fun p =>
        drift g a T p - ∫ t, mean (jet g 4) a t.toNNReal ∂window T := by
  filter_upwards [IBMSchwartzNativeAverage.observable_actual (jet g 4) a T] with p hp
  rw [hp]
  simp_rw [IBMSchwartzHybridReconstruction.global_mean]
  change (∫ t, (jet g 4) (a+IBMConstructedSources.ibmValue t.toNNReal p) -
    mean (jet g 4) a t.toNNReal ∂window T) = _
  rw [integral_sub (drift_path_integrable g a T p) (mean_integrable (jet g 4) a T)]
  congr 1
  exact (intervalIntegral.integral_of_le T.property).symm

private def endpointInput (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    jointDivergence.domain :=
  ⟨IBMSchwartzHybridReconstruction.integrand g a T,
    (IBMSchwartzHybridReconstruction.reconstruction g a T).choose⟩

private def averageInput (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    jointDivergence.domain :=
  ⟨IBMSchwartzNativeAverage.field (jet g 4) a T,
    (IBMSchwartzNativeAverage.reconstruction (jet g 4) a T).choose⟩

def input (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : jointDivergence.domain :=
  endpointInput g a T - (1/8:ℝ) • averageInput g a T

theorem input_field (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    (input g a T : JointFieldSpace) = IBMSchwartzHybridReconstruction.integrand g a T -
      (1/8:ℝ) • IBMSchwartzNativeAverage.field (jet g 4) a T := rfl

theorem input_value (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    jointDivergence (input g a T) = IBMSchwartzHybridReconstruction.centered g a T -
      (1/8:ℝ) • IBMSchwartzNativeAverage.observable (jet g 4) a T := by
  change jointDivergence (endpointInput g a T - (1/8:ℝ) • averageInput g a T) = _
  have he : jointDivergence (endpointInput g a T) =
      IBMSchwartzHybridReconstruction.centered g a T :=
    (IBMSchwartzHybridReconstruction.reconstruction g a T).choose_spec
  have ha : jointDivergence (averageInput g a T) =
      IBMSchwartzNativeAverage.observable (jet g 4) a T :=
    (IBMSchwartzNativeAverage.reconstruction (jet g 4) a T).choose_spec
  rw [LinearPMap.map_sub,LinearPMap.map_smul,he,ha]

def correction (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : ℝ :=
  mean g a T - g a - (1/8:ℝ) * ∫ t, mean (jet g 4) a t.toNNReal ∂window T

def value (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : JointL2 :=
  (jointDivergence (input g a T) : JointL2) +
    Lp.const 2 IBMSourceLaws.jointMeasure (correction g a T)

theorem value_actual (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    value g a T =ᵐ[IBMSourceLaws.jointMeasure]
      IBMActualTaylorChain.limitValue (shiftedJet g a 0) T := by
  have hv := input_value g a T
  have he : (jointDivergence (input g a T) : JointL2) =
      (IBMSchwartzHybridReconstruction.centered g a T : JointL2) -
        (1/8:ℝ) • (IBMSchwartzNativeAverage.observable (jet g 4) a T : JointL2) :=
    congrArg (fun v : IntrinsicSpace => (v : JointL2)) hv
  unfold value
  rw [he]
  filter_upwards [IBMSchwartzHybridReconstruction.centered_actual g a T,
    average_actual_split g a T,IBMRawInitialPast.ibm_zero_ae,
    Lp.coeFn_smul (1/8:ℝ) (IBMSchwartzNativeAverage.observable (jet g 4) a T : JointL2),
    Lp.coeFn_sub (IBMSchwartzHybridReconstruction.centered g a T : JointL2)
      ((1/8:ℝ) • (IBMSchwartzNativeAverage.observable (jet g 4) a T : JointL2)),
    Lp.coeFn_add
      ((IBMSchwartzHybridReconstruction.centered g a T : JointL2) -
        (1/8:ℝ) • (IBMSchwartzNativeAverage.observable (jet g 4) a T : JointL2))
      (Lp.const 2 IBMSourceLaws.jointMeasure (correction g a T)),
    Lp.coeFn_const 2 IBMSourceLaws.jointMeasure (correction g a T)]
    with p hc ha hz hsm hsub hadd hconst
  rw [hadd,Pi.add_apply,hsub,Pi.sub_apply,hsm,Pi.smul_apply,hc,ha,hconst]
  rw [IBMSchwartzHybridReconstruction.global_mean]
  unfold IBMActualTaylorChain.limitValue IBMActualTaylorChain.endpointDifference
  rw [IBMSchwartzSimpsonNative.iterated_shifted,hz]
  change g (a+IBMConstructedSources.ibmValue T p) - mean g a T -
      (1/8:ℝ)*(drift g a T p - ∫ t, mean (jet g 4) a t.toNNReal ∂window T) +
      correction g a T = g (a+IBMConstructedSources.ibmValue T p) - g (a+0) -
        (1/8:ℝ)*drift g a T p
  simp only [add_zero,correction]
  ring

/-- The ORIGINAL actual first THREE forward Taylor channels converge in
probability to the native divergence plus its deterministic mean correction. -/
theorem channels_tendstoInMeasure (g : SchwartzMap ℝ ℝ) (a : ℝ)
    {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure IBMSourceLaws.jointMeasure
      (IBMActualTaylorChain.channels (shiftedJet g a 0) T) atTop (value g a T) :=
  TendstoInMeasure.congr_right (value_actual g a T).symm
    (IBMActualTaylorChain.channels_tendstoInMeasure (shiftedJet g a 0)
      (IBMSchwartzSimpsonNative.shifted_smooth g a 4) hT)

attribute [local irreducible] input correction value

theorem limit_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    MemLp (IBMActualTaylorChain.limitValue (shiftedJet g a 0) T) 2
      IBMSourceLaws.jointMeasure :=
  (Lp.memLp (value g a T)).ae_eq (value_actual g a T)

theorem actual_pairing_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (F : JointL2) : Integrable (fun p =>
      IBMActualTaylorChain.limitValue (shiftedJet g a 0) T p * F p)
      IBMSourceLaws.jointMeasure :=
  (limit_memLp g a T).integrable_mul (Lp.memLp F)

/-- Stochastic IBP for the ACTUAL limiting Taylor random variable. No claim
of uniform integrability or finite-channel expectation convergence is made. -/
theorem actual_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (F : jointDerivative.domain) :
    (∫ p, IBMActualTaylorChain.limitValue (shiftedJet g a 0) T p *
      ((F : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure) =
      inner ℝ (input g a T : JointFieldSpace) (jointDerivative F) +
        correction g a T * ∫ p, ((F : IntrinsicSpace) : JointL2) p
          ∂IBMSourceLaws.jointMeasure := by
  have he : (∫ p, IBMActualTaylorChain.limitValue (shiftedJet g a 0) T p *
      ((F : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure) =
      inner ℝ (value g a T) ((F : IntrinsicSpace) : JointL2) := by
    rw [L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [value_actual g a T] with p hp
    simp only [hp,Real.inner_apply]
  have hc : inner ℝ (Lp.const 2 IBMSourceLaws.jointMeasure (correction g a T))
      ((F : IntrinsicSpace) : JointL2) =
      correction g a T * ∫ p, ((F : IntrinsicSpace) : JointL2) p
        ∂IBMSourceLaws.jointMeasure := by
    rw [L2_inner_eq_integral,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 IBMSourceLaws.jointMeasure (correction g a T)] with p hp
    simp only [hp,Function.const_apply,Real.inner_apply]
  rw [he]
  unfold value
  have hn : inner ℝ (jointDivergence (input g a T) : JointL2)
      ((F : IntrinsicSpace) : JointL2) =
      inner ℝ (input g a T : JointFieldSpace) (jointDerivative F) :=
    jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense (input g a T) F
  calc
    _ = inner ℝ (jointDivergence (input g a T) : JointL2) ((F : IntrinsicSpace) : JointL2) +
        inner ℝ (Lp.const 2 IBMSourceLaws.jointMeasure (correction g a T))
          ((F : IntrinsicSpace) : JointL2) := inner_add_left _ _ _
    _ = _ := congrArg₂ (fun x y : ℝ => x+y) hn hc

theorem actual_mean (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    (∫ p, IBMActualTaylorChain.limitValue (shiftedJet g a 0) T p
      ∂IBMSourceLaws.jointMeasure) = correction g a T := by
  let F : jointDerivative.domain :=
    ⟨IBMCenteredSourceRepresentation.intrinsicOne,
      LinearPMap.mem_domain_of_mem_graph IBMCenteredSourceRepresentation.joint_one_graph⟩
  have hD : jointDerivative F = 0 :=
    ((jointDerivative.image_iff F.property).mpr
      IBMCenteredSourceRepresentation.joint_one_graph).symm
  have ho : ((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun _ => (1:ℝ) := IBMGlobalVacuum.one_coeFn
  have hi : (∫ p, ((F : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure) = 1 := by
    rw [integral_congr_ae ho]
    simp
  have he : (∫ p, IBMActualTaylorChain.limitValue (shiftedJet g a 0) T p *
      ((F : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure) =
      ∫ p, IBMActualTaylorChain.limitValue (shiftedJet g a 0) T p
        ∂IBMSourceLaws.jointMeasure := by
    apply integral_congr_ae
    filter_upwards [ho] with p hp
    rw [hp,mul_one]
  have h := actual_pairing g a T F
  rw [hD,inner_zero_right,zero_add,hi,mul_one] at h
  exact he.symm.trans h

end OperatorDerivativeRewrite.Foundation.IBMSchwartzNativeTaylor
