import Foundation.IBMSceneryUniversalPrediction
import Foundation.IBMClockInitialEnlargement
import Foundation.GeneratedFamilyModification
import Foundation.GaussianSmallTimeCutoff
import Foundation.IBMIntrinsicRightApproach

/-! The actual reflected-clock IBM initial right germ consists of constants.
Coordinatewise AE replacement is used per measurable functional; no simultaneous
uncountable-coordinate null-event assertion is made. Product sections retain
the original Brownian clock past and the original joint measure. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMInitialGermTriviality
open InfiniteGaussian IBMConstructedSources

theorem clock_section {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : MeasurableSpace β) (H : α × β → ℝ) (g : β → ℝ)
    (hH : AEStronglyMeasurable[mα.prod n] H (@Measure.prod α β mα mβ μ ν))
    (he : H =ᵐ[@Measure.prod α β mα mβ μ ν] fun p => g p.2) : AEStronglyMeasurable[n] g ν := by
  let : MeasurableSpace β := mβ
  obtain ⟨h, hsm, heh⟩ := hH
  have hprod : h =ᵐ[@Measure.prod α β mα mβ μ ν] fun p => g p.2 := heh.symm.trans he
  obtain ⟨x, hx⟩ := (Measure.ae_ae_of_ae_prod hprod).exists
  have hs : StronglyMeasurable[n] (fun y => h (x,y)) := by
    let : MeasurableSpace β := n
    exact hsm.comp_measurable (measurable_const.prodMk measurable_id)
  have hx' : (fun y => h (x,y)) =ᵐ[ν] g := hx
  exact ⟨_,hs,hx'.symm⟩

theorem actual_past_raw (T : ℝ≥0) (G : IBMTimeAveragedObservable.JointL2)
    (hG : G ∈ IBMNaturalFiltrationObstruction.past T) :
    AEStronglyMeasurable[IBMClockInitialEnlargement.rawEnlargement T] G
      IBMSourceLaws.jointMeasure := by
  have hv (r : Iic T) :
      AEStronglyMeasurable[IBMClockInitialEnlargement.rawEnlargement T]
        (ibmValue r.val) IBMSourceLaws.jointMeasure :=
    (IBMClockInitialEnlargement.ibm_raw_aestronglyMeasurable r.val).mono
      (IBMClockInitialEnlargement.rawEnlargement.mono r.property)
  let X : IBMSourceLaws.JointSample → Iic T → ℝ := fun ω r => ibmValue r.val ω
  let Y : IBMSourceLaws.JointSample → Iic T → ℝ := fun ω r => (hv r).mk (ibmValue r.val) ω
  have hXY (r : Iic T) : (fun ω => X ω r) =ᵐ[IBMSourceLaws.jointMeasure] fun ω => Y ω r :=
    (hv r).ae_eq_mk
  have hY : Measurable[IBMClockInitialEnlargement.rawEnlargement T] Y := by
    let : MeasurableSpace IBMSourceLaws.JointSample := IBMClockInitialEnlargement.rawEnlargement T
    exact Measurable.of_eval fun r => (hv r).stronglyMeasurable_mk.measurable
  have hX : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] G
      IBMSourceLaws.jointMeasure := by
    change AEStronglyMeasurable[IBMNaturalFiltrationObstruction.naturalFiltration T] G
      IBMSourceLaws.jointMeasure at hG
    rw [IBMNaturalFiltrationObstruction.naturalFiltration,
      Filtration.natural_eq_comap ibmValue
        IBMNaturalFiltrationObstruction.point_stronglyMeasurable T] at hG
    exact hG
  exact (GeneratedFamilyModification.aestronglyMeasurable_transfer
    IBMSourceLaws.jointMeasure X Y hXY hX).mono hY.comap_le

theorem germ_clock_past (G : IBMTimeAveragedObservable.JointL2)
    (hG : G ∈ IBMIntrinsicRightGerm.rightPast 0) (T : ℝ≥0) (hT : 0 < T) :
    IBMGlobalVacuum.factorMean (IBMIntrinsicOperators.sourceUnitary G) ∈
      GaussianConditionalIto.pastL2 T := by
  have hr := actual_past_raw T G (IBMIntrinsicRightGerm.rightPast_le_past hT hG)
  exact clock_section gaussianProduct gaussianProduct (GaussianTimeProcess.naturalFiltration T)
    G (IBMGlobalVacuum.factorMean (IBMIntrinsicOperators.sourceUnitary G)) hr
    (IBMSceneryUniversalPrediction.germ_clock_actual G hG)

end OperatorDerivativeRewrite.Foundation.IBMInitialGermTriviality


namespace OperatorDerivativeRewrite.Foundation.IBMInitialGermTriviality
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMGlobalVacuum
open IBMIntrinsicRightApproach
attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative

-- Use the existing strictly positive dyadic approach.
theorem germ_constant (G : JointL2) (hG : G ∈ IBMIntrinsicRightGerm.rightPast 0) :
    ∃ c : ℝ, G =ᵐ[IBMSourceLaws.jointMeasure] fun _ => c := by
  let m := factorMean (sourceUnitary G)
  have hm := GaussianSmallTimeCutoff.constant_of_shrinking_pasts m (approach 0)
    (approach_tendsto 0) (fun n => germ_clock_past G hG _ (approach_positive 0 n))
  let c := ∫ ω, m ω ∂gaussianProduct
  have hm' : m = c • InfiniteGaussian.gaussianOne := hm
  have ha : m =ᵐ[gaussianProduct] fun _ => c := by
    rw [hm']
    filter_upwards [Lp.coeFn_smul c InfiniteGaussian.gaussianOne,
      InfiniteGaussian.gaussianOne_coeFn] with ω hs ho
    rw [hs]
    change c * InfiniteGaussian.gaussianOne ω = c
    rw [ho,mul_one]
  have hmp := measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)
  have hs := hmp.quasiMeasurePreserving.ae_eq_comp ha
  exact ⟨c, (IBMSceneryUniversalPrediction.germ_clock_actual G hG).trans hs⟩

theorem initial_projection_zero (F : JointL2)
    (hF : (∫ ω, F ω ∂IBMSourceLaws.jointMeasure) = 0) :
    (IBMIntrinsicRightGerm.rightPast 0).starProjection F = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (IBMIntrinsicRightGerm.rightPast 0).zero_mem
  intro g hg
  obtain ⟨c, hc⟩ := germ_constant g hg
  rw [sub_zero, L2.inner_def]
  calc
    _ = ∫ ω, F ω * c ∂IBMSourceLaws.jointMeasure := by
      apply integral_congr_ae
      filter_upwards [hc] with ω hω
      rw [hω, Real.inner_apply]
    _ = 0 := by rw [integral_mul_const, hF, zero_mul]

-- Remove the initial channel for all centered original observables,
-- while retaining the genuine target-indexed integral and its exact domains.
theorem centered_target_reconstruction (f : IntrinsicSpace)
    (hf : (∫ ω, (f : JointL2) ω ∂IBMSourceLaws.jointMeasure) = 0) :
    IBMFullPredictableIntegral.integral (f : JointL2)
      ((IBMFullPredictableIntegral.integral (f : JointL2)).toContinuousLinearMap.adjoint
        (f : JointL2)) = (f : JointL2) := by
  have h := IBMTerminalSelfRepresentation.target_indexed_reconstruction f
  have hz : IBMObservedTerminalMartingale.channelClass (f : JointL2) 0 = 0 :=
    initial_projection_zero _ hf
  simpa only [hz, sub_zero] using h

-- Stronger all-target scalar initial channel, not only a centered corollary.
-- The scalar formula holds on the entire original joint L2 space.
theorem initial_projection_expectation (F : JointL2) :
    (IBMIntrinsicRightGerm.rightPast 0).starProjection F =
      (∫ ω, F ω ∂IBMSourceLaws.jointMeasure) • IBMGlobalVacuum.one := by
  let c := ∫ ω, F ω ∂IBMSourceLaws.jointMeasure
  have ho : IBMGlobalVacuum.one ∈ IBMIntrinsicRightGerm.rightPast 0 := by
    apply IBMIntrinsicRightGerm.past_le_rightPast 0
    change AEStronglyMeasurable[IBMNaturalFiltrationObstruction.naturalFiltration 0]
      IBMGlobalVacuum.one IBMSourceLaws.jointMeasure
    exact aestronglyMeasurable_const.congr IBMGlobalVacuum.one_coeFn.symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((IBMIntrinsicRightGerm.rightPast 0).smul_mem c ho)
  intro g hg
  obtain ⟨d, hd⟩ := germ_constant g hg
  rw [L2.inner_def]
  calc
    _ = ∫ ω, (F ω - c) * d ∂IBMSourceLaws.jointMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub F (c • IBMGlobalVacuum.one),
        Lp.coeFn_smul c IBMGlobalVacuum.one, IBMGlobalVacuum.one_coeFn, hd]
        with ω hs hm ho hg
      rw [Real.inner_apply, hs, hg]
      simp only [Pi.sub_apply, hm, Pi.smul_apply, ho, smul_eq_mul, mul_one]
    _ = 0 := by
      rw [integral_mul_const, integral_sub
        ((Lp.memLp F).integrable (by norm_num)) (integrable_const c), integral_const]
      simp [c]

theorem target_reconstruction (f : IntrinsicSpace) :
    IBMFullPredictableIntegral.integral (f : JointL2)
      ((IBMFullPredictableIntegral.integral (f : JointL2)).toContinuousLinearMap.adjoint
        (f : JointL2)) = (f : JointL2) -
          (∫ ω, (f : JointL2) ω ∂IBMSourceLaws.jointMeasure) • IBMGlobalVacuum.one := by
  rw [IBMTerminalSelfRepresentation.target_indexed_reconstruction,
    IBMObservedTerminalMartingale.channelClass, initial_projection_expectation]

theorem native_target_reconstruction (f : IBMJointIntrinsicDerivative.jointDerivative.domain) :
    let F : JointL2 := (f : IntrinsicSpace)
    IBMFullPredictableIntegral.integral F
      ((IBMNativePredictableTransfer.transfer F).adjoint
        (IBMJointIntrinsicDerivative.jointDerivative f)) = F -
          (∫ ω, F ω ∂IBMSourceLaws.jointMeasure) • IBMGlobalVacuum.one := by
  dsimp only
  have h := IBMNativePredictableTransfer.native_gradient_adjoint_identity
    ((f : IntrinsicSpace) : JointL2) f
  exact (congrArg (IBMFullPredictableIntegral.integral ((f : IntrinsicSpace) : JointL2)) h).trans
    (target_reconstruction (f : IntrinsicSpace))

end OperatorDerivativeRewrite.Foundation.IBMInitialGermTriviality
