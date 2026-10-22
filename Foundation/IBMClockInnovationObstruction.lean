import Foundation.IBMClockSignSymmetry
import Foundation.IBMPastCoreDensity
import Foundation.IBMClockConditionalCorrection
import Foundation.L2GeneratedSubspace

/-! The actual signed Brownian clock is invisible to the entire IBM observation
sigma algebra. Its first-chaos projection cannot be used as an IBM innovation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockInnovationObstruction
open InfiniteGaussian GaussianSampleReflection IBMClockSignSymmetry
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMClockConditionalCorrection
set_option backward.isDefEq.respectTransparency false
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
attribute [local irreducible] IBMConstructedSources.ibmValue IBMConstructedSources.clockPath

def jointReflection : JointL2 →ₗᵢ[ℝ] JointL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ reflectClock reflectClock_preserving

theorem jointReflection_ae (f : JointL2) :
    jointReflection f =ᵐ[IBMSourceLaws.jointMeasure] fun ω => f (reflectClock ω) :=
  Lp.coeFn_compMeasurePreserving f reflectClock_preserving

theorem observable_fixed (f : JointL2) (hf : f ∈ IntrinsicSpace) : jointReflection f = f := by
  have hm0 : AEStronglyMeasurable[IBMConditionalObservable.observableSigma
      IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath]
      f IBMSourceLaws.jointMeasure := mem_lpMeas_iff_aestronglyMeasurable.mp hf
  have hm : AEStronglyMeasurable[MeasurableSpace.comap
      (fun ω t => IBMConstructedSources.ibmValue t ω) inferInstance] f IBMSourceLaws.jointMeasure := by
    have hs : IBMConditionalObservable.observableSigma
        IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath =
          MeasurableSpace.comap (fun ω t => IBMConstructedSources.ibmValue t ω) inferInstance := by
      unfold IBMConditionalObservable.observableSigma IBMConstructedSources.ibmValue
      rfl
    rw [hs] at hm0
    exact hm0
  obtain ⟨g, hg, he⟩ := hm.stronglyMeasurable_mk.exists_eq_measurable_comp
  have hfg : f =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => g (fun t => IBMConstructedSources.ibmValue t ω) := by
    have h := hm.ae_eq_mk
    rw [he] at h
    exact h
  apply Lp.ext
  filter_upwards [jointReflection_ae f, hfg,
    reflectClock_preserving.quasiMeasurePreserving.ae_eq_comp hfg,
    ibm_reflect_simultaneous] with ω hr ho hn hi
  simp only [Function.comp_def] at hn
  rw [hr, hn, ho]
  exact congrArg g (funext hi)

theorem odd_inner_zero (F : JointL2) (hF : jointReflection F = -F)
    (f : JointL2) (hf : f ∈ IntrinsicSpace) : inner ℝ F f = 0 := by
  have h := jointReflection.inner_map_map F f
  rw [hF, observable_fixed f hf, inner_neg_left] at h
  linarith

theorem nonzero_odd_not_observable (F : JointL2) (hF : jointReflection F = -F) (hn : F ≠ 0) :
    F ∉ IntrinsicSpace := by
  intro hf
  exact hn (inner_self_eq_zero.mp (odd_inner_zero F hF F hf))

theorem odd_condExpL2_zero (T : ℝ≥0) (F : JointL2) (hF : jointReflection F = -F) :
    (condExpL2 ℝ ℝ (naturalFiltration.le T) F : JointL2) = 0 := by
  let : CompleteSpace (past T) := (past_closed T).completeSpace_coe
  change (past T).starProjection F = 0
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (past T).zero_mem
  intro f hf
  rw [sub_zero]
  exact odd_inner_zero F hF f (IBMPastCoreDensity.past_le_intrinsic T hf)

theorem clockLift_reflection (f : GaussianL2) :
    jointReflection (clockLift f) = clockLift (reflection f) := by
  apply Lp.ext
  filter_upwards [jointReflection_ae (clockLift f),
    reflectClock_preserving.quasiMeasurePreserving.ae_eq_comp (clockLift_coeFn f),
    clockLift_coeFn (reflection f),
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      (reflection_ae f)] with ω hj hc hl hr
  simp only [Function.comp_def] at hc hr
  rw [hj, hc, hl, hr]
  rfl

theorem clock_firstChaos_condExp_zero (T : ℝ≥0) (h : CoefficientSpace) :
    (condExpL2 ℝ ℝ (naturalFiltration.le T) (clockLift (firstChaosEmbedding h)) : JointL2) = 0 := by
  apply odd_condExpL2_zero
  rw [clockLift_reflection, reflection_firstChaos, map_neg]

theorem clock_class_actual_ae (t : ℝ≥0) :
    clockLift (GaussianTimeProcess.wienerL2 t) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => IBMConstructedSources.clockPath ω.2 t := by
  exact (clockLift_coeFn _).trans
    ((measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      (IBMConstructedSources.clockPath_coordinate_ae t)).symm

theorem signed_clock_condExp_zero (T t : ℝ≥0) :
    IBMSourceLaws.jointMeasure[(fun ω => IBMConstructedSources.clockPath ω.2 t) |
      naturalFiltration T] =ᵐ[IBMSourceLaws.jointMeasure] fun _ => (0 : ℝ) := by
  let F : JointL2 := clockLift (GaussianTimeProcess.wienerL2 t)
  have hz : (condExpL2 ℝ ℝ (naturalFiltration.le T) F : JointL2) = 0 :=
    clock_firstChaos_condExp_zero T (SeparableHilbertEmbedding.hilbertEmbedding
      GaussianTimeHilbert.TimeHilbert (GaussianTimeHilbert.timeVector t))
  have hc : (condExpL2 ℝ ℝ (naturalFiltration.le T) F : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      IBMSourceLaws.jointMeasure[F | naturalFiltration T] := by
    simpa only [Lp.toLp_coeFn] using (Lp.memLp F).condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (naturalFiltration.le T)
  have he : IBMSourceLaws.jointMeasure[F | naturalFiltration T] =ᵐ[IBMSourceLaws.jointMeasure]
      fun _ => (0 : ℝ) := by
    rw [hz] at hc
    exact hc.symm.trans (Lp.coeFn_zero ℝ 2 IBMSourceLaws.jointMeasure)
  exact (condExp_congr_ae (clock_class_actual_ae t).symm).trans he

theorem clock_class_not_in_past (T t : ℝ≥0) (ht : 0 < t) :
    clockLift (GaussianTimeProcess.wienerL2 t) ∉ past T := by
  intro hm
  let : CompleteSpace (past T) := (past_closed T).completeSpace_coe
  have h0 : (past T).starProjection (clockLift (GaussianTimeProcess.wienerL2 t)) = 0 :=
    clock_firstChaos_condExp_zero T (SeparableHilbertEmbedding.hilbertEmbedding
      GaussianTimeHilbert.TimeHilbert (GaussianTimeHilbert.timeVector t))
  rw [Submodule.starProjection_eq_self_iff.mpr hm] at h0
  have hw : GaussianTimeProcess.wienerL2 t = 0 := clockLift.injective (h0.trans clockLift.map_zero.symm)
  have hn := GaussianTimeProcess.wienerL2_sub_norm_sq 0 t (show 0 ≤ t from bot_le)
  have he : (t : ℝ) = 0 := by simpa [hw, GaussianTimeProcess.wienerL2_zero] using hn.symm
  exact (ne_of_gt ht) (by exact_mod_cast he)

theorem signed_clock_not_measurable (T t : ℝ≥0) (ht : 0 < t) :
    ¬ AEStronglyMeasurable[naturalFiltration T]
      (fun ω => IBMConstructedSources.clockPath ω.2 t) IBMSourceLaws.jointMeasure := by
  intro hm
  apply clock_class_not_in_past T t ht
  exact hm.congr (clock_class_actual_ae t).symm

theorem signed_clock_not_stronglyAdapted :
    ¬ StronglyAdapted naturalFiltration
      (fun t ω => IBMConstructedSources.clockPath ω.2 t) := by
  intro h
  exact signed_clock_not_measurable 1 1 (by norm_num) (h 1).aestronglyMeasurable

end OperatorDerivativeRewrite.Foundation.IBMClockInnovationObstruction
