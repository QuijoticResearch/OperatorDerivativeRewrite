import Foundation.IBMBrownianDyadicControl
import Foundation.IBMConstructedChainRule
import Foundation.IBMConditionalFiniteDim

/-! Unconditional continuous Brownian source modifications and their actual
IBM composition on the original independent Gaussian product factors. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.IBMConstructedSources
open InfiniteGaussian IBMSourceLaws IBMBrownianDyadicControl
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable
attribute [local irreducible] GaussianContinuousModification.field IBMDyadicExtension.field

def sceneryPath : SampleSpace → C(ℝ, ℝ) :=
  GaussianContinuousModification.path IBMContinuousScenery.sourceScenery (7/8)
    (by norm_num) (by norm_num)

theorem sceneryPath_measurable : Measurable sceneryPath :=
  GaussianContinuousModification.path_measurable _ _ _ _

theorem sceneryPath_coordinate_ae (r : ℝ) :
    (fun ω => sceneryPath ω r) =ᵐ[gaussianProduct] sceneryBase r :=
  GaussianContinuousModification.field_coordinate_ae _ _ _ _
    IBMContinuousScenery.sourceScenery_continuous scenery_good r

def clockPath (ω : SampleSpace) : C(ℝ≥0, ℝ) :=
  ⟨fun t => GaussianContinuousModification.path clockClass (7/8)
      (by norm_num) (by norm_num) ω t,
    (GaussianContinuousModification.path clockClass (7/8)
      (by norm_num) (by norm_num) ω).continuous.comp NNReal.continuous_coe⟩

theorem clockPath_coordinate_ae (t : ℝ≥0) :
    (fun ω => clockPath ω t) =ᵐ[gaussianProduct] GaussianTimeProcess.process t := by
  have h := GaussianContinuousModification.field_coordinate_ae clockClass (7/8)
    (by norm_num) (by norm_num) clockClass_continuous clock_good t
  simpa only [clockPath, GaussianContinuousModification.path, ContinuousMap.coe_mk,
    clockClass, Real.toNNReal_coe, GaussianTimeProcess.process] using h

theorem clockPath_measurable : Measurable clockPath := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (ContinuousMap.measurable_eval (t : ℝ)).comp
    (GaussianContinuousModification.path_measurable clockClass (7/8) (by norm_num) (by norm_num))

/-- An actual continuous Brownian clock, without a supplied path hypothesis. -/
theorem clock_isBrownian : IsBrownianReal (fun t ω => clockPath ω t) gaussianProduct :=
  ⟨GaussianTimeProcess.process_isPreBrownian.congr
      (fun t => (clockPath_coordinate_ae t).symm),
    Filter.Eventually.of_forall (fun ω => (clockPath ω).continuous)⟩

theorem scenery_isGaussianProcess : IsGaussianProcess (fun r ω => sceneryPath ω r) gaussianProduct :=
  sceneryBase_isGaussianProcess.congr (fun r => (sceneryPath_coordinate_ae r).symm)

theorem sceneryPath_covariance (s t : ℝ) :
    cov[(fun ω => sceneryPath ω s), (fun ω => sceneryPath ω t); gaussianProduct] =
      (|s|+|t|-|t-s|)/2 := by
  have hs := sceneryPath_coordinate_ae s
  have ht := sceneryPath_coordinate_ae t
  have hEs := integral_congr_ae hs
  have hEt := integral_congr_ae ht
  calc
    _ = cov[sceneryBase s, sceneryBase t; gaussianProduct] := by
      unfold covariance
      apply integral_congr_ae
      filter_upwards [hs, ht] with ω hωs hωt
      rw [hωs, hωt, hEs, hEt]
    _ = _ := sceneryBase_covariance s t

theorem positiveScenery_isBrownian :
    IsBrownianReal (fun t : ℝ≥0 => fun ω => sceneryPath ω t) gaussianProduct := by
  refine ⟨?_, Filter.Eventually.of_forall fun ω =>
    (sceneryPath ω).continuous.comp NNReal.continuous_coe⟩
  apply (scenery_isGaussianProcess.comp_right (fun t : ℝ≥0 => (t : ℝ))).isPreBrownianReal_of_covariance
  · intro t
    simp only [Function.comp_def]
    rw [integral_congr_ae (sceneryPath_coordinate_ae t)]
    exact GaussianHilbertProcess.isonormal_integral _
  · intro s t hst
    simp only [Function.comp_def]
    have hs0 : (0 : ℝ) ≤ s := s.property
    have ht0 : (0 : ℝ) ≤ t := t.property
    rw [sceneryPath_covariance]
    simp only [abs_of_nonneg hs0, abs_of_nonneg ht0,
      abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst))]
    ring

theorem negativeScenery_isBrownian :
    IsBrownianReal (fun t : ℝ≥0 => fun ω => sceneryPath ω (-(t : ℝ))) gaussianProduct := by
  refine ⟨?_, Filter.Eventually.of_forall fun ω =>
    (sceneryPath ω).continuous.comp NNReal.continuous_coe.neg⟩
  apply (scenery_isGaussianProcess.comp_right (fun t : ℝ≥0 => -(t : ℝ))).isPreBrownianReal_of_covariance
  · intro t
    simp only [Function.comp_def]
    rw [integral_congr_ae (sceneryPath_coordinate_ae (-(t : ℝ)))]
    exact GaussianHilbertProcess.isonormal_integral _
  · intro s t hst
    simp only [Function.comp_def]
    have hs0 : (0 : ℝ) ≤ s := s.property
    have ht0 : (0 : ℝ) ≤ t := t.property
    rw [sceneryPath_covariance]
    simp only [abs_neg, abs_of_nonneg hs0, abs_of_nonneg ht0]
    have hh : -(t : ℝ)-(-(s : ℝ)) ≤ 0 := by
      exact sub_nonpos.mpr (neg_le_neg (show (s : ℝ) ≤ t from hst))
    rw [abs_of_nonpos hh]
    ring

/-- The positive and negative branches are independent as whole coordinate
processes, not merely pairwise independent at a single time. -/
theorem scenery_branches_independent :
    IndepFun (fun ω => fun t : ℝ≥0 => sceneryPath ω t)
      (fun ω => fun t : ℝ≥0 => sceneryPath ω (-(t : ℝ))) gaussianProduct := by
  have hjoint : IsGaussianProcess
      (Sum.elim (fun t : ℝ≥0 => fun ω => sceneryPath ω t)
        (fun t : ℝ≥0 => fun ω => sceneryPath ω (-(t : ℝ)))) gaussianProduct := by
    convert scenery_isGaussianProcess.comp_right
      (Sum.elim (fun t : ℝ≥0 => (t : ℝ)) (fun t : ℝ≥0 => -(t : ℝ))) using 1
    funext q; cases q <;> rfl
  apply hjoint.indepFun_of_covariance_eq_zero
    (fun t => ((ContinuousMap.measurable_eval _).comp sceneryPath_measurable).aemeasurable)
    (fun t => ((ContinuousMap.measurable_eval _).comp sceneryPath_measurable).aemeasurable)
  intro s t
  rw [sceneryPath_covariance]
  have hs : |(s : ℝ)| = s := abs_of_nonneg s.property
  have ht : |(t : ℝ)| = t := abs_of_nonneg t.property
  have hs0 : (0 : ℝ) ≤ s := s.property
  have ht0 : (0 : ℝ) ≤ t := t.property
  have hh : |-(t : ℝ)-(s : ℝ)| = -(-(t : ℝ)-(s : ℝ)) :=
    abs_of_nonpos (by linarith)
  simp only [hs, abs_neg, ht, hh]
  ring

/-- Full continuous source paths retain independence on their original factors. -/
theorem sources_independent :
    IndepFun (fun ω : JointSample => sceneryPath ω.1)
      (fun ω : JointSample => clockPath ω.2) jointMeasure :=
  IBMContinuousComposition.sources_independent _ _ sceneryPath_measurable clockPath_measurable

def ibmPath : JointSample → C(ℝ≥0, ℝ) := IBMContinuousComposition.path sceneryPath clockPath

def ibmValue : ℝ≥0 → JointSample → ℝ := IBMContinuousComposition.value sceneryPath clockPath

theorem ibmPath_measurable : Measurable ibmPath :=
  IBMContinuousComposition.path_measurable _ _ sceneryPath_measurable clockPath_measurable

theorem ibmValue_continuous (ω : JointSample) : Continuous (fun t => ibmValue t ω) :=
  IBMContinuousComposition.path_continuous _ _ ω

theorem ibmValue_jointly_measurable : Measurable (fun p : ℝ≥0 × JointSample => ibmValue p.1 p.2) :=
  IBMContinuousComposition.value_jointly_measurable _ _ sceneryPath_measurable clockPath_measurable

/-- Exact pointwise composition, now instantiated with constructed sources. -/
theorem ibmValue_eq (t : ℝ≥0) (ω : JointSample) :
    ibmValue t ω = sceneryPath ω.1 |clockPath ω.2 t| := rfl

def mollifiedPath (n : ℕ) (i : Fin 3) : JointSample → C(ℝ≥0, ℝ) :=
  IBMContinuousComposition.path (IBMDyadicExtension.path n i) clockPath

def mollifiedValue (n : ℕ) (i : Fin 3) : ℝ≥0 → JointSample → ℝ :=
  IBMContinuousComposition.value (IBMDyadicExtension.path n i) clockPath

theorem mollifiedValue_jointly_measurable (n : ℕ) (i : Fin 3) :
    Measurable (fun p : ℝ≥0 × JointSample => mollifiedValue n i p.1 p.2) :=
  IBMContinuousComposition.value_jointly_measurable _ _
    (IBMDyadicExtension.path_measurable n i) clockPath_measurable

theorem mollifiedValue_continuous (n : ℕ) (i : Fin 3) (ω : JointSample) :
    Continuous (fun t => mollifiedValue n i t ω) :=
  IBMContinuousComposition.path_continuous _ _ ω

theorem mollifiedValue_ae_original (n : ℕ) (i : Fin 3) (t : ℝ≥0) :
    mollifiedValue n i t =ᵐ[jointMeasure] IBMPointwiseEvaluation.value n i t := by
  have hclock : ∀ᵐ ω ∂jointMeasure, clockPath ω.2 t = GaussianTimeProcess.process t ω.2 :=
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae
      (clockPath_coordinate_ae t)
  filter_upwards [hclock] with ω hω
  change IBMDyadicExtension.field n i ω.1 |clockPath ω.2 t| =
    IBMDyadicExtension.field n i ω.1 |GaussianTimeProcess.process t ω.2|
  rw [hω]

theorem mollifiedValue_memLp (n : ℕ) (i : Fin 3) (t : ℝ≥0) :
    MemLp (mollifiedValue n i t) 2 jointMeasure :=
  (IBMPointwiseEvaluation.value_memLp n i t).ae_eq (mollifiedValue_ae_original n i t).symm

end OperatorDerivativeRewrite.Foundation.IBMConstructedSources
