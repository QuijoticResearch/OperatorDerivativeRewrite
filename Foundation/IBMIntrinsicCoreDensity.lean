import Foundation.IBMFiniteWeightedLaws
import Foundation.GaussianGeneratedDensity

/-! NonGaussian intrinsic IBM common-domain density via actual finite weighted
laws and the process-generated sigma algebra. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicCoreDensity
open InfiniteGaussian IBMTimeAveragedObservable IBMFiniteAverageCore IBMFiniteWeightedLaws
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local irreducible] IBMConstructedSources.ibmValue IBMConstructedSources.clockPath

abbrev PositiveTime := {t : ℝ // 0 < t}

def positiveFamily (ω : IBMSourceLaws.JointSample) (t : PositiveTime) : ℝ :=
  IBMConstructedSources.ibmValue t.val.toNNReal ω

@[instance_reducible] def positiveSigma : MeasurableSpace IBMSourceLaws.JointSample :=
  MeasurableSpace.comap positiveFamily inferInstance

theorem positiveFamily_measurable : Measurable positiveFamily := by
  apply Measurable.of_eval
  intro t
  exact IBMConstructedSources.ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)

theorem annihilator_positive_cylinder (H : JointL2) (hH : H ∈ intrinsicCoreᗮ)
    (s : Finset PositiveTime) (S : Set (s → ℝ)) (hS : MeasurableSet S) :
    (∫ ω in positiveFamily ⁻¹' cylinder s S, H ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  let t : s → ℝ := fun i => i.val.val
  have ht : ∀ i, 0 < t i := fun i => i.val.property
  have hSE : MeasurableSet ((fun x : EuclideanSpace ℝ s => x.ofLp) ⁻¹' S) :=
    hS.preimage (PiLp.continuous_ofLp (p := 2) (fun _ : s => ℝ)).measurable
  exact annihilator_finite_event H hH t ht _ hSE

theorem annihilator_positive_measurable_zero (H : JointL2) (hH : H ∈ intrinsicCoreᗮ)
    (hmH : AEStronglyMeasurable[positiveSigma] H IBMSourceLaws.jointMeasure) : H = 0 := by
  have hi : Integrable H IBMSourceLaws.jointMeasure := (Lp.memLp H).integrable (by simp)
  have hu : (∫ ω, H ω ∂IBMSourceLaws.jointMeasure) = 0 := by
    simpa [cylinder] using annihilator_positive_cylinder H hH ∅ Set.univ MeasurableSet.univ
  have hall : ∀ A : Set (PositiveTime → ℝ), MeasurableSet A →
      (∫ ω in positiveFamily ⁻¹' A, H ω ∂IBMSourceLaws.jointMeasure) = 0 := by
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => (∫ ω in positiveFamily ⁻¹' A, H ω ∂IBMSourceLaws.jointMeasure) = 0)
      (generateFrom_measurableCylinders (α := fun _ : PositiveTime => ℝ)).symm
      isPiSystem_measurableCylinders (by simp) ?_ ?_ ?_
    · intro A hA
      obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders A).mp hA
      exact annihilator_positive_cylinder H hH s S hS
    · intro A hA hz
      rw [Set.preimage_compl, setIntegral_compl (hA.preimage positiveFamily_measurable) hi,
        hu, hz, sub_self]
    · intro A hd hm hz
      rw [Set.preimage_iUnion, integral_iUnion (fun n => (hm n).preimage positiveFamily_measurable)
        (hd.mono fun i j hij => hij.preimage _) hi.integrableOn]
      simp only [hz, tsum_zero]
  have hz : H =ᵐ[IBMSourceLaws.jointMeasure] (0 : IBMSourceLaws.JointSample → ℝ) :=
    Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' ℝ positiveFamily_measurable.comap_le H
      (by norm_num) (by simp) (fun _ _ _ => hi.integrableOn)
      (by rintro A ⟨S, hS, rfl⟩ _; exact hall S hS) hmH
  exact Lp.ext (hz.trans (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := IBMSourceLaws.jointMeasure)).symm)

/-- Every actual coordinate, including zero time, is measurable in the
positive-time observation sigma algebra by EVERY-SAMPLE path continuity. -/
theorem all_coordinates_positive_measurable (t : ℝ≥0) :
    Measurable[positiveSigma] (IBMConstructedSources.ibmValue t) := by
  letI : MeasurableSpace IBMSourceLaws.JointSample := positiveSigma
  have hp (u : PositiveTime) : Measurable[positiveSigma]
      (IBMConstructedSources.ibmValue u.val.toNNReal) :=
    (measurable_pi_apply u).comp (comap_measurable positiveFamily)
  by_cases ht : 0 < t
  · simpa using hp ⟨t, ht⟩
  · have ht0 : t = 0 := le_antisymm (le_of_not_gt ht) (by exact zero_le)
    subst t
    have hm (n : ℕ) : Measurable[positiveSigma]
        (IBMConstructedSources.ibmValue (RealSteklovApprox.width n).toNNReal) :=
      hp ⟨_, RealSteklovApprox.width_pos n⟩
    apply measurable_of_tendsto_metrizable hm
    apply tendsto_pi_nhds.mpr
    intro ω
    have hw := continuous_real_toNNReal.continuousAt.tendsto.comp
      (tendsto_nhds_of_tendsto_nhdsWithin RealSteklovApprox.width_tendsto)
    simpa only [Real.toNNReal_zero, Function.comp_def] using
      (IBMConstructedSources.ibmValue_continuous ω).continuousAt.tendsto.comp hw

theorem intrinsicSigma_le_positive : IBMConditionalObservable.observableSigma
    IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath ≤ positiveSigma := by
  letI : MeasurableSpace IBMSourceLaws.JointSample := positiveSigma
  have hm : @Measurable IBMSourceLaws.JointSample (ℝ≥0 → ℝ) positiveSigma inferInstance
      (fun ω t => IBMConstructedSources.ibmValue t ω) :=
    Measurable.of_eval all_coordinates_positive_measurable
  simpa only [IBMConditionalObservable.observableSigma, IBMConstructedSources.ibmValue] using hm.comap_le

theorem intrinsic_annihilator_zero (H : JointL2) (hH : H ∈ intrinsicCoreᗮ)
    (hobs : H ∈ IntrinsicSpace) : H = 0 := by
  apply annihilator_positive_measurable_zero H hH
  exact (mem_lpMeas_iff_aestronglyMeasurable.mp hobs).mono intrinsicSigma_le_positive

theorem core_closure_eq_intrinsic : intrinsicCore.topologicalClosure = IntrinsicSpace := by
  have hle : intrinsicCore.topologicalClosure ≤ IntrinsicSpace := by
    apply Submodule.topologicalClosure_minimal
    · intro f hf
      exact ((mem_intrinsicCore_iff f).mp hf).1
    · exact IBMConditionalObservable.observableSpace_isClosed _ _
        IBMConstructedSources.sceneryPath_measurable IBMConstructedSources.clockPath_measurable
  have hz : intrinsicCore.topologicalClosureᗮ ⊓ IntrinsicSpace = ⊥ := by
    apply eq_bot_iff.mpr
    rintro H ⟨hH, hobs⟩
    apply intrinsic_annihilator_zero H _ hobs
    rwa [Submodule.orthogonal_closure] at hH
  have he := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
  simpa only [hz, sup_bot_eq] using he

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicCoreDensity
