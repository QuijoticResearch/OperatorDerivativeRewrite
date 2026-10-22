import Foundation.IBMIntrinsicRightApproach
import Foundation.AmbientNullAugmentation

/-! An explicit new right-continued ambient-null IBM filtration realizes the
verified L2 right germs. The original raw filtration and process are unchanged. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRightGermFiltration
open IBMNaturalFiltrationObstruction IBMTimeAveragedObservable IBMIntrinsicRightGerm
set_option backward.isDefEq.respectTransparency false

def augmented := AmbientNullAugmentation.filtration IBMSourceLaws.jointMeasure naturalFiltration

def germFiltration := augmented.rightCont

theorem right_continuous : germFiltration.IsRightContinuous := by
  unfold germFiltration
  infer_instance

theorem germFiltration_eq (t : ℝ≥0) :
    germFiltration t = ⨅ u > t, AmbientNullAugmentation.augment
      (naturalFiltration u) IBMSourceLaws.jointMeasure :=
  Filtration.rightCont_eq augmented t

theorem raw_le_germ (t : ℝ≥0) : naturalFiltration t ≤ germFiltration t :=
  (AmbientNullAugmentation.filtration_raw_le IBMSourceLaws.jointMeasure naturalFiltration t).trans
    (augmented.le_rightCont t)

theorem augmented_mem_iff (t : ℝ≥0) (f : JointL2) :
    AEStronglyMeasurable[AmbientNullAugmentation.augment (naturalFiltration t)
      IBMSourceLaws.jointMeasure] f IBMSourceLaws.jointMeasure ↔ f ∈ past t := by
  constructor
  · intro hf
    have hi := (Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have he := (AmbientNullAugmentation.condExp_invariant (naturalFiltration t)
      IBMSourceLaws.jointMeasure (naturalFiltration.le t) f hi).trans
        (condExp_of_aestronglyMeasurable'
          (AmbientNullAugmentation.le_ambient (naturalFiltration t) IBMSourceLaws.jointMeasure) hf hi)
    exact (stronglyMeasurable_condExp.aestronglyMeasurable).congr he
  · intro hf
    exact hf.mono (AmbientNullAugmentation.raw_le (naturalFiltration t)
      IBMSourceLaws.jointMeasure (naturalFiltration.le t))

theorem representative_measurable (t : ℝ≥0) (f : JointL2) (hf : f ∈ rightPast t) :
    Measurable[germFiltration t] f := by
  apply Measurable.of_comap_le
  rw [germFiltration_eq]
  apply le_iInf₂
  intro u hu
  exact (AmbientNullAugmentation.measurable_of_raw_aestronglyMeasurable
    (naturalFiltration u) IBMSourceLaws.jointMeasure (Lp.stronglyMeasurable f).measurable
      ((rightPast_le_past hu) hf)).comap_le

def germPast (t : ℝ≥0) : Submodule ℝ JointL2 :=
  lpMeas ℝ ℝ (germFiltration t) 2 IBMSourceLaws.jointMeasure

theorem germPast_eq (t : ℝ≥0) : germPast t = rightPast t := by
  apply le_antisymm
  · rw [rightPast_eq_iInf]
    apply le_iInf
    intro u f hf
    have hle : germFiltration t ≤ AmbientNullAugmentation.augment
        (naturalFiltration u.val) IBMSourceLaws.jointMeasure := by
      rw [germFiltration_eq]
      exact iInf₂_le u.val u.property
    exact (augmented_mem_iff u.val f).mp (hf.mono hle)
  · intro f hf
    exact (representative_measurable t f hf).stronglyMeasurable.aestronglyMeasurable

theorem rightValue_adapted : StronglyAdapted germFiltration rightValue := by
  intro t
  exact (representative_measurable t (rightLimitClass t) (rightLimitClass_mem t)).stronglyMeasurable

theorem ibm_adapted : StronglyAdapted germFiltration IBMConstructedSources.ibmValue := by
  intro t
  exact (point_stronglyAdapted t).mono (raw_le_germ t)

theorem projection_ae (t : ℝ≥0) (f : JointL2) :
    (rightPast t).starProjection f =ᵐ[IBMSourceLaws.jointMeasure]
      IBMSourceLaws.jointMeasure[f | germFiltration t] := by
  have he := (Lp.memLp f).condExpL2_ae_eq_condExp (𝕜 := ℝ) (germFiltration.le t)
  have hg : lpMeas ℝ ℝ (germFiltration t) 2 IBMSourceLaws.jointMeasure = rightPast t := germPast_eq t
  simp only [Lp.toLp_coeFn, condExpL2,
    ← Submodule.starProjection_apply] at he
  simpa only [hg] using he

theorem rightPast_mono : Monotone rightPast := by
  intro s t hst
  rw [rightPast_eq_iInf t]
  exact le_iInf fun u : Ioi t => rightPast_le_past (hst.trans_lt u.property)

theorem project_rightLimit {s t : ℝ≥0} (hst : s ≤ t) :
    (rightPast s).starProjection (rightLimitClass t) = rightLimitClass s := by
  calc
    _ = (rightPast s).starProjection ((rightPast t).starProjection
        (IBMIntrinsicQuadraticMartingale.valueClass (t + 1) : JointL2)) := rfl
    _ = (rightPast s).starProjection
        (IBMIntrinsicQuadraticMartingale.valueClass (t + 1) : JointL2) :=
      DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le
        (rightPast_mono hst)) _
    _ = _ := (rightLimitClass_horizon (hst.trans_lt (by simp))).symm

/-- A genuine actual martingale under the EXPLICIT new right-continued
ambient-null filtration. This does not claim a modification of the raw M. -/
theorem actual_martingale : Martingale rightValue germFiltration IBMSourceLaws.jointMeasure := by
  refine ⟨rightValue_adapted, ?_⟩
  intro s t hst
  have he := projection_ae s (rightLimitClass t)
  rw [project_rightLimit hst] at he
  exact he.symm

end OperatorDerivativeRewrite.Foundation.IBMRightGermFiltration
