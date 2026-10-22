import Foundation.IBMPredictableIntegralObservable

/-! Actual observable IBM L2 is recovered by increasing finite horizons. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMObservableHorizonLimit
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction
open IBMIntrinsicRightGerm IBMPredictableIntegralObservable
set_option backward.isDefEq.respectTransparency false

abbrev observationSigma := IBMConditionalObservable.observableSigma
  IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath

theorem raw_le_observation (t : ℝ≥0) : naturalFiltration t ≤ observationSigma := by
  change (⨆ s ≤ t, MeasurableSpace.comap (IBMConstructedSources.ibmValue s) inferInstance) ≤ _
  apply iSup₂_le
  intro s _
  exact ((measurable_pi_apply s).comp
    (comap_measurable (fun ω r => IBMConstructedSources.ibmValue r ω))).comap_le

theorem observation_eq_all_past : observationSigma = ⨆ n : ℕ, naturalFiltration n := by
  apply le_antisymm
  · letI : MeasurableSpace IBMSourceLaws.JointSample := ⨆ n : ℕ, naturalFiltration n
    have hm : Measurable (fun ω r => IBMConstructedSources.ibmValue r ω) := by
      apply Measurable.of_eval
      intro r
      obtain ⟨n, hn⟩ := exists_nat_ge (r : ℝ)
      have hr : r ≤ (n : ℝ≥0) := by exact_mod_cast hn
      exact (point_stronglyAdapted r).measurable.mono
        ((naturalFiltration.mono hr).trans (le_iSup (fun n : ℕ => naturalFiltration n) n)) le_rfl
    exact hm.comap_le
  · exact iSup_le fun n => raw_le_observation n

theorem raw_projection_tendsto (f : IntrinsicSpace) :
    Tendsto (fun n : ℕ => (past n).starProjection (f : JointL2)) atTop (𝓝 (f : JointL2)) := by
  letI : ∀ n : ℕ, Fact (naturalFiltration n ≤
      (inferInstance : MeasurableSpace IBMSourceLaws.JointSample)) := fun n => ⟨naturalFiltration.le _⟩
  letI : ∀ n : ℕ, (past n).HasOrthogonalProjection := fun n => by unfold past; infer_instance
  have hp := Submodule.starProjection_tendsto_closure_iSup (fun n : ℕ => past n)
    (fun i j hij g hg => hg.mono (naturalFiltration.mono (by exact_mod_cast hij))) (f : JointL2)
  have hm := tendstoInMeasure_of_tendsto_Lp hp
  have hc := tendsto_eLpNorm_condExp (μ := IBMSourceLaws.jointMeasure)
    (ℱ := IBMIntrinsicMartingaleGrid.gridFiltration (fun n : ℕ => (n : ℝ≥0))
      (fun i j h => by change (i : ℝ≥0) ≤ (j : ℝ≥0); exact_mod_cast h)) (f : IBMSourceLaws.JointSample → ℝ)
  change Tendsto (fun n : ℕ => eLpNorm
    (IBMSourceLaws.jointMeasure[(f : JointL2) | naturalFiltration n] -
      IBMSourceLaws.jointMeasure[(f : JointL2) | ⨆ n : ℕ, naturalFiltration n])
      1 IBMSourceLaws.jointMeasure) atTop (𝓝 0) at hc
  have hf : AEStronglyMeasurable[observationSigma] (f : JointL2) IBMSourceLaws.jointMeasure := f.property
  have he := condExp_of_aestronglyMeasurable'
    (IBMConditionalObservable.observableSigma_le _ _
      IBMConstructedSources.sceneryPath_measurable IBMConstructedSources.clockPath_measurable)
    hf ((Lp.memLp (f : JointL2)).integrable (by norm_num))
  rw [← observation_eq_all_past] at hc
  have hc' := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) hc
  have heq := tendstoInMeasure_ae_unique hm
    (hc'.congr (fun n => (IBMCofinalPast.projection_ae n (f : JointL2)).symm) he)
  have hx : (⨆ n : ℕ, past n).topologicalClosure.starProjection (f : JointL2) = (f : JointL2) := Lp.ext heq
  rwa [hx] at hp

theorem all_past_closure : (⨆ n : ℕ, past n).topologicalClosure = IntrinsicSpace := by
  apply le_antisymm
  · exact (⨆ n : ℕ, past n).topologicalClosure_minimal
      (iSup_le fun n => IBMPastCoreDensity.past_le_intrinsic n)
      (IBMConditionalObservable.observableSpace_isClosed _ _
        IBMConstructedSources.sceneryPath_measurable IBMConstructedSources.clockPath_measurable)
  · intro f hf
    apply (⨆ n : ℕ, past n).isClosed_topologicalClosure.mem_of_tendsto
      (raw_projection_tendsto ⟨f,hf⟩)
    exact Eventually.of_forall fun n => (⨆ n : ℕ, past n).le_topologicalClosure
      ((le_iSup (fun n : ℕ => past n) n) ((past n).starProjection_apply_mem f))

theorem all_right_past_closure :
    (⨆ n : ℕ, rightPast n).topologicalClosure = IntrinsicSpace := by
  apply le_antisymm
  · exact (⨆ n : ℕ, rightPast n).topologicalClosure_minimal
      (iSup_le fun n => rightPast_le_intrinsic n)
      (IBMConditionalObservable.observableSpace_isClosed _ _
        IBMConstructedSources.sceneryPath_measurable IBMConstructedSources.clockPath_measurable)
  · rw [← all_past_closure]
    exact Submodule.topologicalClosure_mono (iSup_le fun n =>
      (past_le_rightPast n).trans (le_iSup (fun n : ℕ => rightPast n) n))

theorem right_projection_tendsto (f : IntrinsicSpace) :
    Tendsto (fun n : ℕ => (rightPast n).starProjection (f : JointL2))
      atTop (𝓝 (f : JointL2)) := by
  have hp := Submodule.starProjection_tendsto_closure_iSup (fun n : ℕ => rightPast n)
    (fun i j h => IBMRightGermFiltration.rightPast_mono (by exact_mod_cast h)) (f : JointL2)
  have hf : (f : JointL2) ∈ (⨆ n : ℕ, rightPast n).topologicalClosure := by
    rw [all_right_past_closure]
    exact f.property
  rwa [Submodule.starProjection_eq_self_iff.mpr hf] at hp

end OperatorDerivativeRewrite.Foundation.IBMObservableHorizonLimit
