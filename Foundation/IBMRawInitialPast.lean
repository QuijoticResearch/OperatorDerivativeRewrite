import Foundation.IBMObservedTerminalMartingale

/-! The actual raw IBM initial past contains only almost-sure constants.
This does not assert triviality of the strictly-right germ. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawInitialPast
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction
open IBMDeterministicRangeObstruction
set_option backward.isDefEq.respectTransparency false

theorem observed_zero : observed 0 = 0 := by
  change jointRealization (IBMRandomTimeHilbert.randomSourceL2 0) = 0
  rw [IBMPastEndpointCore.randomSource_zero, map_zero]

theorem ibm_zero_ae : IBMConstructedSources.ibmValue 0 =ᵐ[IBMSourceLaws.jointMeasure]
    (fun _ => (0 : ℝ)) := by
  have hz : observed 0 =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => (0 : ℝ)) := by
    rw [observed_zero]
    exact Lp.coeFn_zero _ _ _
  exact (observed_ae 0).symm.trans hz

theorem past_zero_constant (f : JointL2) (hf : f ∈ past 0) :
    ∃ c : ℝ, f =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => c) := by
  change AEStronglyMeasurable[naturalFiltration 0] f IBMSourceLaws.jointMeasure at hf
  obtain ⟨g, _, he⟩ := (GaussianPredictableStep.measurable_natural_iff_exists_pastCoefficient
    (fun t => (point_stronglyMeasurable t).measurable) 0 (hf.mk f)).mp
      hf.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[IBMSourceLaws.jointMeasure]
      GaussianPredictableStep.pastCoefficient IBMConstructedSources.ibmValue 0 g :=
    hf.ae_eq_mk.trans (EventuallyEq.of_eq he)
  refine ⟨g 0, ?_⟩
  filter_upwards [hfg, ibm_zero_ae] with ω hh hz
  rw [hh]
  apply congrArg g
  funext t
  have ht : t.val = 0 := le_antisymm t.property zero_le
  change IBMConstructedSources.ibmValue t.val ω = 0
  rw [ht, hz]

theorem initial_projection_zero (F : JointL2)
    (hF : (∫ ω, F ω ∂IBMSourceLaws.jointMeasure) = 0) :
    (past 0).starProjection F = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (past 0).zero_mem
  intro g hg
  obtain ⟨c, hc⟩ := past_zero_constant g hg
  rw [sub_zero, L2.inner_def]
  calc
    _ = ∫ ω, F ω * c ∂IBMSourceLaws.jointMeasure := by
      apply integral_congr_ae
      filter_upwards [hc] with ω hω
      rw [hω, Real.inner_apply]
    _ = 0 := by rw [integral_mul_const, hF, zero_mul]

end OperatorDerivativeRewrite.Foundation.IBMRawInitialPast
