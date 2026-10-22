import Foundation.IBMClippedForecastPairing

/-! Zero initial right-germ prediction of actual IBM coordinates.
This does not assert triviality of the whole germ or equality at positive times. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMObservedInitialGerm
open IBMTimeAveragedObservable IBMConstructedSources IBMRightGermFiltration
open IBMIntrinsicRightGerm IBMDeterministicRangeObstruction IBMClippedForecastPairing
open IBMObservedTerminalMartingale
set_option backward.isDefEq.respectTransparency false

theorem setIntegral_zero (t : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[germFiltration 0] A) :
    (∫ ω in A, ibmValue t ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  have hAm := germFiltration.le 0 A hA
  have hi : MemLp (A.indicator (fun _ => (1 : ℝ))) 2 IBMSourceLaws.jointMeasure :=
    (memLp_const (1 : ℝ)).indicator hAm
  let f : JointL2 := hi.toLp _
  have hfa : f =ᵐ[IBMSourceLaws.jointMeasure] A.indicator (fun _ => (1 : ℝ)) :=
    hi.coeFn_toLp
  have hm : StronglyMeasurable[germFiltration 0] (A.indicator (fun _ => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hA
  have hf : f ∈ rightPast 0 := by
    rw [← germPast_eq 0]
    exact hm.aestronglyMeasurable.congr hfa.symm
  have hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |f ω| ≤ 1 := by
    filter_upwards [hfa] with ω hω
    rw [hω]
    by_cases ha : ω ∈ A <;> simp [Set.indicator, ha]
  have hp := bounded_germ_orthogonal t f hf 1 (by norm_num) hb
  rw [L2.inner_def] at hp
  rw [← integral_indicator hAm]
  convert hp using 1
  apply integral_congr_ae
  filter_upwards [observed_ae t, hfa] with ω ho he
  rw [Real.inner_apply, ho, he]
  by_cases ha : ω ∈ A <;> simp [Set.indicator, ha]

theorem initial_condExp_zero (t : ℝ≥0) :
    IBMSourceLaws.jointMeasure[ibmValue t | germFiltration 0]
      =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => (0 : ℝ)) := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (germFiltration.le 0)
    ((ibm_memLp t).integrable (by norm_num))
  · intro A _ _
    exact (integrable_zero IBMSourceLaws.JointSample ℝ IBMSourceLaws.jointMeasure).integrableOn
  · intro A hA _
    simpa only [integral_zero] using (setIntegral_zero t A hA).symm
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem initial_channel_zero (t : ℝ≥0) : channelClass (observed t) 0 = 0 := by
  apply Lp.ext
  exact (projection_ae 0 (observed t)).trans
    ((condExp_congr_ae (observed_ae t)).trans
      ((initial_condExp_zero t).trans (Lp.coeFn_zero _ _ _).symm))

theorem initial_channel_ae_zero (t : ℝ≥0) :
    channel (observed t) 0 =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => (0 : ℝ)) := by
  change channelClass (observed t) 0 =ᵐ[IBMSourceLaws.jointMeasure] _
  rw [initial_channel_zero]
  exact Lp.coeFn_zero _ _ _

theorem initial_raw_zero (t : ℝ≥0) :
    IBMRawObservedMartingale.rawClass (observed t) 0 = 0 := by
  have he := IBMRawObservedMartingale.right_germ_projects_to_raw (observed t) 0
  rw [initial_channel_zero, map_zero] at he
  exact he.symm

theorem raw_prediction_tendsto_zero (t : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hτ : Antitone τ) (ht : ∀ n, 0 < τ n) (hlim : Tendsto τ atTop (𝓝 0)) :
    Tendsto (fun n => IBMRawObservedMartingale.rawClass (observed t) (τ n)) atTop (𝓝 0) := by
  simpa only [initial_channel_zero] using
    IBMRawObservedMartingale.raw_right_limit (observed t) τ hτ 0 ht hlim

theorem terminal_energy_mass (t : ℝ≥0) :
    IBMTerminalEnergyMeasure.energyMeasure (observed t) (Ioc 0 t) =
      ENNReal.ofReal (‖observed t‖ ^ 2) := by
  rw [IBMTerminalEnergyMeasure.terminal_mass _ (observed_mem_past t), initial_channel_zero]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]

end OperatorDerivativeRewrite.Foundation.IBMObservedInitialGerm
