import Foundation.IBMRawInitialPast

/-! A genuinely nonconstant actual raw-observation IBM martingale, and
its exact strong-L2 right-germ comparison without an initial-germ assumption. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawObservedMartingale
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction
open IBMIntrinsicRightGerm IBMDeterministicRangeObstruction IBMRawInitialPast
set_option backward.isDefEq.respectTransparency false

def rawClass (F : JointL2) (t : ℝ≥0) : JointL2 := (past t).starProjection F

def rawValue (F : JointL2) (t : ℝ≥0) : IBMSourceLaws.JointSample → ℝ :=
  IBMSourceLaws.jointMeasure[F | naturalFiltration t]

theorem rawClass_ae (F : JointL2) (t : ℝ≥0) :
    rawClass F t =ᵐ[IBMSourceLaws.jointMeasure] rawValue F t := by
  simpa only [rawClass, rawValue, past, Lp.toLp_coeFn, condExpL2,
    ← Submodule.starProjection_apply] using
    (Lp.memLp F).condExpL2_ae_eq_condExp (𝕜 := ℝ) (naturalFiltration.le t)

theorem rawValue_memLp (F : JointL2) (t : ℝ≥0) :
    MemLp (rawValue F t) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (rawClass F t)).ae_eq (rawClass_ae F t)

theorem raw_martingale (F : JointL2) :
    Martingale (rawValue F) naturalFiltration IBMSourceLaws.jointMeasure := by
  refine ⟨fun t => stronglyMeasurable_condExp, ?_⟩
  intro s t hst
  exact condExp_condExp_of_le (naturalFiltration.mono hst) (naturalFiltration.le t)

theorem raw_mean (F : JointL2) (t : ℝ≥0) :
    (∫ ω, rawValue F t ω ∂IBMSourceLaws.jointMeasure) =
      ∫ ω, F ω ∂IBMSourceLaws.jointMeasure :=
  integral_condExp (naturalFiltration.le t)

theorem raw_terminal_class (F : JointL2) {T t : ℝ≥0} (hF : F ∈ past T) (ht : T ≤ t) :
    rawClass F t = F :=
  Submodule.starProjection_eq_self_iff.mpr (hF.mono (naturalFiltration.mono ht))

theorem raw_origin_class (F : JointL2)
    (hF : (∫ ω, F ω ∂IBMSourceLaws.jointMeasure) = 0) : rawClass F 0 = 0 :=
  initial_projection_zero F hF

theorem raw_origin_ae (F : JointL2)
    (hF : (∫ ω, F ω ∂IBMSourceLaws.jointMeasure) = 0) :
    rawValue F 0 =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => (0 : ℝ)) := by
  have he := (rawClass_ae F 0).symm
  rw [raw_origin_class F hF] at he
  exact he.trans (Lp.coeFn_zero _ _ _)

theorem observed_raw_terminal {t : ℝ≥0} (ht : 1 ≤ t) :
    rawValue (observed 1) t =ᵐ[IBMSourceLaws.jointMeasure] IBMConstructedSources.ibmValue 1 := by
  have he := (rawClass_ae (observed 1) t).symm
  rw [raw_terminal_class _ (observed_mem_past 1) ht] at he
  exact he.trans (observed_ae 1)

theorem observed_raw_origin : rawValue (observed 1) 0 =ᵐ[IBMSourceLaws.jointMeasure]
    (fun _ => (0 : ℝ)) := raw_origin_ae _ (observed_centered 1)

theorem observed_raw_odd (t : ℝ≥0) :
    IBMScenerySignSymmetry.action (rawClass (observed 1) t) = -rawClass (observed 1) t := by
  have he := IBMObservedTerminalMartingale.projection_action (past t)
    (IBMScenerySignSymmetry.action_mem_past t) (observed 1)
  rw [observed_odd] at he
  exact he.trans ((past t).starProjection.map_neg _)

theorem observed_raw_nonconstant :
    ¬ rawValue (observed 1) 1 =ᵐ[IBMSourceLaws.jointMeasure] rawValue (observed 1) 0 := by
  intro he
  have hz := (observed_ae 1).trans ((observed_raw_terminal le_rfl).symm.trans
    (he.trans observed_raw_origin))
  exact observed_one_ne_zero (Lp.ext (hz.trans (Lp.coeFn_zero _ _ _).symm))

theorem raw_right_limit (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Antitone τ) (t : ℝ≥0)
    (ht : ∀ n, t < τ n) (hlim : Tendsto τ atTop (𝓝 t)) :
    Tendsto (fun n => rawClass F (τ n)) atTop
      (𝓝 (IBMObservedTerminalMartingale.channelClass F t)) := by
  simpa only [rawClass, IBMObservedTerminalMartingale.channelClass,
    intersection_eq_rightPast τ t ht hlim] using
      IBMDecreasingPastProjection.projection_tendsto τ hτ F

theorem right_germ_projects_to_raw (F : JointL2) (t : ℝ≥0) :
    (past t).starProjection (IBMObservedTerminalMartingale.channelClass F t) = rawClass F t :=
  DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le (past_le_rightPast t)) F

end OperatorDerivativeRewrite.Foundation.IBMRawObservedMartingale
