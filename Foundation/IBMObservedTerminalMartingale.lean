import Foundation.IBMDeterministicRangeObstruction

/-! Actual terminal-observable martingales in the explicit IBM right-germ
filtration, including a nonzero scenery-odd terminal channel. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMObservedTerminalMartingale
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMIntrinsicRightGerm
open IBMRightGermFiltration IBMScenerySignSymmetry IBMDeterministicRangeObstruction
set_option backward.isDefEq.respectTransparency false

def channelClass (F : JointL2) (t : ℝ≥0) : JointL2 := (rightPast t).starProjection F

def channel (F : JointL2) (t : ℝ≥0) : IBMSourceLaws.JointSample → ℝ := channelClass F t

theorem channel_memLp (F : JointL2) (t : ℝ≥0) :
    MemLp (channel F t) 2 IBMSourceLaws.jointMeasure := Lp.memLp _

theorem channel_adapted (F : JointL2) : StronglyAdapted germFiltration (channel F) := by
  intro t
  exact (representative_measurable t _ (Submodule.starProjection_apply_mem _ _)).stronglyMeasurable

theorem project_channel (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) :
    (rightPast s).starProjection (channelClass F t) = channelClass F s :=
  DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le (rightPast_mono hst)) F

theorem channel_martingale (F : JointL2) :
    Martingale (channel F) germFiltration IBMSourceLaws.jointMeasure := by
  refine ⟨channel_adapted F, ?_⟩
  intro s t hst
  have he := projection_ae s (channelClass F t)
  rw [project_channel F hst] at he
  exact he.symm

theorem channel_right_continuous (F : JointL2) (t : ℝ≥0) :
    ContinuousWithinAt (channelClass F) (Ici t) t :=
  IBMRightGermContinuity.projection_right_continuous t F

theorem channel_norm_bound (F : JointL2) (t : ℝ≥0) : ‖channelClass F t‖ ≤ ‖F‖ :=
  (rightPast t).norm_starProjection_apply_le F

theorem channel_mean (F : JointL2) (t : ℝ≥0) :
    (∫ ω, channel F t ω ∂IBMSourceLaws.jointMeasure) =
      ∫ ω, F ω ∂IBMSourceLaws.jointMeasure := by
  change (∫ ω, ((rightPast t).starProjection F) ω ∂IBMSourceLaws.jointMeasure) = _
  rw [integral_congr_ae (projection_ae t F), integral_condExp (germFiltration.le t)]

theorem terminal_class (F : JointL2) {T t : ℝ≥0} (hF : F ∈ past T) (hT : T ≤ t) :
    channelClass F t = F := by
  apply Submodule.starProjection_eq_self_iff.mpr
  exact (past_le_rightPast t) (hF.mono (naturalFiltration.mono hT))

theorem terminal_ae (F : JointL2) {T t : ℝ≥0} (hF : F ∈ past T) (hT : T ≤ t) :
    channel F t =ᵐ[IBMSourceLaws.jointMeasure] F := by
  have he := terminal_class F hF hT
  exact EventuallyEq.of_eq (congrArg (fun f : JointL2 => (f : IBMSourceLaws.JointSample → ℝ)) he)

theorem projection_action (K : Submodule ℝ JointL2) [K.HasOrthogonalProjection]
    (hK : ∀ f ∈ K, action f ∈ K) (F : JointL2) :
    action (K.starProjection F) = K.starProjection (action F) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hK _ (K.starProjection_apply_mem F))
  intro g hg
  calc
    inner ℝ (action F - action (K.starProjection F)) g =
        inner ℝ (action (F - K.starProjection F)) g := by rw [map_sub]
    _ = inner ℝ (F - K.starProjection F) (action g) := action_self_adjoint _ _
    _ = 0 := K.starProjection_inner_eq_zero F (action g) (hK g hg)

theorem channel_action (F : JointL2) (t : ℝ≥0) :
    action (channelClass F t) = channelClass (action F) t :=
  projection_action (rightPast t) (action_mem_rightPast t) F

theorem observed_channel_odd (T t : ℝ≥0) :
    action (channelClass (observed T) t) = -channelClass (observed T) t := by
  rw [channel_action, observed_odd]
  exact (rightPast t).starProjection.map_neg _

theorem observed_channel_centered (T t : ℝ≥0) :
    (∫ ω, channel (observed T) t ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  rw [channel_mean, observed_centered]

theorem observed_terminal (T t : ℝ≥0) (hT : T ≤ t) :
    channel (observed T) t =ᵐ[IBMSourceLaws.jointMeasure] IBMConstructedSources.ibmValue T :=
  (terminal_ae _ (observed_mem_past T) hT).trans (observed_ae T)

theorem observed_terminal_ne_zero : channelClass (observed 1) 1 ≠ 0 := by
  rw [terminal_class _ (observed_mem_past 1) le_rfl]
  exact observed_one_ne_zero

theorem observed_channel_quadratic_orthogonal (T t u : ℝ≥0) :
    inner ℝ (channelClass (observed T) t) (rightLimitClass u) = 0 := by
  have h := action.inner_map_map (channelClass (observed T) t) (rightLimitClass u)
  rw [observed_channel_odd, rightLimit_fixed, inner_neg_left] at h
  linarith

end OperatorDerivativeRewrite.Foundation.IBMObservedTerminalMartingale
