import Foundation.IBMClockLinearDivergence
import Foundation.IBMObservedTerminalMartingale
import Foundation.IBMTerminalSelfRepresentation
import Foundation.IBMCenteredSourceRepresentation

/-! A genuine observed quadratic-clock martingale tied to an explicit native divergence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMQuadraticClockMartingale
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMClockLinearDivergence
open IBMNaturalFiltrationObstruction IBMIntrinsicRightGerm IBMRightGermFiltration
open IBMObservedTerminalMartingale IBMPredictableIntegralObservable
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

def terminal (T : ℝ≥0) : IntrinsicSpace := output (timeDirection T) (timeDirection T)

def valueClass (T s : ℝ≥0) : JointL2 := channelClass (IBMEvenClockProjection.clockQuadratic T) s

def process (T s : ℝ≥0) : IBMSourceLaws.JointSample → ℝ := valueClass T s

theorem process_martingale (T : ℝ≥0) : Martingale (process T) germFiltration IBMSourceLaws.jointMeasure :=
  channel_martingale (IBMEvenClockProjection.clockQuadratic T)

theorem process_memLp (T s : ℝ≥0) : MemLp (process T s) 2 IBMSourceLaws.jointMeasure := Lp.memLp _

theorem right_L2_continuity (T s : ℝ≥0) : ContinuousWithinAt (valueClass T) (Ici s) s :=
  channel_right_continuous (IBMEvenClockProjection.clockQuadratic T) s

theorem native_channel (T s : ℝ≥0) : channelClass (terminal T : JointL2) s = valueClass T s := by
  have ht := congrArg (fun z : IntrinsicSpace => (z : JointL2)) (time_output T)
  change (terminal T : JointL2) = IntrinsicSpace.starProjection (IBMEvenClockProjection.clockQuadratic T) at ht
  rw [channelClass,ht]
  exact DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le (rightPast_le_intrinsic s)) _

theorem process_centered (T s : ℝ≥0) :
    (∫ ω, process T s ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  have h0 := IBMCenteredSourceRepresentation.divergence_mean_zero
    ⟨nativeField (timeDirection T) (timeDirection T),native_mem _ _⟩
  rw [native_value] at h0
  have he := congrArg (fun q : JointL2 => ∫ ω, q ω ∂IBMSourceLaws.jointMeasure) (native_channel T s).symm
  exact he.trans ((channel_mean (terminal T : JointL2) s).trans h0)

theorem fourth_pairing (T s : ℝ≥0) (hTs : T ≤ s) :
    inner ℝ (valueClass T s) (IBMActualQuarticMoment.fourthClass T) = 6*(T : ℝ)^2 := by
  have hf : IBMActualQuarticMoment.fourthClass T ∈ rightPast s :=
    past_le_rightPast s (IBMActualQuarticMoment.fourthClass_mem_past hTs)
  have he : inner ℝ (valueClass T s) (IBMActualQuarticMoment.fourthClass T) =
      inner ℝ (IBMEvenClockProjection.clockQuadratic T) (IBMActualQuarticMoment.fourthClass T) :=
    (rightPast s).inner_orthogonalProjectionOnto_eq_of_mem_right
      ⟨IBMActualQuarticMoment.fourthClass T,hf⟩ (IBMEvenClockProjection.clockQuadratic T)
  exact he.trans (IBMEvenClockProjection.quadratic_fourth_pairing T)

theorem value_ne_zero (T s : ℝ≥0) (hT : 0 < T) (hTs : T ≤ s) : valueClass T s ≠ 0 := by
  intro hz
  have hp := fourth_pairing T s hTs
  rw [hz,inner_zero_left] at hp
  have hn : 0 < 6*(T : ℝ)^2 := mul_pos (by norm_num) (sq_pos_of_pos hT)
  linarith

theorem scenery_fixed (T s : ℝ≥0) : IBMScenerySignSymmetry.action (valueClass T s) = valueClass T s := by
  change IBMScenerySignSymmetry.action (channelClass (IBMEvenClockProjection.clockQuadratic T) s) = _
  rw [channel_action,IBMScenerySignSymmetry.clockQuadratic_fixed]
  rfl

theorem observed_orthogonal (T s u : ℝ≥0) :
    inner ℝ (valueClass T s) (IBMDeterministicRangeObstruction.observed u) = 0 := by
  have he := IBMScenerySignSymmetry.action.inner_map_map (valueClass T s)
    (IBMDeterministicRangeObstruction.observed u)
  rw [scenery_fixed,IBMDeterministicRangeObstruction.observed_odd,inner_neg_right] at he
  linarith

theorem actual_unit_integral (T s : ℝ≥0) :
    IBMFullPredictableIntegral.integral (IBMEvenClockProjection.clockQuadratic T)
      (IBMTerminalSelfRepresentation.unitIntegrand (IBMEvenClockProjection.clockQuadratic T) s) =
      valueClass T s-valueClass T 0 :=
  IBMTerminalSelfRepresentation.integral_unit _ _

theorem before_terminal (T s : ℝ≥0) (hs : s < T) : valueClass T s = rightLimitClass s := by
  have he := DFunLike.congr_fun
    (Submodule.starProjection_comp_starProjection_of_le (rightPast_le_past hs))
    (IBMEvenClockProjection.clockQuadratic T)
  have hp : (rightPast s).starProjection
      (IBMIntrinsicQuadraticMartingale.valueClass T : JointL2) = valueClass T s := he
  exact hp.symm.trans (rightLimitClass_horizon hs).symm

theorem initial_zero (T : ℝ≥0) (hT : 0 < T) : valueClass T 0 = 0 :=
  (before_terminal T 0 hT).trans IBMIntrinsicRightApproach.rightLimitClass_zero

theorem actual_integral_value (T : ℝ≥0) (hT : 0 < T) (s : ℝ≥0) :
    IBMFullPredictableIntegral.integral (IBMEvenClockProjection.clockQuadratic T)
      (IBMTerminalSelfRepresentation.unitIntegrand (IBMEvenClockProjection.clockQuadratic T) s) =
      valueClass T s := by
  rw [actual_unit_integral,initial_zero T hT,sub_zero]

theorem nonzero_integrand (T s : ℝ≥0) (hT : 0 < T) (hTs : T ≤ s) :
    IBMTerminalSelfRepresentation.unitIntegrand (IBMEvenClockProjection.clockQuadratic T) s ≠ 0 := by
  intro hz
  have he := actual_integral_value T hT s
  rw [hz,map_zero] at he
  exact value_ne_zero T s hT hTs he.symm

theorem not_constant (T : ℝ≥0) (hT : 0 < T) : valueClass T T ≠ valueClass T 0 := by
  rw [initial_zero T hT]
  exact value_ne_zero T T hT le_rfl

end OperatorDerivativeRewrite.Foundation.IBMQuadraticClockMartingale
