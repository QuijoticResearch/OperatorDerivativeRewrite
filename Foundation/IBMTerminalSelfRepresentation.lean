import Foundation.IBMObservableHorizonLimit
import Foundation.IBMNativePredictableTransfer

/-! Actual terminal-indexed reconstruction retains the whole initial germ. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMTerminalSelfRepresentation
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMIntrinsicRightGerm
open IBMObservedTerminalMartingale IBMPredictableLpDictionary
open IBMPredictableFiniteIntegral (Index integralLinear)
open IBMFullPredictableIntegral IBMWeightedTerminalEnergy IBMObservableHorizonLimit
set_option backward.isDefEq.respectTransparency false

def unitIndex (T : ℝ≥0) : Index := ⟨(0,T,univ), zero_le, MeasurableSet.univ⟩

def unitIntegrand (F : JointL2) (T : ℝ≥0) : PredictableL2 F :=
  dictionary F (Finsupp.single (unitIndex T) 1)

theorem weighted_unit (F : JointL2) (s : ℝ≥0) :
    weightedTerminal F s (eventCoefficient s univ MeasurableSet.univ) = F := by
  apply Lp.ext
  filter_upwards [weightedTerminal_ae F s (eventCoefficient s univ MeasurableSet.univ)] with ω hω
  simpa [eventCoefficient] using hω

theorem integral_unit (F : JointL2) (T : ℝ≥0) :
    integral F (unitIntegrand F T) = channelClass F T-channelClass F 0 := by
  rw [unitIntegrand, integral_dictionary]
  simp only [integralLinear, Finsupp.linearCombination_single, one_smul]
  change IBMGermPredictableStep.stepClass F 0 T
    (eventCoefficient 0 univ MeasurableSet.univ) = _
  rw [IBMGermPredictableStep.stepClass, weighted_unit]

theorem integral_unit_limit (f : IntrinsicSpace) :
    Tendsto (fun n : ℕ => integral (f : JointL2) (unitIntegrand (f : JointL2) n)) atTop
      (𝓝 ((f : JointL2)-channelClass (f : JointL2) 0)) := by
  simpa only [integral_unit, channelClass] using
    (right_projection_tendsto f).sub_const ((rightPast 0).starProjection (f : JointL2))

theorem self_representation (f : IntrinsicSpace) :
    ∃ H : PredictableL2 (f : JointL2),
      integral (f : JointL2) H = (f : JointL2)-channelClass (f : JointL2) 0 := by
  have hc : IsClosed (Set.range (integral (f : JointL2))) :=
    (integral (f : JointL2)).isometry.antilipschitz.isClosed_range
      (integral (f : JointL2)).isometry.uniformContinuous
  exact hc.mem_of_tendsto (integral_unit_limit f)
    (Eventually.of_forall fun n => ⟨unitIntegrand (f : JointL2) n, rfl⟩)

theorem integrand_unit_limit (f : IntrinsicSpace) (H : PredictableL2 (f : JointL2))
    (hH : integral (f : JointL2) H = (f : JointL2)-channelClass (f : JointL2) 0) :
    Tendsto (fun n : ℕ => unitIntegrand (f : JointL2) n) atTop (𝓝 H) := by
  apply (integral (f : JointL2)).isometry.tendsto_nhds_iff.mpr
  change Tendsto (fun n : ℕ => integral (f : JointL2) (unitIntegrand (f : JointL2) n))
    atTop (𝓝 (integral (f : JointL2) H))
  exact hH.symm ▸ integral_unit_limit f

theorem all_channels_range_iff (x : JointL2) :
    (∃ F : JointL2, ∃ H : PredictableL2 F, integral F H = x) ↔
      x ∈ IntrinsicSpace ∧ x ∈ (rightPast 0)ᗮ := by
  constructor
  · rintro ⟨F,H,rfl⟩
    refine ⟨IBMPredictableIntegralObservable.integral_mem_intrinsic F H, ?_⟩
    rw [Submodule.mem_orthogonal']
    intro g hg
    rw [real_inner_comm]
    exact IBMPredictableIntegralObservable.integral_orthogonal_initial F H g hg
  · rintro ⟨hx,hg⟩
    have hz : channelClass x 0 = 0 := by
      exact (Submodule.starProjection_apply_eq_zero_iff (rightPast 0)).mpr hg
    obtain ⟨H,hH⟩ := self_representation ⟨x,hx⟩
    exact ⟨x,H,by simpa only [hz, sub_zero] using hH⟩

theorem self_integrand_adjoint (f : IntrinsicSpace) (H : PredictableL2 (f : JointL2))
    (hH : integral (f : JointL2) H = (f : JointL2)-channelClass (f : JointL2) 0) :
    (integral (f : JointL2)).toContinuousLinearMap.adjoint (f : JointL2) = H := by
  apply ext_inner_left ℝ
  intro K
  rw [ContinuousLinearMap.adjoint_inner_right]
  have ho := IBMPredictableIntegralObservable.integral_orthogonal_initial (f : JointL2) K
    (channelClass (f : JointL2) 0) ((rightPast 0).starProjection_apply_mem (f : JointL2))
  have he : (f : JointL2) = integral (f : JointL2) H + channelClass (f : JointL2) 0 := by
    rw [hH, sub_add_cancel]
  calc
    inner ℝ (integral (f : JointL2) K) (f : JointL2) =
        inner ℝ (integral (f : JointL2) K)
          (integral (f : JointL2) H + channelClass (f : JointL2) 0) :=
      congrArg (fun y : JointL2 => inner ℝ (integral (f : JointL2) K) y) he
    _ = inner ℝ K H := by
      have ho' : inner ℝ (integral (f : JointL2) K) (channelClass (f : JointL2) 0) = 0 :=
        (real_inner_comm (channelClass (f : JointL2) 0) (integral (f : JointL2) K)).trans ho
      rw [inner_add_right, integral_inner, ho', add_zero]

theorem target_indexed_reconstruction (f : IntrinsicSpace) :
    integral (f : JointL2) ((integral (f : JointL2)).toContinuousLinearMap.adjoint (f : JointL2)) =
      (f : JointL2)-channelClass (f : JointL2) 0 := by
  obtain ⟨H,hH⟩ := self_representation f
  have he := self_integrand_adjoint f H hH
  exact (congrArg (integral (f : JointL2)) he).trans hH

theorem native_target_indexed_reconstruction (f : IBMJointIntrinsicDerivative.jointDerivative.domain) :
    integral ((f : IntrinsicSpace) : JointL2)
      ((IBMNativePredictableTransfer.transfer ((f : IntrinsicSpace) : JointL2)).adjoint
        (IBMJointIntrinsicDerivative.jointDerivative f)) =
      ((f : IntrinsicSpace) : JointL2)-channelClass ((f : IntrinsicSpace) : JointL2) 0 := by
  have he := IBMNativePredictableTransfer.native_gradient_adjoint_identity
    ((f : IntrinsicSpace) : JointL2) f
  exact (congrArg (integral ((f : IntrinsicSpace) : JointL2)) he).trans
    (target_indexed_reconstruction (f : IntrinsicSpace))

end OperatorDerivativeRewrite.Foundation.IBMTerminalSelfRepresentation
