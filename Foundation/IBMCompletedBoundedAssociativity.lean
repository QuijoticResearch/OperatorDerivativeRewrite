import Foundation.IBMStochasticProductAssociativity

/-! Common bounded predictable multiplication on any completed family is
the actual original stochastic integral of its output channel. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology DirectSum
namespace OperatorDerivativeRewrite.Foundation.IBMCompletedBoundedAssociativity
open IBMTimeAveragedObservable IBMPredictableLpDictionary IBMMultichannelCompletion
open IBMJointPredictableMultiplier IBMCompletedPredictableMultiplier IBMStochasticProductAssociativity
attribute [local instance] componentAdd componentGroup componentModule componentZeroDec
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [DecidableEq ι] (F : ι → JointL2)

def augmented (G : JointL2) : Option ι → JointL2
  | none => G
  | some i => F i

def liftRaw (G : JointL2) : Raw F →ₗ[ℝ] Raw (augmented F G) :=
  DirectSum.toModule ℝ ι (Raw (augmented F G))
    (fun i => DirectSum.lof ℝ (Option ι) (fun j => PredictableL2 (augmented F G j)) (some i))

theorem lift_actual (G : JointL2) (u : Raw F) :
    rawIntegral (augmented F G) (liftRaw F G u)=rawIntegral F u := by
  have he : (rawIntegral (augmented F G)).comp (liftRaw F G)=rawIntegral F := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro H
    simp only [LinearMap.comp_apply,liftRaw,DirectSum.toModule_lof]
    exact (rawIntegral_single (augmented F G) (some i) H).trans (rawIntegral_single F i H).symm
  exact DFunLike.congr_fun he u

theorem lift_modified (G : JointL2) (g : BoundedPredictable) (u : Raw F) :
    modifiedIntegral (augmented F G) g (liftRaw F G u)=modifiedIntegral F g u := by
  have he : (modifiedIntegral (augmented F G) g).comp (liftRaw F G)=modifiedIntegral F g := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro H
    simp only [LinearMap.comp_apply,liftRaw,DirectSum.toModule_lof]
    change modifiedIntegral (augmented F G) g
      (DirectSum.lof ℝ (Option ι) (fun j => PredictableL2 (augmented F G j)) (some i) H) = _
    have hl : modifiedIntegral (augmented F G) g
        (DirectSum.lof ℝ (Option ι) (fun j => PredictableL2 (augmented F G j)) (some i) H) =
        IBMFullPredictableIntegral.integral (F i) (multiplier g (F i) H) :=
      DirectSum.toModule_lof ℝ
        (φ := fun j => (IBMFullPredictableIntegral.integral (augmented F G j)).toLinearMap.comp
          (multiplier g (augmented F G j)).toLinearMap) (some i) H
    have hr : modifiedIntegral F g (DirectSum.lof ℝ ι (fun j => PredictableL2 (F j)) i H) =
        IBMFullPredictableIntegral.integral (F i) (multiplier g (F i) H) :=
      DirectSum.toModule_lof ℝ
        (φ := fun j => (IBMFullPredictableIntegral.integral (F j)).toLinearMap.comp
          (multiplier g (F j)).toLinearMap) i H
    exact hl.trans hr.symm
  exact DFunLike.congr_fun he u

theorem raw_comparison (G : JointL2) (K : PredictableL2 G) (g : BoundedPredictable) (u : Raw F) :
    ‖completedIntegral F (operator F g (embed F u))-
      IBMFullPredictableIntegral.integral G (multiplier g G K)‖ ≤
      g.bound*‖completedIntegral F (embed F u)-IBMFullPredictableIntegral.integral G K‖ := by
  let v : Raw (augmented F G) := liftRaw F G u-
    DirectSum.lof ℝ (Option ι) (fun j => PredictableL2 (augmented F G j)) none K
  have hb := raw_bound (augmented F G) g v
  have hm : rawIntegral (augmented F G) (rawMap (augmented F G) g v)=
      modifiedIntegral F g u-IBMFullPredictableIntegral.integral G (multiplier g G K) := by
    change ((rawIntegral (augmented F G)).comp (rawMap (augmented F G) g)) v=_
    rw [rawMap_integral]
    change modifiedIntegral (augmented F G) g (liftRaw F G u-_) = _
    rw [map_sub,lift_modified]
    simp only [modifiedIntegral,DirectSum.toModule_lof,LinearMap.comp_apply]
    rfl
  have hi : rawIntegral (augmented F G) v = rawIntegral F u-IBMFullPredictableIntegral.integral G K := by
    change rawIntegral (augmented F G) (liftRaw F G u-_) = _
    rw [map_sub,lift_actual,rawIntegral_single]
    rfl
  rw [hm,hi] at hb
  rw [operator_embed,completedIntegral_embed,completedIntegral_embed]
  change ‖((rawIntegral F).comp (rawMap F g)) u-_‖ ≤ _
  rw [rawMap_integral]
  exact hb

theorem comparison_bound (G : JointL2) (K : PredictableL2 G) (g : BoundedPredictable) (z : Completed F) :
    ‖completedIntegral F (operator F g z)-IBMFullPredictableIntegral.integral G (multiplier g G K)‖ ≤
      g.bound*‖completedIntegral F z-IBMFullPredictableIntegral.integral G K‖ := by
  refine (embed_dense F).induction_on z
    (isClosed_le
      (((completedIntegral F).continuous.comp (operator F g).continuous).sub continuous_const).norm
      (continuous_const.mul ((completedIntegral F).continuous.sub continuous_const).norm)) ?_
  intro u
  exact raw_comparison F G K g u

theorem actual_bounded_associativity (g : BoundedPredictable) (z : Completed F) :
    completedIntegral F (operator F g z)=
      IBMFullPredictableIntegral.integral (completedIntegral F z) (boundedClass g (completedIntegral F z)) := by
  obtain ⟨G,K,hK⟩ := (IBMTerminalSelfRepresentation.all_channels_range_iff (completedIntegral F z)).mpr
    (completed_mem_remainder F z)
  have hb := comparison_bound F G K g z
  rw [hK,sub_self,norm_zero,mul_zero] at hb
  have he : completedIntegral F (operator F g z)=IBMFullPredictableIntegral.integral G (multiplier g G K) :=
    sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
  calc
    _ = IBMFullPredictableIntegral.integral G (multiplier g G K) := he
    _ = IBMFullPredictableIntegral.integral (IBMFullPredictableIntegral.integral G K)
        (boundedClass g (IBMFullPredictableIntegral.integral G K)) := (bounded_associativity G K g).symm
    _ = _ := congrArg (fun Y : JointL2 => IBMFullPredictableIntegral.integral Y (boundedClass g Y)) hK

theorem nested_identification (g : BoundedPredictable) (z : Completed F) :
    operator F g z=IBMCompletedStochasticAssociativity.nestedIntegral F z
      (boundedClass g (completedIntegral F z)) := by
  apply (completedIntegral F).injective
  rw [actual_bounded_associativity,IBMCompletedStochasticAssociativity.nested_actual]

end OperatorDerivativeRewrite.Foundation.IBMCompletedBoundedAssociativity
