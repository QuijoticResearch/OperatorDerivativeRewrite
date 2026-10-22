import Foundation.IBMIntrinsicProductCalculus
import Foundation.MultiplierCore

/-! Bounded multipliers in the actual two-channel native IBM field coordinates. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeFieldMultiplier
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMIntrinsicChainRule IBMIntrinsicChainEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

theorem vectorSwap_involution (g : JointVectorL2) : vectorSwap (vectorSwap g) = g := by
  apply Lp.ext
  have ht := (measurePreserving_swap (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (vectorSwap_ae g)
  filter_upwards [vectorSwap_ae (vectorSwap g),ht] with ω ho hi
  exact ho.trans hi

def vectorSwapEquiv : JointVectorL2 ≃ₗᵢ[ℝ] JointVectorL2 :=
  LinearIsometryEquiv.ofSurjective vectorSwap fun g => ⟨vectorSwap g,vectorSwap_involution g⟩

def coordinate (i : Fin 2) : FieldSpace ≃ₗᵢ[ℝ] JointVectorL2 :=
  if i = 0 then
    (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.trans vectorSwapEquiv
  else (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm

theorem coordinate_zero (g : FieldSpace) : coordinate 0 g = sourceField g := rfl

theorem coordinate_one (g : FieldSpace) : coordinate 1 g = uncurryField g := rfl

def channelMultiplier (i : Fin 2) (a : IBMSourceLaws.JointSample → ℝ)
    (ha : MemLp a ∞ IBMSourceLaws.jointMeasure) : FieldSpace →L[ℝ] FieldSpace :=
  (coordinate i).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((boundedMultiplier a ha).comp (coordinate i).toContinuousLinearEquiv.toContinuousLinearMap)

theorem channel_coordinate (i : Fin 2) (a : IBMSourceLaws.JointSample → ℝ)
    (ha : MemLp a ∞ IBMSourceLaws.jointMeasure) (g : FieldSpace) :
    coordinate i (channelMultiplier i a ha g) = boundedMultiplier a ha (coordinate i g) :=
  (coordinate i).apply_symm_apply _

theorem channel_ae (i : Fin 2) (a : IBMSourceLaws.JointSample → ℝ)
    (ha : MemLp a ∞ IBMSourceLaws.jointMeasure) (g : FieldSpace) :
    coordinate i (channelMultiplier i a ha g) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a ω • coordinate i g ω := by
  rw [channel_coordinate]
  exact boundedMultiplier_coeFn a ha _

theorem channel_symmetric (i : Fin 2) (a : IBMSourceLaws.JointSample → ℝ)
    (ha : MemLp a ∞ IBMSourceLaws.jointMeasure) (u v : FieldSpace) :
    inner ℝ (channelMultiplier i a ha u) v = inner ℝ u (channelMultiplier i a ha v) := by
  calc
    inner ℝ (channelMultiplier i a ha u) v =
        inner ℝ (coordinate i (channelMultiplier i a ha u)) (coordinate i v) :=
      ((coordinate i).inner_map_map _ _).symm
    _ = inner ℝ (boundedMultiplier a ha (coordinate i u)) (coordinate i v) :=
      congrArg (fun z : JointVectorL2 => inner ℝ z (coordinate i v))
        (channel_coordinate i a ha u)
    _ = inner ℝ (coordinate i u) (boundedMultiplier a ha (coordinate i v)) :=
      boundedMultiplier_symmetric a ha _ _
    _ = inner ℝ (coordinate i u) (coordinate i (channelMultiplier i a ha v)) :=
      congrArg (fun z : JointVectorL2 => inner ℝ (coordinate i u) z)
        (channel_coordinate i a ha v).symm
    _ = inner ℝ u (channelMultiplier i a ha v) := (coordinate i).inner_map_map _ _

def multiply (a : IBMSourceLaws.JointSample → ℝ)
    (ha : MemLp a ∞ IBMSourceLaws.jointMeasure) : JointFieldSpace →L[ℝ] JointFieldSpace :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => FieldSpace)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      (channelMultiplier i a ha).comp (PiLp.proj 2 (fun _ : Fin 2 => FieldSpace) i))

theorem multiply_channel (a : IBMSourceLaws.JointSample → ℝ)
    (ha : MemLp a ∞ IBMSourceLaws.jointMeasure) (g : JointFieldSpace) (i : Fin 2) :
    multiply a ha g i = channelMultiplier i a ha (g i) := rfl

theorem multiply_ae (a : IBMSourceLaws.JointSample → ℝ)
    (ha : MemLp a ∞ IBMSourceLaws.jointMeasure) (g : JointFieldSpace) (i : Fin 2) :
    coordinate i (multiply a ha g i) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a ω • coordinate i (g i) ω := channel_ae i a ha (g i)

theorem multiply_symmetric (a : IBMSourceLaws.JointSample → ℝ)
    (ha : MemLp a ∞ IBMSourceLaws.jointMeasure) (u v : JointFieldSpace) :
    inner ℝ (multiply a ha u) v = inner ℝ u (multiply a ha v) := by
  simp only [PiLp.inner_apply,multiply_channel]
  apply Finset.sum_congr rfl
  intro i _
  exact channel_symmetric i a ha (u i) (v i)

theorem multiply_add_ae (x y : IBMTimeAveragedObservable.JointL2)
    (hx : MemLp (x : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (hy : MemLp (y : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (U V : JointFieldSpace) (i : Fin 2) :
    coordinate i ((multiply x hx V + multiply y hy U) i)
      =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
        x ω • coordinate i (V i) ω+y ω • coordinate i (U i) ω := by
  have he : coordinate i ((multiply x hx V + multiply y hy U) i) =
      coordinate i (multiply x hx V i) + coordinate i (multiply y hy U i) :=
    (coordinate i).map_add _ _
  rw [he]
  exact (Lp.coeFn_add _ _).trans ((multiply_ae x hx V i).add (multiply_ae y hy U i))

end OperatorDerivativeRewrite.Foundation.IBMNativeFieldMultiplier
