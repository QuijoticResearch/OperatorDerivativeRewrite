import Foundation.IBMNativeDeterministicFields

/-! Actual field multiplication and contraction maps for deterministic native directions. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeDirectionalMaps
open InfiniteGaussian (CoefficientSpace)
open IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative IBMIntrinsicChainRule
open IBMNativeFieldMultiplier IBMNativeDeterministicFields
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

def coefficientLift (h : CoefficientSpace) : JointL2 →L[ℝ] JointVectorL2 :=
  (ContinuousLinearMap.toSpanSingleton ℝ h).compLpL 2 IBMSourceLaws.jointMeasure

theorem coefficientLift_ae (h : CoefficientSpace) (f : JointL2) :
    coefficientLift h f =ᵐ[IBMSourceLaws.jointMeasure] fun ω => f ω • h :=
  (ContinuousLinearMap.toSpanSingleton ℝ h).coeFn_compLpL f

def lift (h k : CoefficientSpace) : JointL2 →L[ℝ] JointFieldSpace :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => FieldSpace)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      (coordinate i).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (coefficientLift (if i=0 then h else k)))

theorem lift_coordinate (h k : CoefficientSpace) (f : JointL2) (i : Fin 2) :
    coordinate i (lift h k f i) = coefficientLift (if i=0 then h else k) f :=
  (coordinate i).apply_symm_apply _

theorem lift_ae (h k : CoefficientSpace) (f : JointL2) (i : Fin 2) :
    coordinate i (lift h k f i) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => f ω • (if i=0 then h else k) := by
  rw [lift_coordinate]
  exact coefficientLift_ae _ _

theorem bounded_weight_eq (h k : CoefficientSpace) (f : JointL2)
    (hf : MemLp (f : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    multiply f hf (nativeField h k) = lift h k f := by
  apply PiLp.ext
  intro i
  apply (coordinate i).injective
  apply Lp.ext
  filter_upwards [multiply_ae f hf (nativeField h k) i,native_coordinates h k i,
    lift_ae h k f i] with ω hm hu hl
  exact (hm.trans (congrArg (fun z : CoefficientSpace => f ω • z) hu)).trans hl.symm

def coefficientContract (h : CoefficientSpace) : JointVectorL2 →L[ℝ] JointL2 :=
  (innerSL ℝ h).compLpL 2 IBMSourceLaws.jointMeasure

def contract (h k : CoefficientSpace) : JointFieldSpace →L[ℝ] JointL2 :=
  (coefficientContract h).comp
    ((coordinate 0).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (PiLp.proj 2 (fun _ : Fin 2 => FieldSpace) 0)) +
  (coefficientContract k).comp
    ((coordinate 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (PiLp.proj 2 (fun _ : Fin 2 => FieldSpace) 1))

theorem coefficientContract_ae (h : CoefficientSpace) (V : JointVectorL2) :
    coefficientContract h V =ᵐ[IBMSourceLaws.jointMeasure] fun ω => inner ℝ (V ω) h := by
  have ht := (innerSL ℝ h).coeFn_compLpL V
  change coefficientContract h V =ᵐ[IBMSourceLaws.jointMeasure]
    (fun ω => inner ℝ h (V ω)) at ht
  exact ht.mono fun ω hω => hω.trans (real_inner_comm _ _)

theorem contract_eq (h k : CoefficientSpace) (V : JointFieldSpace) :
    contract h k V = coefficientContract h (coordinate 0 (V 0)) +
      coefficientContract k (coordinate 1 (V 1)) := rfl

theorem contract_ae (h k : CoefficientSpace) (V : JointFieldSpace) :
    contract h k V =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      inner ℝ (coordinate 0 (V 0) ω) h + inner ℝ (coordinate 1 (V 1) ω) k := by
  rw [contract_eq]
  exact (Lp.coeFn_add _ _).trans ((coefficientContract_ae h _).add (coefficientContract_ae k _))

theorem correction_eq (h k : CoefficientSpace) (V : JointFieldSpace)
    (hc : MemLp (IBMNativeContractionDomain.pairingFunction V (nativeField h k))
      2 IBMSourceLaws.jointMeasure) :
    IBMNativeContractionDomain.correction V (nativeField h k) hc = contract h k V := by
  apply Lp.ext
  filter_upwards [IBMNativeContractionDomain.correction_ae V (nativeField h k) hc,
    native_coordinates h k 0,native_coordinates h k 1,contract_ae h k V]
    with ω hc h0 h1 ht
  simp only [IBMNativeContractionDomain.pairingFunction] at hc
  have h0' : coordinate 0 (nativeField h k 0) ω = h := by simpa using h0
  have h1' : coordinate 1 (nativeField h k 1) ω = k := by simpa using h1
  rw [h0',h1'] at hc
  exact hc.trans ht.symm

end OperatorDerivativeRewrite.Foundation.IBMNativeDirectionalMaps
