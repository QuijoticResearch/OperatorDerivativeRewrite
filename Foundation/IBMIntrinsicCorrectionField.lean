import Foundation.IBMIntrinsicDualMultiplier

/-! Ordinary L2 correction fields for the intrinsic IBM Leibniz rule.
The scalar factor may be unbounded; the fixed native vector field is bounded. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicCorrectionField
open InfiniteGaussian (CoefficientSpace)
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicGraphDual
open IBMIntrinsicOperators IBMIntrinsicChainRule
open IBMNativeFieldMultiplier IBMNativeContraction IBMIntrinsicWeakLeibniz
open IBMIntrinsicGraphMultiplier IBMIntrinsicDualMultiplier
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

variable (v : JointVectorL2)
  (hv : MemLp (v : IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure)

def vectorProduct : JointL2 →L[ℝ] JointVectorL2 :=
  LinearMap.mkContinuous
    { toFun := fun g => lpSmul (r := 2) g (hv.toLp v)
      map_add' := by
        intro g h
        apply Lp.ext
        filter_upwards [lpSmul_coeFn (r := 2) (g+h) (hv.toLp v),
          lpSmul_coeFn (r := 2) g (hv.toLp v), lpSmul_coeFn (r := 2) h (hv.toLp v),
          Lp.coeFn_add g h,
          Lp.coeFn_add (lpSmul (r := 2) g (hv.toLp v)) (lpSmul (r := 2) h (hv.toLp v))]
          with ω hab ha hb hi ho
        rw [hab, ho]
        simp only [Pi.add_apply]
        rw [hi, ha, hb]
        exact add_smul _ _ _
      map_smul' := by
        intro c g
        apply Lp.ext
        filter_upwards [lpSmul_coeFn (r := 2) (c • g) (hv.toLp v),
          lpSmul_coeFn (r := 2) g (hv.toLp v), Lp.coeFn_smul c g,
          Lp.coeFn_smul c (lpSmul (r := 2) g (hv.toLp v))] with ω hc hg hi ho
        simp only [RingHom.id_apply]
        rw [hc, ho]
        simp only [Pi.smul_apply]
        rw [hi, hg]
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul] }
    ‖hv.toLp v‖ (fun g => (lpSmul_norm_le g (hv.toLp v)).trans_eq (mul_comm _ _))

theorem vectorProduct_ae (g : JointL2) :
    vectorProduct v hv g =ᵐ[IBMSourceLaws.jointMeasure] fun ω => g ω • v ω := by
  filter_upwards [lpSmul_coeFn (r := 2) g (hv.toLp v), hv.coeFn_toLp] with ω hp hv
  exact hp.trans (congrArg (fun z : CoefficientSpace => g ω • z) hv)

theorem vectorProduct_norm (g : JointL2) :
    ‖vectorProduct v hv g‖ ≤ ‖hv.toLp v‖ * ‖g‖ :=
  (lpSmul_norm_le g (hv.toLp v)).trans_eq (mul_comm _ _)

theorem vectorProduct_pairing (g : JointL2) (u : JointVectorL2) :
    inner ℝ (vectorProduct v hv g) u = inner ℝ g (contract v hv u) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [vectorProduct_ae v hv g, contract_ae v hv u] with ω hp hc
  rw [hp, hc, real_inner_smul_left, Real.inner_apply]

variable (V : JointFieldSpace)
  (hV : ∀ i : Fin 2, MemLp (coordinate i (V i) :
    IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure)

def correctionField : JointL2 →L[ℝ] JointFieldSpace :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => FieldSpace)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      (coordinate i).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (vectorProduct (coordinate i (V i)) (hV i)))

theorem correctionField_coordinate (g : JointL2) (i : Fin 2) :
    coordinate i (correctionField V hV g i) = vectorProduct (coordinate i (V i)) (hV i) g :=
  (coordinate i).apply_symm_apply _

theorem correctionField_ae (g : JointL2) (i : Fin 2) :
    coordinate i (correctionField V hV g i) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => g ω • coordinate i (V i) ω := by
  rw [correctionField_coordinate]
  exact vectorProduct_ae _ _ g

theorem correctionField_channel_norm (g : JointL2) (i : Fin 2) :
    ‖correctionField V hV g i‖ ≤ ‖(hV i).toLp (coordinate i (V i))‖ * ‖g‖ := by
  rw [← (coordinate i).norm_map, correctionField_coordinate]
  exact vectorProduct_norm _ _ g

theorem correctionField_bounded_agreement (g : JointL2)
    (hg : MemLp (g : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    correctionField V hV g = multiply g hg V := by
  apply PiLp.ext
  intro i
  apply (coordinate i).injective
  exact Lp.ext ((correctionField_ae V hV g i).trans (multiply_ae g hg V i).symm)

theorem pointCorrection_actual_ae (t : ℝ≥0) (i : Fin 2) :
    coordinate i (correctionField V hV (intrinsicCurve t : JointL2) i)
      =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
        IBMConstructedSources.ibmValue t ω • coordinate i (V i) ω := by
  filter_upwards [correctionField_ae V hV (intrinsicCurve t : JointL2) i,
    joint_point_actual_ae t] with ω hc hx
  exact hc.trans (congrArg (fun z : ℝ => z • coordinate i (V i) ω) hx)

theorem pointCorrection_continuous :
    Continuous (fun t : ℝ≥0 => correctionField V hV (intrinsicCurve t : JointL2)) :=
  (correctionField V hV).continuous.comp
    (IntrinsicSpace.subtypeL.continuous.comp intrinsicCurve_continuous)

theorem correctionField_pairing (g : JointL2) (u : JointFieldSpace) :
    inner ℝ (correctionField V hV g) u = inner ℝ g (correction V hV u) := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, correction, inner_add_right]
  apply congrArg₂ (fun a b : ℝ => a+b)
  · exact ((coordinate 0).inner_map_map _ _).symm.trans
      ((congrArg (fun z : JointVectorL2 => inner ℝ z (coordinate 0 (u 0)))
        (correctionField_coordinate V hV g 0)).trans (vectorProduct_pairing _ _ g _))
  · exact ((coordinate 1).inner_map_map _ _).symm.trans
      ((congrArg (fun z : JointVectorL2 => inner ℝ z (coordinate 1 (u 1)))
        (correctionField_coordinate V hV g 1)).trans (vectorProduct_pairing _ _ g _))

attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative

variable (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
  (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
  (hDf : ∀ i : Fin 2, MemLp (coordinate i (jointDerivative f i) :
    IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure)

theorem correctionFunctional_embed (g : IntrinsicSpace) :
    correctionFunctional f C hC hf hDf g =
      embed (correctionField (jointDerivative f) hDf (g : JointL2)) := by
  ext w
  have he : correctionFunctional f C hC hf hDf g (testOf (asDomain w)) =
      embed (correctionField (jointDerivative f) hDf (g : JointL2)) (testOf (asDomain w)) := by
    exact (correctionFunctional_actual f C hC hf hDf g (asDomain w)).trans
      (correctionField_pairing _ _ (g : JointL2) (asDomain w)).symm
  simpa only [testOf_asDomain] using he

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicCorrectionField
