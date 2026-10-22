import Foundation.IBMClockDerivativeReflection

/-! Full observable weights times deterministic clock directions lie in the actual divergence kernel. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMObservableClockKernel
open InfiniteGaussian (CoefficientSpace)
open IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative IBMIntrinsicChainRule
open IBMNativeFieldMultiplier IBMNativeDirectionalMaps IBMClockDerivativeReflection
open IBMClockInnovationObstruction
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

theorem contraction_reflection (k : CoefficientSpace) (V : JointVectorL2) :
    jointReflection (coefficientContract k V) = coefficientContract k (jointVectorReflection V) := by
  apply Lp.ext
  have ht := IBMClockSignSymmetry.reflectClock_preserving.quasiMeasurePreserving.ae_eq_comp
    (coefficientContract_ae k V)
  filter_upwards [jointReflection_ae (coefficientContract k V),ht,
    coefficientContract_ae k (jointVectorReflection V),jointVectorReflection_ae V]
    with ω hj ht hc hv
  change coefficientContract k V (IBMClockSignSymmetry.reflectClock ω) =
    inner ℝ (V (IBMClockSignSymmetry.reflectClock ω)) k at ht
  rw [hj,ht,hc,hv]

theorem clock_contract_eq (k : CoefficientSpace) (G : JointFieldSpace) :
    contract 0 k G = coefficientContract k (uncurryField (G 1)) := by
  have hz : coefficientContract (0 : CoefficientSpace) (coordinate 0 (G 0)) = 0 := by
    apply Lp.ext
    filter_upwards [coefficientContract_ae (0 : CoefficientSpace) (coordinate 0 (G 0)),
      Lp.coeFn_zero (E := ℝ) (p := 2) (μ := IBMSourceLaws.jointMeasure)] with ω hc ho
    rw [hc,inner_zero_right,ho]
    rfl
  rw [contract_eq,hz,zero_add,coordinate_one]

theorem clock_contract_odd (k : CoefficientSpace) (f : jointDerivative.domain) :
    jointReflection (contract 0 k (jointDerivative f)) = -contract 0 k (jointDerivative f) := by
  rw [clock_contract_eq,contraction_reflection,observable_clock_odd,map_neg]

theorem projected_clock_zero (k : CoefficientSpace) (f : jointDerivative.domain) :
    IntrinsicSpace.orthogonalProjectionOnto (contract 0 k (jointDerivative f)) = 0 := by
  apply Subtype.ext
  change IntrinsicSpace.starProjection (contract 0 k (jointDerivative f)) = 0
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero IntrinsicSpace.zero_mem
  intro F hF
  rw [sub_zero]
  exact odd_inner_zero _ (clock_contract_odd k f) F hF

theorem coefficient_pairing (h : CoefficientSpace) (F : JointL2) (V : JointVectorL2) :
    inner ℝ (coefficientLift h F) V = inner ℝ F (coefficientContract h V) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientLift_ae h F,coefficientContract_ae h V] with ω hl hc
  rw [hl,hc,real_inner_smul_left,Real.inner_apply]
  rw [real_inner_comm h (V ω)]

theorem coordinate_inner (U G : JointFieldSpace) :
    inner ℝ U G = inner ℝ (coordinate 0 (U 0)) (coordinate 0 (G 0)) +
      inner ℝ (coordinate 1 (U 1)) (coordinate 1 (G 1)) := by
  have he : inner ℝ U G = inner ℝ (U 0) (G 0) + inner ℝ (U 1) (G 1) := by
    rw [PiLp.inner_apply,Fin.sum_univ_two]
  exact he.trans (congrArg₂ (fun a b : ℝ => a+b)
    ((coordinate 0).inner_map_map _ _).symm ((coordinate 1).inner_map_map _ _).symm)

theorem field_pairing (h k : CoefficientSpace) (F : JointL2) (G : JointFieldSpace) :
    inner ℝ (lift h k F) G = inner ℝ F (contract h k G) := by
  have h0 : coordinate 0 (lift h k F 0) = coefficientLift h F := lift_coordinate h k F 0
  have h1 : coordinate 1 (lift h k F 1) = coefficientLift k F := lift_coordinate h k F 1
  have he : inner ℝ (lift h k F) G =
      inner ℝ (coefficientLift h F) (coordinate 0 (G 0)) +
      inner ℝ (coefficientLift k F) (coordinate 1 (G 1)) :=
    (coordinate_inner (lift h k F) G).trans
      (congrArg₂ (fun a b : ℝ => a+b)
        (congrArg (fun z : JointVectorL2 => inner ℝ z (coordinate 0 (G 0))) h0)
        (congrArg (fun z : JointVectorL2 => inner ℝ z (coordinate 1 (G 1))) h1))
  have hs : inner ℝ F (contract h k G) =
      inner ℝ F (coefficientContract h (coordinate 0 (G 0))) +
      inner ℝ F (coefficientContract k (coordinate 1 (G 1))) :=
    (congrArg (fun z : JointL2 => inner ℝ F z) (contract_eq h k G)).trans (inner_add_right _ _ _)
  exact he.trans ((congrArg₂ (fun a b : ℝ => a+b)
    (coefficient_pairing h F (coordinate 0 (G 0)))
    (coefficient_pairing k F (coordinate 1 (G 1)))).trans hs.symm)

theorem clock_pairing_zero (k : CoefficientSpace) (F : IntrinsicSpace)
    (g : jointDerivative.domain) : inner ℝ (lift 0 k (F : JointL2)) (jointDerivative g) = 0 := by
  have hp := IBMNativeWeightedDivergence.projection_pairing (contract 0 k (jointDerivative g)) F
  rw [projected_clock_zero,inner_zero_left] at hp
  exact (field_pairing 0 k (F : JointL2) (jointDerivative g)).trans
    ((real_inner_comm _ _).trans hp.symm)

theorem observable_clock_mem (k : CoefficientSpace) (F : IntrinsicSpace) :
    lift 0 k (F : JointL2) ∈ jointDivergence.domain :=
  jointDerivative.mem_adjoint_domain_of_exists _
    ⟨0,fun g => (inner_zero_left _).trans (clock_pairing_zero k F g).symm⟩

theorem observable_clock_value (k : CoefficientSpace) (F : IntrinsicSpace) :
    jointDivergence ⟨lift 0 k (F : JointL2),observable_clock_mem k F⟩ = 0 :=
  jointDerivative.adjoint_apply_eq jointDerivative_dense _
    (fun g => (inner_zero_left _).trans (clock_pairing_zero k F g).symm)

theorem clock_lift_ne_zero (k : CoefficientSpace) (hk : k ≠ 0) (F : IntrinsicSpace)
    (hF : (F : JointL2) ≠ 0) : lift 0 k (F : JointL2) ≠ 0 := by
  intro hz
  have hc := lift_ae 0 k (F : JointL2) 1
  rw [hz] at hc
  simp only [PiLp.zero_apply,map_zero,show ¬(1 : Fin 2)=0 from by decide,ite_false] at hc
  apply hF
  apply Lp.ext
  filter_upwards [hc,Lp.coeFn_zero (E := CoefficientSpace) (p := 2) (μ := IBMSourceLaws.jointMeasure),
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := IBMSourceLaws.jointMeasure)] with ω hc hv hs
  have he : (F : JointL2) ω • k = 0 := hc.symm.trans hv
  have hf : (F : JointL2) ω = 0 := (smul_eq_zero.mp he).resolve_right hk
  exact hf.trans hs.symm

end OperatorDerivativeRewrite.Foundation.IBMObservableClockKernel
