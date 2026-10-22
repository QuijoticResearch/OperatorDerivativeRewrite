import Foundation.IBMIntrinsicGraphMultiplier

/-! Actual native multiplication extended to the WHOLE intrinsic graph dual,
with a bounded correction identified by the existing stochastic contraction. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicDualMultiplier
open InfiniteGaussian (CoefficientSpace)
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicGraphDual
open IBMNativeFieldMultiplier IBMNativeProductOperators IBMIntrinsicWeakLeibniz
open IBMIntrinsicGraphMultiplier
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative
  IBMIntrinsicGraphMultiplier.graphMultiplier

variable (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
  (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
  (hDf : ∀ i : Fin 2, MemLp (coordinate i (jointDerivative f i) :
    IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure)

def dualMultiplier : StrongDual ℝ Tests →L[ℝ] StrongDual ℝ Tests :=
  (graphMultiplier f C hC hf hDf).precomp ℝ

theorem dualMultiplier_apply (F : StrongDual ℝ Tests) (w : Tests) :
    dualMultiplier f C hC hf hDf F w = F (graphMultiplier f C hC hf hDf w) := rfl

theorem dualMultiplier_testOf (F : StrongDual ℝ Tests) (v : jointDivergence.domain) :
    dualMultiplier f C hC hf hDf F (testOf v) = F (weightedTest f C hC hf hDf v) :=
  congrArg F (graphMultiplier_testOf f C hC hf hDf v)

theorem dualMultiplier_norm (F : StrongDual ℝ Tests) :
    ‖dualMultiplier f C hC hf hDf F‖ ≤ ‖F‖ * ‖graphMultiplier f C hC hf hDf‖ :=
  ContinuousLinearMap.opNorm_comp_le _ _

theorem dualMultiplier_embed (V : JointFieldSpace) :
    dualMultiplier f C hC hf hDf (embed V) =
      embed (multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) V) := by
  ext w
  change inner ℝ V (testField (graphMultiplier f C hC hf hDf w)) = _
  exact (congrArg (fun z : JointFieldSpace => inner ℝ V z)
    (graphMultiplier_field f C hC hf hDf w)).trans
      (multiply_symmetric _ _ V (testField w)).symm

def correctionTest : Tests →L[ℝ] IntrinsicSpace :=
  (scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf)).comp testValue -
    testValue.comp (graphMultiplier f C hC hf hDf)

theorem correctionTest_actual (v : jointDivergence.domain) :
    correctionTest f C hC hf hDf (testOf v) =
      IntrinsicSpace.orthogonalProjectionOnto
        (IBMNativeContraction.correction (jointDerivative f) hDf v) := by
  have hv : testValue (graphMultiplier f C hC hf hDf (testOf v)) =
      IBMNativeWeightedDivergence.output f (bounded_memLp f C hf) hDf v :=
    (congrArg testValue (graphMultiplier_testOf f C hC hf hDf v)).trans
      (IBMNativeWeightedDivergence.weighted_value f C hC hf hDf v)
  change scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf) (jointDivergence v) -
    testValue (graphMultiplier f C hC hf hDf (testOf v)) = _
  rw [hv]
  let q : JointL2 := boundedMultiplier ((f : IntrinsicSpace) : JointL2)
    (bounded_memLp f C hf) ((jointDivergence v : IntrinsicSpace) : JointL2)
  change IntrinsicSpace.orthogonalProjectionOnto q -
    IntrinsicSpace.orthogonalProjectionOnto
      (q - IBMNativeContraction.correction (jointDerivative f) hDf v) = _
  rw [← map_sub]
  congr 1
  abel

def correctionFunctional : IntrinsicSpace →L[ℝ] StrongDual ℝ Tests :=
  ((correctionTest f C hC hf hDf).precomp ℝ).comp (innerSL ℝ)

theorem correctionFunctional_actual (g : IntrinsicSpace) (v : jointDivergence.domain) :
    correctionFunctional f C hC hf hDf g (testOf v) =
      inner ℝ (g : JointL2) (IBMNativeContraction.correction (jointDerivative f) hDf v) := by
  change inner ℝ g (correctionTest f C hC hf hDf (testOf v)) = _
  rw [correctionTest_actual]
  exact (real_inner_comm _ _).trans
    ((IBMNativeWeightedDivergence.projection_pairing _ g).trans (real_inner_comm _ _))

theorem full_dual_leibniz (g : IntrinsicSpace) :
    weakDerivative (scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf) g) =
      dualMultiplier f C hC hf hDf (weakDerivative g) +
        correctionFunctional f C hC hf hDf g := by
  apply ContinuousLinearMap.ext
  intro w
  have he : weakDerivative (scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf) g)
      (testOf (asDomain w)) =
      dualMultiplier f C hC hf hDf (weakDerivative g) (testOf (asDomain w)) +
        correctionFunctional f C hC hf hDf g (testOf (asDomain w)) := by
    exact (weak_leibniz f C hC hf hDf g (asDomain w)).trans
      (congrArg₂ (fun x y : ℝ => x+y)
        (dualMultiplier_testOf f C hC hf hDf (weakDerivative g) (asDomain w)).symm
        (correctionFunctional_actual f C hC hf hDf g (asDomain w)).symm)
  exact (congrArg (fun z : Tests =>
    weakDerivative (scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf) g) z)
      (testOf_asDomain w).symm).trans
    (he.trans (congrArg (fun z : Tests =>
      dualMultiplier f C hC hf hDf (weakDerivative g) z +
        correctionFunctional f C hC hf hDf g z) (testOf_asDomain w)))

theorem dualMultiplier_tendsto {F : ℕ → StrongDual ℝ Tests} {G : StrongDual ℝ Tests}
    (hF : Tendsto F atTop (𝓝 G)) :
    Tendsto (fun n => dualMultiplier f C hC hf hDf (F n)) atTop
      (𝓝 (dualMultiplier f C hC hf hDf G)) :=
  (dualMultiplier f C hC hf hDf).continuous.tendsto G |>.comp hF

theorem multiplied_gradients_limit (g : IntrinsicSpace) (u : ℕ → jointDerivative.domain)
    (hu : Tendsto (fun n => (u n : IntrinsicSpace)) atTop (𝓝 g)) :
    Tendsto (fun n => embed (multiply ((f : IntrinsicSpace) : JointL2)
      (bounded_memLp f C hf) (jointDerivative (u n)))) atTop
      (𝓝 (dualMultiplier f C hC hf hDf (weakDerivative g))) := by
  have h := dualMultiplier_tendsto f C hC hf hDf (graph_dual_limit g u hu)
  simpa only [dualMultiplier_embed] using h

theorem multiplied_gradients_error (g : IntrinsicSpace) (u : jointDerivative.domain) :
    ‖embed (multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf)
      (jointDerivative u)) - dualMultiplier f C hC hf hDf (weakDerivative g)‖ ≤
      ‖(u : IntrinsicSpace) - g‖ * ‖graphMultiplier f C hC hf hDf‖ := by
  have he : dualMultiplier f C hC hf hDf (embed (jointDerivative u) - weakDerivative g) =
      embed (multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf)
        (jointDerivative u)) - dualMultiplier f C hC hf hDf (weakDerivative g) :=
    ((dualMultiplier f C hC hf hDf).map_sub _ _).trans
      (congrArg (fun z : StrongDual ℝ Tests =>
        z - dualMultiplier f C hC hf hDf (weakDerivative g))
          (dualMultiplier_embed f C hC hf hDf (jointDerivative u)))
  calc
    _ = ‖dualMultiplier f C hC hf hDf (embed (jointDerivative u) - weakDerivative g)‖ :=
      (congrArg Norm.norm he).symm
    _ ≤ _ := (dualMultiplier_norm f C hC hf hDf _).trans
      (mul_le_mul_of_nonneg_right (graph_dual_error g u) (norm_nonneg _))

theorem point_correction_actual (t : ℝ≥0) (v : jointDivergence.domain) :
    correctionFunctional f C hC hf hDf (intrinsicCurve t) (testOf v) =
      ∫ ω, IBMConstructedSources.ibmValue t ω *
        IBMNativeContraction.correction (jointDerivative f) hDf v ω
          ∂IBMSourceLaws.jointMeasure := by
  have hi : inner ℝ (intrinsicCurve t : JointL2)
      (IBMNativeContraction.correction (jointDerivative f) hDf v) =
      ∫ ω, IBMConstructedSources.ibmValue t ω *
        IBMNativeContraction.correction (jointDerivative f) hDf v ω
          ∂IBMSourceLaws.jointMeasure := by
    rw [L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [joint_point_actual_ae t] with ω hx
    change inner ℝ (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t) ω) _ = _
    rw [hx, Real.inner_apply]
  exact (correctionFunctional_actual f C hC hf hDf (intrinsicCurve t) v).trans hi

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicDualMultiplier
