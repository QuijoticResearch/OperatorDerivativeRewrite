import Foundation.IBMIntrinsicGraphDual
import Foundation.IBMNativeWeightedDivergence

/-! Full intrinsic-adjoint test Leibniz identities for actual IBM observables.
The rough factor need not belong to the original derivative domain. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicWeakLeibniz
open InfiniteGaussian (CoefficientSpace)
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative
open IBMNativeFieldMultiplier IBMNativeProductOperators IBMNativeContraction
open IBMIntrinsicGraphDual
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative

def scalarMultiplier (f : IntrinsicSpace)
    (hf : MemLp ((f : JointL2) : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    IntrinsicSpace →L[ℝ] IntrinsicSpace :=
  IntrinsicSpace.orthogonalProjectionOnto.comp
    ((boundedMultiplier (f : JointL2) hf).comp IntrinsicSpace.subtypeL)

theorem scalarMultiplier_symmetric (f : IntrinsicSpace)
    (hf : MemLp ((f : JointL2) : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (g h : IntrinsicSpace) :
    inner ℝ (scalarMultiplier f hf g) h = inner ℝ g (scalarMultiplier f hf h) := by
  calc
    _ = inner ℝ (boundedMultiplier (f : JointL2) hf (g : JointL2)) (h : JointL2) :=
      IBMNativeWeightedDivergence.projection_pairing _ h
    _ = inner ℝ (g : JointL2) (boundedMultiplier (f : JointL2) hf (h : JointL2)) :=
      boundedMultiplier_symmetric _ _ _ _
    _ = _ := by
      rw [real_inner_comm]
      exact (IBMNativeWeightedDivergence.projection_pairing _ g).symm.trans
        (real_inner_comm _ _)

theorem scalarMultiplier_actual_ae (f g : IntrinsicSpace)
    (hf : MemLp ((f : JointL2) : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    ((scalarMultiplier f hf g : IntrinsicSpace) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure] fun ω => (f : JointL2) ω * (g : JointL2) ω := by
  have hm : boundedMultiplier (f : JointL2) hf (g : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure] fun ω => (f : JointL2) ω * (g : JointL2) ω := by
    simpa only [smul_eq_mul] using boundedMultiplier_coeFn (f : JointL2) hf (g : JointL2)
  have ho : boundedMultiplier (f : JointL2) hf (g : JointL2) ∈ IntrinsicSpace :=
    (f.property.mul g.property).congr hm.symm
  have he := IntrinsicSpace.orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨boundedMultiplier (f : JointL2) hf (g : JointL2), ho⟩ : IntrinsicSpace)
  have hs : scalarMultiplier f hf g =
      (⟨boundedMultiplier (f : JointL2) hf (g : JointL2), ho⟩ : IntrinsicSpace) := he
  have hv := congrArg (fun z : IntrinsicSpace => (z : JointL2)) hs
  rw [hv]
  exact hm

variable (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
  (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
  (hDf : ∀ i : Fin 2, MemLp (coordinate i (jointDerivative f i) :
    IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure)

def weightedTest (v : jointDivergence.domain) : Tests :=
  testOf ⟨multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) v,
    IBMNativeWeightedDivergence.weighted_mem f C hC hf hDf v⟩

theorem weak_leibniz (g : IntrinsicSpace) (v : jointDivergence.domain) :
    weakDerivative (scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf) g) (testOf v) =
      weakDerivative g (weightedTest f C hC hf hDf v) +
        inner ℝ (g : JointL2) (correction (jointDerivative f) hDf v) := by
  let w : jointDivergence.domain :=
    ⟨multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) v,
      IBMNativeWeightedDivergence.weighted_mem f C hC hf hDf v⟩
  have hv : jointDivergence w =
      scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf) (jointDivergence v) -
        IntrinsicSpace.orthogonalProjectionOnto (correction (jointDerivative f) hDf v) := by
    rw [IBMNativeWeightedDivergence.weighted_value f C hC hf hDf v]
    exact IntrinsicSpace.orthogonalProjectionOnto.map_sub _ _
  have he : scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf) (jointDivergence v) =
      jointDivergence w + IntrinsicSpace.orthogonalProjectionOnto
        (correction (jointDerivative f) hDf v) := by rw [hv]; abel
  have hp : inner ℝ g (IntrinsicSpace.orthogonalProjectionOnto
      (correction (jointDerivative f) hDf v)) =
      inner ℝ (g : JointL2) (correction (jointDerivative f) hDf v) :=
    (real_inner_comm _ _).trans
      ((IBMNativeWeightedDivergence.projection_pairing _ g).trans (real_inner_comm _ _))
  calc
    _ = inner ℝ (scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf) g)
        (jointDivergence v) := test_pairing _ v
    _ = inner ℝ g (scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf)
        (jointDivergence v)) := scalarMultiplier_symmetric _ _ _ _
    _ = inner ℝ g (jointDivergence w + IntrinsicSpace.orthogonalProjectionOnto
        (correction (jointDerivative f) hDf v)) := congrArg (fun z => inner ℝ g z) he
    _ = inner ℝ g (jointDivergence w) + inner ℝ g
        (IntrinsicSpace.orthogonalProjectionOnto (correction (jointDerivative f) hDf v)) :=
      inner_add_right _ _ _
    _ = _ := congrArg₂ (fun x y : ℝ => x+y) rfl hp

theorem point_product_actual_ae (t : ℝ≥0) :
    ((scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf) (intrinsicCurve t) :
      IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => (((f : IntrinsicSpace) : JointL2) ω) * IBMConstructedSources.ibmValue t ω := by
  filter_upwards [scalarMultiplier_actual_ae (f : IntrinsicSpace) (intrinsicCurve t)
    (bounded_memLp f C hf), joint_point_actual_ae t] with ω hm hx
  exact hm.trans (congrArg (fun z : ℝ => (((f : IntrinsicSpace) : JointL2) ω) * z) hx)

theorem point_weak_leibniz (t : ℝ≥0) (v : jointDivergence.domain) :
    weakDerivative (scalarMultiplier (f : IntrinsicSpace) (bounded_memLp f C hf)
      (intrinsicCurve t)) (testOf v) =
      pointDerivative t (weightedTest f C hC hf hDf v) +
        ∫ ω, IBMConstructedSources.ibmValue t ω * correction (jointDerivative f) hDf v ω
          ∂IBMSourceLaws.jointMeasure := by
  have hi : inner ℝ (intrinsicCurve t : JointL2) (correction (jointDerivative f) hDf v) =
      ∫ ω, IBMConstructedSources.ibmValue t ω * correction (jointDerivative f) hDf v ω
        ∂IBMSourceLaws.jointMeasure := by
    rw [L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [joint_point_actual_ae t] with ω hx
    change inner ℝ (jointRealization (IBMRandomTimeHilbert.randomSourceL2 t) ω) _ = _
    rw [hx, Real.inner_apply]
  exact (weak_leibniz f C hC hf hDf (intrinsicCurve t) v).trans
    (congrArg (fun z : ℝ => pointDerivative t (weightedTest f C hC hf hDf v) + z) hi)

theorem point_correction_integrable (t : ℝ≥0) (v : jointDivergence.domain) :
    Integrable (fun ω => IBMConstructedSources.ibmValue t ω *
      correction (jointDerivative f) hDf v ω) IBMSourceLaws.jointMeasure := by
  apply ((Lp.memLp (intrinsicCurve t : JointL2)).integrable_mul
    (Lp.memLp (correction (jointDerivative f) hDf v))).congr
  filter_upwards [joint_point_actual_ae t] with ω hx
  change jointRealization (IBMRandomTimeHilbert.randomSourceL2 t) ω * _ = _
  rw [hx]

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicWeakLeibniz
