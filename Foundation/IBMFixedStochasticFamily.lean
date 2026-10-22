import Foundation.IBMTerminalSelfRepresentation
import Foundation.SeparableHilbertEmbedding
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! A fixed countable family of ACTUAL predictable IBM integrals.
The original full initial germ is retained. No causal-gradient formula is asserted. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFixedStochasticFamily
open IBMTimeAveragedObservable IBMIntrinsicRightGerm IBMObservedTerminalMartingale
open IBMPredictableIntegralObservable IBMPredictableLpDictionary IBMFullPredictableIntegral
open IBMTerminalSelfRepresentation
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem joint_secondCountable : SecondCountableTopology JointL2 := by
  change SecondCountableTopology (Lp ℝ 2 IBMSourceLaws.jointMeasure)
  infer_instance
local instance : SecondCountableTopology JointL2 := joint_secondCountable

def remainderSpace : Submodule ℝ JointL2 := IntrinsicSpace ⊓ (rightPast 0)ᗮ

theorem remainderSpace_closed : IsClosed (remainderSpace : Set JointL2) :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).inter (Submodule.isClosed_orthogonal _)
local instance : CompleteSpace remainderSpace := remainderSpace_closed.completeSpace_coe

def remainder (f : IntrinsicSpace) : remainderSpace :=
  ⟨(f : JointL2)-channelClass (f : JointL2) 0,
    ⟨IntrinsicSpace.sub_mem f.property (rightPast_le_intrinsic 0
      ((rightPast 0).starProjection_apply_mem _)),
      (rightPast 0).sub_starProjection_mem_orthogonal (f : JointL2)⟩⟩

def basisSet : Set remainderSpace := Classical.choose (exists_hilbertBasis ℝ remainderSpace)

def basis : HilbertBasis basisSet ℝ remainderSpace :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℝ remainderSpace))

theorem basis_countable : Countable basisSet :=
  SeparableHilbertEmbedding.orthonormal_index_countable basis.orthonormal

def terminal (i : basisSet) : IntrinsicSpace :=
  ⟨(basis i : JointL2), (basis i).property.1⟩

theorem terminal_initial_zero (i : basisSet) : channelClass (terminal i : JointL2) 0 = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff (rightPast 0)).mpr (basis i).property.2

def integrand (i : basisSet) : PredictableL2 (terminal i : JointL2) :=
  Classical.choose (self_representation (terminal i))

theorem integral_integrand (i : basisSet) :
    integral (terminal i : JointL2) (integrand i) = (terminal i : JointL2) := by
  have h := Classical.choose_spec (self_representation (terminal i))
  simpa only [integrand, terminal_initial_zero, sub_zero] using h

theorem terminal_norm (i : basisSet) : ‖(terminal i : JointL2)‖ = 1 :=
  basis.orthonormal.1 i

theorem integrand_norm (i : basisSet) : ‖integrand i‖ = 1 :=
  ((integral (terminal i : JointL2)).norm_map (integrand i)).symm.trans
    ((congrArg Norm.norm (integral_integrand i)).trans (terminal_norm i))

def coefficient (f : IntrinsicSpace) (i : basisSet) : ℝ := basis.repr (remainder f) i

theorem coefficient_pairing (f : IntrinsicSpace) (i : basisSet) :
    coefficient f i = inner ℝ (terminal i : JointL2) (f : JointL2) := by
  have ho : inner ℝ (terminal i : JointL2) (channelClass (f : JointL2) 0) = 0 := by
    exact (Submodule.mem_orthogonal' _ _).mp (basis i).property.2 _
      ((rightPast 0).starProjection_apply_mem _)
  rw [coefficient, HilbertBasis.repr_apply_apply]
  change inner ℝ (terminal i : JointL2) ((f : JointL2)-channelClass (f : JointL2) 0) = _
  rw [inner_sub_right, ho, sub_zero]

theorem stochastic_reconstruction (f : IntrinsicSpace) :
    HasSum (fun i : basisSet => integral (terminal i : JointL2)
      (coefficient f i • integrand i)) ((f : JointL2)-channelClass (f : JointL2) 0) := by
  have h := (basis.hasSum_repr (remainder f)).mapL remainderSpace.subtypeL
  change HasSum (fun i : basisSet => coefficient f i • (terminal i : JointL2))
    ((f : JointL2)-channelClass (f : JointL2) 0) at h
  simpa only [map_smul, integral_integrand] using h

theorem coefficient_energy (f : IntrinsicSpace) :
    HasSum (fun i : basisSet => (coefficient f i)^2) (‖remainder f‖^2) := by
  convert basis.hasSum_inner_mul_inner (remainder f) (remainder f) using 1
  · ext i
    rw [coefficient, HilbertBasis.repr_apply_apply, pow_two, real_inner_comm (remainder f)]
  · exact (real_inner_self_eq_norm_sq _).symm

theorem stochastic_energy (f : IntrinsicSpace) :
    HasSum (fun i : basisSet => ‖coefficient f i • integrand i‖^2) (‖remainder f‖^2) := by
  simpa only [norm_smul, integrand_norm, mul_one, Real.norm_eq_abs, sq_abs] using coefficient_energy f

theorem stochastic_orthonormal :
    Orthonormal ℝ (fun i : basisSet => integral (terminal i : JointL2) (integrand i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [integral_integrand, integral_integrand]
  change inner ℝ (basis i) (basis j) = _
  exact (orthonormal_iff_ite.mp basis.orthonormal) i j

theorem coefficients_zero_iff (f : IntrinsicSpace) :
    (∀ i : basisSet, coefficient f i = 0) ↔ (f : JointL2) ∈ rightPast 0 := by
  constructor
  · intro hz
    have h := stochastic_reconstruction f
    have h0 : HasSum (fun i : basisSet => integral (terminal i : JointL2)
        (coefficient f i • integrand i)) 0 := by
      simpa only [hz, zero_smul, map_zero] using (show HasSum (fun _ : basisSet => (0 : JointL2)) 0 from hasSum_zero)
    have he := sub_eq_zero.mp (h.unique h0)
    exact Submodule.starProjection_eq_self_iff.mp he.symm
  · intro hf i
    rw [coefficient_pairing]
    exact (Submodule.mem_orthogonal' _ _).mp (basis i).property.2 (f : JointL2) hf

end OperatorDerivativeRewrite.Foundation.IBMFixedStochasticFamily
