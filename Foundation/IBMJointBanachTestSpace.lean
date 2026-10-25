import Foundation.IBMJointCompletedTestGraph
import Foundation.IBMNativeWeakObstruction

/-! A faithful Banach test space in ORIGINAL joint L2, with its stronger
quotient norm and actual native scalar reconstruction. It is not all intrinsic
L2, and the Hilbert weak-convergence obstruction is preserved. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMJointBanachTestSpace
open InfiniteGaussian IBMTimeAveragedObservable IBMJointCompletedTestGraph
open IBMJointMixedSpatialTransport IBMRawGridSecondChaos

instance joint_kernel_closed : IsClosed (jointMap.ker : Set Graph) := jointMap.isClosed_ker

abbrev Tests := Graph ⧸ jointMap.ker

def projection : Graph →L[ℝ] Tests := jointMap.ker.mkQL

def realize : Tests →L[ℝ] JointL2 := jointMap.ker.liftQL jointMap le_rfl

theorem realize_projection (p : Graph) : realize (projection p) = jointMap p := rfl

theorem realize_injective : Function.Injective realize := by
  apply LinearMap.ker_eq_bot.mp
  change LinearMap.ker (jointMap.ker.liftQ jointMap.toLinearMap le_rfl) = ⊥
  exact jointMap.ker.ker_liftQ_eq_bot jointMap.toLinearMap le_rfl le_rfl

def distribution (T : ℝ≥0) (hT : 0 < T) : Tests →L[ℝ] ℝ :=
  jointMap.ker.liftQL (limitFunctional T) (joint_kernel_le_limit_kernel T hT)

theorem distribution_projection (T : ℝ≥0) (hT : 0 < T) (p : Graph) :
    distribution T hT (projection p) = limitFunctional T p := rfl

def nativeFunctional (T : ℝ≥0) (N : ℕ) : Tests →L[ℝ] ℝ :=
  (innerSL ℝ (jointRealization (sourceGrid (T/(N+1)) (N+1)))).comp realize

theorem native_tendsto (T : ℝ≥0) (hT : 0 < T) (x : Tests) :
    Tendsto (fun N => nativeFunctional T N x) atTop (𝓝 (distribution T hT x)) := by
  refine Submodule.Quotient.induction_on jointMap.ker x ?_
  intro p
  change Tendsto (fun N => finiteFunctional T N p) atTop (𝓝 (limitFunctional T p))
  exact functional_tendsto T hT p

theorem distribution_unique (T : ℝ≥0) (hT : 0 < T) (f : Tests → ℝ)
    (hf : ∀ x, Tendsto (fun N => nativeFunctional T N x) atTop (𝓝 (f x))) :
    f = distribution T hT := by
  funext x
  exact tendsto_nhds_unique (hf x) (native_tendsto T hT x)

def test (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) : Tests := projection (generator g h a)

theorem realize_test (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) :
    realize (test g h a) = jointTest g h a := rfl

theorem distribution_test (T : ℝ≥0) (hT : 0 < T) (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) :
    distribution T hT (test g h a) = limitingPairing g h a T := by
  change L1.integralCLM (IBMSpatialSignedRandomTests.limitOperator T (symbol g h a)) = _
  simp only [← L1.integral_eq,L1.integral_eq_integral,limitingPairing]

local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _ IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem exists_intrinsic_outside_range (T : ℝ≥0) (hT : 0 < T) :
    ∃ v : IntrinsicSpace, ∀ x : Tests, realize x ≠ (v:JointL2) := by
  obtain ⟨v,hv⟩ := IBMNativeWeakObstruction.exists_original_nonconvergent_observable T hT
  refine ⟨v,fun x hx => ?_⟩
  apply hv (distribution T hT x)
  have he (N : ℕ) : nativeFunctional T N x = inner ℝ
      (IBMJointIntrinsicDerivative.jointDivergence (IBMRawGridCompensation.gridInput (T/(N+1)) (N+1))) v := by
    change inner ℝ (jointRealization (sourceGrid (T/(N+1)) (N+1))) (realize x) = _
    rw [hx,native_grid_value]
    exact (IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right v
      (jointRealization (sourceGrid (T/(N+1)) (N+1)))).symm
  exact (native_tendsto T hT x).congr' (Eventually.of_forall he)

theorem intrinsic_native_tendsto (T : ℝ≥0) (hT : 0 < T) (x : Tests)
    (v : IntrinsicSpace) (hv : (v:JointL2) = realize x) :
    Tendsto (fun N : ℕ => inner ℝ
      (IBMJointIntrinsicDerivative.jointDivergence (IBMRawGridCompensation.gridInput (T/(N+1)) (N+1))) v)
      atTop (𝓝 (distribution T hT x)) := by
  have he (N : ℕ) : inner ℝ
      (IBMJointIntrinsicDerivative.jointDivergence (IBMRawGridCompensation.gridInput (T/(N+1)) (N+1))) v =
        nativeFunctional T N x := by
    rw [native_grid_value]
    have hp := IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right v
      (jointRealization (sourceGrid (T/(N+1)) (N+1)))
    rw [hp,hv]
    rfl
  exact (native_tendsto T hT x).congr' (Eventually.of_forall fun N => (he N).symm)

end OperatorDerivativeRewrite.Foundation.IBMJointBanachTestSpace
