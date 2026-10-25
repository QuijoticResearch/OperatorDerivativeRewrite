import Foundation.IBMJointRandomGraphIdentity
import Foundation.IBMJointTestNormBounds

/-! A clock-L1-valued native reconstruction on the SAME faithful Banach
joint test space, with the earlier scalar distribution as its expectation. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMJointRandomDistribution
open InfiniteGaussian IBMTimeAveragedObservable IBMJointCompletedTestGraph
open IBMJointBanachTestSpace

def distribution (T : ℝ≥0) (hT : 0 < T) : Tests →L[ℝ] Lp ℝ 1 gaussianProduct :=
  jointMap.ker.liftQL (IBMJointRandomGraphIdentity.limitOperator T)
    (IBMJointRandomGraphIdentity.joint_kernel_le_limit_kernel T hT)

theorem distribution_projection (T : ℝ≥0) (hT : 0 < T) (p : Graph) :
    distribution T hT (projection p) =
      IBMSpatialSignedRandomTests.limitOperator T (symbolMap p) := rfl

def nativeOperator (T : ℝ≥0) (N : ℕ) : Tests →L[ℝ] Lp ℝ 1 gaussianProduct :=
  (IBMJointRandomGraphIdentity.nativeOperator T N).comp realize

theorem native_tendsto (T : ℝ≥0) (hT : 0 < T) (x : Tests) :
    Tendsto (fun N => nativeOperator T N x) atTop (𝓝 (distribution T hT x)) := by
  refine Submodule.Quotient.induction_on jointMap.ker x ?_
  intro p
  exact IBMJointRandomGraphIdentity.native_tendsto T hT p

theorem expectation_eq (T : ℝ≥0) (hT : 0 < T) (x : Tests) :
    L1.integralCLM (distribution T hT x) = IBMJointBanachTestSpace.distribution T hT x := by
  refine Submodule.Quotient.induction_on jointMap.ker x ?_
  intro p
  rfl

theorem distribution_unique (T : ℝ≥0) (hT : 0 < T) (f : Tests → Lp ℝ 1 gaussianProduct)
    (hf : ∀ x, Tendsto (fun N => nativeOperator T N x) atTop (𝓝 (f x))) :
    f = distribution T hT := by
  funext x
  exact tendsto_nhds_unique (hf x) (native_tendsto T hT x)

theorem native_bound (T : ℝ≥0) (N : ℕ) (x : Tests) :
    ‖nativeOperator T N x‖ ≤ 6*(T:ℝ)*‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hd : 0 < ε/(6*(T:ℝ)+1) := by positivity
  obtain ⟨p,hp,hpn⟩ := Submodule.Quotient.norm_mk_lt x hd
  have he : nativeOperator T N x =
      IBMSpatialSignedRandomTests.finiteOperator T N (symbolMap p) := by
    rw [← hp]
    exact IBMJointRandomGraphIdentity.finite_identity T N p
  rw [he]
  have hb := (IBMJointTestNormBounds.signed_random_bound T N (symbolMap p)).trans
    (mul_le_mul_of_nonneg_left (IBMJointTestNormBounds.graph_symbol_bound p) (by positivity))
  have hs : 6*(T:ℝ)*(ε/(6*(T:ℝ)+1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 6*(T:ℝ)+1 by positivity)).mpr
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hpn.le (show 0 ≤ 6*(T:ℝ) by positivity)
  nlinarith

theorem distribution_bound (T : ℝ≥0) (hT : 0 < T) (x : Tests) :
    ‖distribution T hT x‖ ≤ 6*(T:ℝ)*‖x‖ :=
  le_of_tendsto (native_tendsto T hT x).norm (Eventually.of_forall fun N => native_bound T N x)

theorem test_actual (T : ℝ≥0) (hT : 0 < T) (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) :
    distribution T hT (test g h a) =ᵐ[gaussianProduct] fun Y =>
      IBMSpatialPathReconstruction.signedPath T Y
        (IBMSpatialCompletedTestLimit.realize (IBMJointMixedSpatialTransport.symbol g h a Y)) :=
  IBMSpatialSignedRandomTests.limit_actual T (IBMJointMixedSpatialTransport.symbol g h a)

end OperatorDerivativeRewrite.Foundation.IBMJointRandomDistribution
