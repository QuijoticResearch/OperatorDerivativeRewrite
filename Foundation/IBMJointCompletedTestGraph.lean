import Foundation.IBMJointMixedSpatialTransport
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! Complete the VERIFIED pairs of original joint tests and spatial symbols
in their product norm. Actual finite native identities extend by continuity;
neither symbol injectivity nor unrestricted Hilbert closure is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMJointCompletedTestGraph
open InfiniteGaussian IBMTimeAveragedObservable IBMSpatialRandomTestBounds
open IBMJointMixedSpatialTransport IBMRawGridSecondChaos

def generators : Set (JointL2 × RandomTests) :=
  {p | ∃ g h : SchwartzMap ℝ ℝ, ∃ a : GaussianL2, p = (jointTest g h a,symbol g h a)}

def testGraph : Submodule ℝ (JointL2 × RandomTests) :=
  (Submodule.span ℝ generators).topologicalClosure

abbrev Graph := testGraph

instance graph_complete : CompleteSpace Graph :=
  (Submodule.isClosed_topologicalClosure (Submodule.span ℝ generators)).completeSpace_coe

def jointMap : Graph →L[ℝ] JointL2 :=
  (ContinuousLinearMap.fst ℝ JointL2 RandomTests).comp testGraph.subtypeL

def symbolMap : Graph →L[ℝ] RandomTests :=
  (ContinuousLinearMap.snd ℝ JointL2 RandomTests).comp testGraph.subtypeL

def generator (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) : Graph :=
  ⟨(jointTest g h a,symbol g h a),
    (Submodule.span ℝ generators).le_topologicalClosure (Submodule.subset_span ⟨g,h,a,rfl⟩)⟩

theorem generator_joint (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) :
    jointMap (generator g h a) = jointTest g h a := rfl

theorem generator_symbol (g h : SchwartzMap ℝ ℝ) (a : GaussianL2) :
    symbolMap (generator g h a) = symbol g h a := rfl

private def finiteDefect (T : ℝ≥0) (N : ℕ) : (JointL2 × RandomTests) →L[ℝ] ℝ :=
  (innerSL ℝ (jointRealization (sourceGrid (T/(N+1)) (N+1)))).comp
    (ContinuousLinearMap.fst ℝ JointL2 RandomTests)-
  (L1.integralCLM (μ := gaussianProduct) (E := ℝ)).comp
    ((IBMSpatialSignedRandomTests.finiteOperator T N).comp
      (ContinuousLinearMap.snd ℝ JointL2 RandomTests))

theorem finite_identity (T : ℝ≥0) (N : ℕ) (p : Graph) :
    inner ℝ (jointRealization (sourceGrid (T/(N+1)) (N+1))) (jointMap p) =
      L1.integralCLM (IBMSpatialSignedRandomTests.finiteOperator T N (symbolMap p)) := by
  have hs : Submodule.span ℝ generators ≤ (finiteDefect T N).ker := by
    apply Submodule.span_le.mpr
    rintro q ⟨g,h,a,rfl⟩
    change inner ℝ (jointRealization (sourceGrid (T/(N+1)) (N+1))) (jointTest g h a)-
      L1.integralCLM (IBMSpatialSignedRandomTests.finiteOperator T N (symbol g h a)) = 0
    rw [original_joint_pairing]
    simp only [← L1.integral_eq,L1.integral_eq_integral,sub_self]
  have hc : testGraph ≤ (finiteDefect T N).ker :=
    (Submodule.span ℝ generators).topologicalClosure_minimal hs (finiteDefect T N).isClosed_ker
  have hp := hc p.property
  change inner ℝ (jointRealization (sourceGrid (T/(N+1)) (N+1))) (jointMap p)-
    L1.integralCLM (IBMSpatialSignedRandomTests.finiteOperator T N (symbolMap p)) = 0 at hp
  exact sub_eq_zero.mp hp

def finiteFunctional (T : ℝ≥0) (N : ℕ) : Graph →L[ℝ] ℝ :=
  (innerSL ℝ (jointRealization (sourceGrid (T/(N+1)) (N+1)))).comp jointMap

def limitFunctional (T : ℝ≥0) : Graph →L[ℝ] ℝ :=
  (L1.integralCLM (μ := gaussianProduct) (E := ℝ)).comp
    ((IBMSpatialSignedRandomTests.limitOperator T).comp symbolMap)

theorem functional_tendsto (T : ℝ≥0) (hT : 0 < T) (p : Graph) :
    Tendsto (fun N => finiteFunctional T N p) atTop (𝓝 (limitFunctional T p)) := by
  have ht := (L1.integralCLM (μ := gaussianProduct) (E := ℝ)).continuous.tendsto
    (IBMSpatialSignedRandomTests.limitOperator T (symbolMap p))
  have hh := ht.comp (IBMSpatialSignedRandomTests.signed_random_tendsto T hT (symbolMap p))
  exact hh.congr' (Eventually.of_forall fun N => (finite_identity T N p).symm)

theorem joint_kernel_le_limit_kernel (T : ℝ≥0) (hT : 0 < T) :
    jointMap.ker ≤ (limitFunctional T).ker := by
  intro p hp
  change jointMap p = 0 at hp
  change limitFunctional T p = 0
  have he (N : ℕ) : finiteFunctional T N p = 0 := by
    change inner ℝ (jointRealization (sourceGrid (T/(N+1)) (N+1))) (jointMap p) = 0
    rw [hp,inner_zero_right]
  have hz : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 (limitFunctional T p)) :=
    (functional_tendsto T hT p).congr' (Eventually.of_forall he)
  exact tendsto_nhds_unique hz tendsto_const_nhds

theorem presentation_consistent (T : ℝ≥0) (hT : 0 < T) (p q : Graph)
    (hpq : jointMap p = jointMap q) : limitFunctional T p = limitFunctional T q := by
  have hk : p-q ∈ jointMap.ker := by
    change jointMap (p-q) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hpq
  have hl := joint_kernel_le_limit_kernel T hT hk
  change limitFunctional T (p-q) = 0 at hl
  rw [map_sub] at hl
  exact sub_eq_zero.mp hl

end OperatorDerivativeRewrite.Foundation.IBMJointCompletedTestGraph
