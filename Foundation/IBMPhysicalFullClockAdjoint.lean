import Foundation.IBMPhysicalSceneryTestClockGraph

/-! Physical IBM slope pairings against EVERY original Gaussian clock
divergence integrand, with actual stochastic and intrinsic-domain agreement. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalFullClockAdjoint
open InfiniteGaussian IBMPhysicalWeakWiener IBMSchwartzWeakWienerClosure
open IBMFirstSourceClockGraph IBMPhysicalPointSlope IBMPhysicalSceneryTestClockGraph
open IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def component (h : CoefficientSpace) : GaussianVectorL2 →L[ℝ] GaussianL2 :=
  (innerSL ℝ h).compLpL 2 gaussianProduct

theorem gradient_pairing (t : ℝ≥0) (L : Tests) (v : GaussianVectorL2) :
    inner ℝ (gradient t L) v =
      inner ℝ (evaluate L (slopeLimit t)) (component (IBMClockAverageCandidate.direction t) v) := by
  rw [L2_inner_eq_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [scalarTensor_coeFn (IBMClockAverageCandidate.direction t)
    (evaluate L (slopeLimit t)),
    (innerSL ℝ (IBMClockAverageCandidate.direction t)).coeFn_compLpL v] with Y hg hc
  change gradient t L Y = _ at hg
  change component (IBMClockAverageCandidate.direction t) v Y = _ at hc
  rw [hg, hc, real_inner_smul_left, innerSL_apply_apply, Real.inner_apply]

theorem clock_ibp (t : ℝ≥0) (ht : 0 < t) (L : Tests) (v : hilbertDivergence.domain) :
    inner ℝ (point t L) (hilbertDivergence v) =
      inner ℝ (evaluate L (slopeLimit t))
        (component (IBMClockAverageCandidate.direction t) (v : GaussianVectorL2)) := by
  have hi := closedCylindricalDerivative.adjoint_isFormalAdjoint
    closedCylindricalDerivative_dense_domain v ⟨point t L, point_mem t ht L⟩
  change inner ℝ (hilbertDivergence v) (point t L) =
    inner ℝ (v : GaussianVectorL2)
      (closedCylindricalDerivative ⟨point t L, point_mem t ht L⟩) at hi
  rw [derivative_value t ht L] at hi
  calc
    _ = inner ℝ (hilbertDivergence v) (point t L) := real_inner_comm _ _
    _ = inner ℝ (v : GaussianVectorL2) (gradient t L) := hi
    _ = inner ℝ (gradient t L) (v : GaussianVectorL2) := real_inner_comm _ _
    _ = _ := gradient_pairing t L _

/-- The tested ACTUAL IBM and the signed physical Dirac slope obey ordinary
Gaussian integration by parts on the ENTIRE original clock divergence domain. -/
theorem actual_clock_ibp (t : ℝ≥0) (ht : 0 < t) (L : Tests)
    (v : hilbertDivergence.domain) :
    (∫ Y, (∫ X, IBMConstructedSources.ibmValue t (X,Y) * testNoise L X ∂gaussianProduct) *
      hilbertDivergence v Y ∂gaussianProduct) =
      ∫ Y, (clockSign t Y * L (IBMPhysicalDirac.dirac |IBMConstructedSources.clockPath Y t|)) *
        component (IBMClockAverageCandidate.direction t) (v : GaussianVectorL2) Y
          ∂gaussianProduct := by
  have he : inner ℝ (point t L) (hilbertDivergence v) =
      ∫ Y, (∫ X, IBMConstructedSources.ibmValue t (X,Y) * testNoise L X ∂gaussianProduct) *
        hilbertDivergence v Y ∂gaussianProduct := by
    rw [L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [point_actual_ae t L] with Y hY
    rw [hY, Real.inner_apply]
  exact he.symm.trans ((clock_ibp t ht L v).trans (slope_pairing_integral t L _))

theorem actual_clock_product_integrable (t : ℝ≥0) (L : Tests)
    (v : hilbertDivergence.domain) :
    Integrable (fun Y =>
      (∫ X, IBMConstructedSources.ibmValue t (X,Y) * testNoise L X ∂gaussianProduct) *
        hilbertDivergence v Y) gaussianProduct := by
  apply ((Lp.memLp (point t L)).integrable_mul (Lp.memLp (hilbertDivergence v))).congr
  filter_upwards [point_actual_ae t L] with Y hY
  rw [Pi.mul_apply, hY]

theorem slope_product_integrable (t : ℝ≥0) (L : Tests) (v : GaussianVectorL2) :
    Integrable (fun Y =>
      (clockSign t Y * L (IBMPhysicalDirac.dirac |IBMConstructedSources.clockPath Y t|)) *
        component (IBMClockAverageCandidate.direction t) v Y) gaussianProduct := by
  apply ((Lp.memLp (evaluate L (slopeLimit t))).integrable_mul
    (Lp.memLp (component (IBMClockAverageCandidate.direction t) v))).congr
  filter_upwards [(ContinuousLinearMap.apply ℝ ℝ L).coeFn_compLpL (slopeLimit t),
    slopeLimit_ae t] with Y he hs
  change evaluate L (slopeLimit t) Y = slopeLimit t Y L at he
  rw [Pi.mul_apply, he, hs L]

def field (L : Tests) (v : hilbertDivergence.domain) : VectorSpace :=
  BochnerClosedOperator.tensor gaussianProduct (testNoise L) (v : GaussianVectorL2)

def output (L : Tests) (v : hilbertDivergence.domain) : ScalarSpace :=
  BochnerClosedOperator.tensor gaussianProduct (testNoise L) (hilbertDivergence v)

theorem adjoint_graph (L : Tests) (v : hilbertDivergence.domain) :
    (field L v, output L v) ∈ IBMClockGraphDualLimit.Clock.adjoint.graph :=
  LinearPMap.le_graph_of_le
    (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct closedCylindricalDerivative
      closedCylindricalDerivative_dense_domain)
    (BochnerClosedOperator.tensor_graph gaussianProduct hilbertDivergence (testNoise L)
      _ _ (hilbertDivergence.mem_graph v))

theorem adjoint_mem (L : Tests) (v : hilbertDivergence.domain) :
    field L v ∈ IBMClockGraphDualLimit.Clock.adjoint.domain :=
  LinearPMap.mem_domain_of_mem_graph (adjoint_graph L v)

theorem adjoint_value (L : Tests) (v : hilbertDivergence.domain) :
    IBMClockGraphDualLimit.Clock.adjoint ⟨field L v,adjoint_mem L v⟩ = output L v :=
  ((IBMClockGraphDualLimit.Clock.adjoint.image_iff (adjoint_mem L v)).mpr (adjoint_graph L v)).symm

theorem projection_inner (u : ScalarSpace) (L : Tests) (ζ : GaussianL2) :
    inner ℝ (projection L u) ζ =
      inner ℝ u (BochnerClosedOperator.tensor gaussianProduct (testNoise L) ζ) := by
  change inner ℝ (GaussianClockBochnerContraction.contract (testNoise L) u) ζ = _
  rw [real_inner_comm, GaussianClockBochnerContraction.contract_inner, real_inner_comm]

theorem clock_inner_bridge (t : ℝ≥0) (ht : 0 < t) (L : Tests)
    (v : hilbertDivergence.domain) :
    inner ℝ (IBMClockGraphDualLimit.point t)
      (IBMClockGraphDualLimit.Clock.adjoint ⟨field L v,adjoint_mem L v⟩) =
      inner ℝ (evaluate L (slopeLimit t))
        (component (IBMClockAverageCandidate.direction t) (v : GaussianVectorL2)) := by
  rw [adjoint_value]
  exact (projection_inner (IBMClockGraphDualLimit.point t) L (hilbertDivergence v)).symm.trans
    (clock_ibp t ht L v)

attribute [local irreducible] jointDerivative intrinsicCurve field slopeLimit
  sourceDerivative clockDerivative pairField

theorem intrinsic_adjoint_bridge (t : ℝ≥0) (ht : 0 < t) (L : Tests)
    (v : hilbertDivergence.domain) :
    ∃ hp : pairField 0 (field L v) ∈ jointDivergence.domain,
      inner ℝ (intrinsicCurve t) (jointDivergence ⟨pairField 0 (field L v),hp⟩) =
        inner ℝ (evaluate L (slopeLimit t))
          (component (IBMClockAverageCandidate.direction t) (v : GaussianVectorL2)) := by
  have hc : field L v ∈ clockDerivative.adjoint.domain := by
    rw [clock_adjoint_domain]
    exact adjoint_mem L v
  have hex := IBMPhysicalClockAdjointBridge.ambient_clock_compatibility
    (intrinsicCurve t) ⟨field L v,hc⟩
  obtain ⟨hp,hv⟩ := hex
  refine ⟨hp,hv.trans ?_⟩
  rw [clock_adjoint_apply _ hc (adjoint_mem L v),
    IBMPhysicalClockAdjointBridge.clock_pairing_transport]
  exact clock_inner_bridge t ht L v

end OperatorDerivativeRewrite.Foundation.IBMPhysicalFullClockAdjoint
