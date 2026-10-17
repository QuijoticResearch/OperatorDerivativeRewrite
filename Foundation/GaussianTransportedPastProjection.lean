import Foundation.GaussianHalfDensityUnitary
import Foundation.GaussianLikelihoodRootInnovation

/-! The transported Q-past projection differs quantitatively from the ordinary P-past projection. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianTransportedPastProjection
open InfiniteGaussian GaussianTimeProcess GaussianLinearTiltLaw GaussianTiltHalfDensity
open GaussianHalfDensityUnitary GaussianTiltBrownianDomain GaussianTiltFiniteHorizon
open GaussianConditionalIto GaussianLikelihoodRootInnovation
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Qlinear := Qlinear_probability

def qPast (T : ℝ≥0) : Submodule ℝ QSpace := lpMeas ℝ ℝ (naturalFiltration T) 2 Qlinear

theorem qPast_isClosed (T : ℝ≥0) : IsClosed (qPast T : Set QSpace) :=
  isClosed_aestronglyMeasurable (naturalFiltration.le T)

instance qPast_complete (T : ℝ≥0) : CompleteSpace (qPast T) :=
  (qPast_isClosed T).completeSpace_coe

def transportedPast (T : ℝ≥0) : Submodule ℝ InfiniteGaussian.GaussianL2 :=
  (qPast T).map unitary.toLinearEquiv.toLinearMap

theorem transportedPast_isClosed (T : ℝ≥0) :
    IsClosed (transportedPast T : Set InfiniteGaussian.GaussianL2) := by
  change IsClosed (unitary '' (qPast T : Set QSpace))
  exact unitary.toHomeomorph.isClosedMap _ (qPast_isClosed T)

instance transportedPast_complete (T : ℝ≥0) : CompleteSpace (transportedPast T) :=
  (transportedPast_isClosed T).completeSpace_coe

def transportedProjection (T : ℝ≥0) :
    InfiniteGaussian.GaussianL2 →L[ℝ] InfiniteGaussian.GaussianL2 :=
  (transportedPast T).starProjection

theorem transportedProjection_apply (T : ℝ≥0) (v : InfiniteGaussian.GaussianL2) :
    transportedProjection T v = unitary ((qPast T).starProjection (unitary.symm v)) :=
  Submodule.starProjection_map_apply unitary (qPast T) v

theorem transportedProjection_idempotent (T : ℝ≥0) (v : InfiniteGaussian.GaussianL2) :
    transportedProjection T (transportedProjection T v) = transportedProjection T v :=
  Submodule.starProjection_eq_self_iff.mpr ((transportedPast T).starProjection_apply_mem v)

def qOne : QSpace := (memLp_const (1 : ℝ)).toLp (fun _ => 1)

theorem qOne_coeFn : qOne =ᵐ[Qlinear] fun _ => 1 := MemLp.coeFn_toLp _

theorem qOne_past (T : ℝ≥0) : qOne ∈ qPast T :=
  stronglyMeasurable_const.aestronglyMeasurable.congr qOne_coeFn.symm

theorem unitary_qOne : unitary qOne = terminalValue := by
  apply Lp.ext
  filter_upwards [unitary_coeFn qOne, P_ac_Qlinear.ae_le qOne_coeFn,
    terminalValue_coeFn] with ω hu hq ht
  rw [hu, ht]
  change GaussianTiltL2Domain.rootDensity ω * qOne ω = GaussianTiltL2Domain.rootDensity ω
  rw [hq, mul_one]

theorem terminal_mem_transportedPast (T : ℝ≥0) : terminalValue ∈ transportedPast T :=
  ⟨qOne, qOne_past T, unitary_qOne⟩

theorem transportedProjection_terminal (T : ℝ≥0) :
    transportedProjection T terminalValue = terminalValue :=
  Submodule.starProjection_eq_self_iff.mpr (terminal_mem_transportedPast T)

theorem transportedPast_one_ne : transportedPast 1 ≠ pastL2 1 := by
  intro h
  have ht := terminal_mem_transportedPast 1
  rw [h] at ht
  exact terminalValue_not_past_one ht

theorem projections_one_ne : transportedProjection 1 ≠ pastProjection 1 := by
  intro h
  have ht := transportedProjection_terminal 1
  rw [h] at ht
  exact terminal_projection_one_ne ht

theorem projections_terminal_gap :
    ‖transportedProjection 1 terminalValue - pastProjection 1 terminalValue‖^2 =
      1 - Real.sqrt (2/3 : ℝ) := by
  rw [transportedProjection_terminal]
  exact conditional_error_exact

theorem projection_operator_gap :
    1 - Real.sqrt (2/3 : ℝ) ≤ ‖transportedProjection 1 - pastProjection 1‖^2 := by
  have ht : ‖terminalValue‖ = 1 := by
    nlinarith [terminal_norm_square, norm_nonneg terminalValue]
  have hb := (transportedProjection 1 - pastProjection 1).le_opNorm terminalValue
  rw [ht, mul_one] at hb
  have he : ‖(transportedProjection 1 - pastProjection 1) terminalValue‖^2 =
      1 - Real.sqrt (2/3 : ℝ) := projections_terminal_gap
  nlinarith [norm_nonneg (transportedProjection 1 - pastProjection 1),
    norm_nonneg ((transportedProjection 1 - pastProjection 1) terminalValue)]

end OperatorDerivativeRewrite.Foundation.GaussianTransportedPastProjection
