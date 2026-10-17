import Foundation.GaussianTransportedPastProjection

/-! The correct conditional formula for the unitarily transported Q-past projection. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianUnitaryConditionalFormula
open InfiniteGaussian GaussianTimeProcess GaussianLinearTiltLaw GaussianTiltHalfDensity
open GaussianHalfDensityUnitary GaussianTransportedPastProjection
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Qlinear := Qlinear_probability

theorem qProjection_ae (T : ℝ≥0) (u : QSpace) :
    (qPast T).starProjection u =ᵐ[Qlinear] Qlinear[u | naturalFiltration T] := by
  change (condExpL2 ℝ ℝ (naturalFiltration.le T) u : QSpace) =ᵐ[Qlinear] _
  simpa only [Lp.toLp_coeFn] using
    (Lp.memLp u).condExpL2_ae_eq_condExp (𝕜 := ℝ) (naturalFiltration.le T)

theorem transportedProjection_condExp (T : ℝ≥0) (v : InfiniteGaussian.GaussianL2) :
    transportedProjection T v =ᵐ[gaussianProduct]
      fun ω => GaussianTiltL2Domain.rootDensity ω *
        Qlinear[inverse v | naturalFiltration T] ω := by
  rw [transportedProjection_apply]
  have hq := (qProjection_ae T (unitary.symm v)).trans
    (condExp_congr_ae (m := naturalFiltration T) (unitary_symm_coeFn v))
  filter_upwards [unitary_coeFn ((qPast T).starProjection (unitary.symm v)),
    P_ac_Qlinear.ae_le hq] with ω hu hω
  rw [hu]
  change GaussianTiltL2Domain.rootDensity ω * (qPast T).starProjection (unitary.symm v) ω = _
  rw [hω]

theorem conditional_intertwiner (T : ℝ≥0) (u : QSpace) :
    transportedProjection T (unitary u) = unitary ((qPast T).starProjection u) := by
  rw [transportedProjection_apply, unitary.symm_apply_apply]

theorem transported_projection_on_image (T : ℝ≥0) (u : QSpace) :
    transportedProjection T (unitary u) =ᵐ[gaussianProduct]
      fun ω => GaussianTiltL2Domain.rootDensity ω * Qlinear[u | naturalFiltration T] ω := by
  rw [conditional_intertwiner]
  filter_upwards [unitary_coeFn ((qPast T).starProjection u),
    P_ac_Qlinear.ae_le (qProjection_ae T u)] with ω hu hq
  rw [hu]
  change GaussianTiltL2Domain.rootDensity ω * (qPast T).starProjection u ω = _
  rw [hq]

end OperatorDerivativeRewrite.Foundation.GaussianUnitaryConditionalFormula
