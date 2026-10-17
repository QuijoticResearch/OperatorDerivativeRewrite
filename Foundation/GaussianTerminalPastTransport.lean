import Foundation.GaussianUnitaryConditionalFormula

/-! After the likelihood is measurable, the transported and ordinary past projections agree. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianTerminalPastTransport
open InfiniteGaussian GaussianTimeProcess GaussianLinearTiltLaw GaussianTiltHalfDensity
open GaussianTiltL2Domain GaussianTiltFiniteHorizon GaussianConditionalIto
open GaussianHalfDensityUnitary GaussianTransportedPastProjection GaussianUnitaryConditionalFormula
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Qlinear := Qlinear_probability

theorem rootDensity_past_after {T : ℝ≥0} (hT : 2 ≤ T) :
    Measurable[naturalFiltration T] rootDensity :=
  rootDensity_past_two.mono (naturalFiltration.mono hT) le_rfl

theorem unitary_mem_past_after {T : ℝ≥0} (hT : 2 ≤ T) {u : QSpace} (hu : u ∈ qPast T) :
    unitary u ∈ pastL2 T := by
  have hp : AEStronglyMeasurable[naturalFiltration T] u gaussianProduct :=
    AEStronglyMeasurable.mono_ac P_ac_Qlinear hu
  have hr : AEStronglyMeasurable[naturalFiltration T] rootDensity gaussianProduct :=
    (rootDensity_past_after hT).stronglyMeasurable.aestronglyMeasurable
  exact (hr.mul hp).congr (unitary_coeFn u).symm

theorem unitary_symm_mem_past_after {T : ℝ≥0} (hT : 2 ≤ T)
    {v : InfiniteGaussian.GaussianL2} (hv : v ∈ pastL2 T) : unitary.symm v ∈ qPast T := by
  have hq : AEStronglyMeasurable[naturalFiltration T] v Qlinear :=
    AEStronglyMeasurable.mono_ac Qlinear_ac_P hv
  have hr : AEStronglyMeasurable[naturalFiltration T] rootDensity Qlinear :=
    (rootDensity_past_after hT).stronglyMeasurable.aestronglyMeasurable
  exact (hq.div₀ hr).congr (unitary_symm_coeFn v).symm

theorem transportedPast_after {T : ℝ≥0} (hT : 2 ≤ T) : transportedPast T = pastL2 T := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact unitary_mem_past_after hT hu
  · intro hv
    exact ⟨unitary.symm v, unitary_symm_mem_past_after hT hv, unitary.apply_symm_apply v⟩

theorem projections_after {T : ℝ≥0} (hT : 2 ≤ T) :
    transportedProjection T = pastProjection T := by
  unfold transportedProjection pastProjection
  simp only [transportedPast_after hT]

theorem ordinary_intertwiner_after {T : ℝ≥0} (hT : 2 ≤ T) (u : QSpace) :
    pastProjection T (unitary u) = unitary ((qPast T).starProjection u) := by
  rw [← projections_after hT]
  exact conditional_intertwiner T u

end OperatorDerivativeRewrite.Foundation.GaussianTerminalPastTransport
