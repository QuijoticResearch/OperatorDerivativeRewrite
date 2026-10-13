import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

/-! Deterministic negative-Sobolev infrastructure for the IBM first-chaos kernel. -/
noncomputable section
open MeasureTheory TemperedDistribution
open scoped LineDeriv BesselPotentialSpace SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.IBMNegativeSobolev

/-- Every complex-valued Lebesgue-L² function has a distributional spatial
derivative in the concrete Bessel-potential space H⁻¹(ℝ). The Mathlib Fourier
normalization is inherited unchanged. -/
theorem l2_derivative_memHminusOne (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (LineDeriv.lineDerivOp (1 : ℝ) (u : 𝓢'(ℝ, ℂ))).MemSobolev (-1) 2 := by
  have hu : (u : 𝓢'(ℝ, ℂ)).MemSobolev 0 2 := by
    exact memSobolev_zero_iff.mpr ⟨u, rfl⟩
  simpa using hu.lineDerivOp (m := (1 : ℝ))

/-- Bundle the distributional derivative as a genuine element of H⁻¹(ℝ). -/
def l2Derivative (u : Lp ℂ 2 (volume : Measure ℝ)) : H^{(-1 : ℝ)}(ℝ) :=
  (l2_derivative_memHminusOne u).toBesselPotentialSpace

@[simp] theorem l2Derivative_toDistr (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (l2Derivative u).toDistr =
      LineDeriv.lineDerivOp (1 : ℝ) (u : 𝓢'(ℝ, ℂ)) := rfl

theorem l2Derivative_add (u v : Lp ℂ 2 (volume : Measure ℝ)) :
    l2Derivative (u + v) = l2Derivative u + l2Derivative v := by
  apply BesselPotentialSpace.ext
  simp only [l2Derivative_toDistr, BesselPotentialSpace.toDistr_add]
  simp [← Lp.toTemperedDistributionCLM_apply, LineDeriv.lineDerivOp_add]

theorem l2Derivative_smul (c : ℂ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    l2Derivative (c • u) = c • l2Derivative u := by
  apply BesselPotentialSpace.ext
  simp only [l2Derivative_toDistr, BesselPotentialSpace.toDistr_smul]
  simp [← Lp.toTemperedDistributionCLM_apply, LineDeriv.lineDerivOp_smul]

/-- Distributional differentiation, algebraically, from Lebesgue L² to H⁻¹. -/
def l2DerivativeLinear : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] H^{(-1 : ℝ)}(ℝ) where
  toFun := l2Derivative
  map_add' := l2Derivative_add
  map_smul' := l2Derivative_smul

end OperatorDerivativeRewrite.Foundation.IBMNegativeSobolev
