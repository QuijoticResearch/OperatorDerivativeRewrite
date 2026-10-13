import Foundation.IBMDualDistribution
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The canonical weighted-L² pairing between the actual Bessel-potential
H⁻¹ and H¹ spaces on the real line. -/
noncomputable section
open MeasureTheory
open scoped BesselPotentialSpace

namespace OperatorDerivativeRewrite.Foundation.IBMBesselDuality

abbrev HminusOne := H^{(-1 : ℝ)}(ℝ)
abbrev HplusOne := H^{(1 : ℝ)}(ℝ)

/-- Weighted-L² Hilbert pairing. The H⁻¹ argument is conjugate-linear
and the H¹ argument is linear. -/
def pairing (u : HminusOne) (v : HplusOne) : ℂ :=
  inner ℂ u.toLp v.toLp

/-- The pairing obeys the sharp Cauchy–Schwarz continuity bound. -/
theorem pairing_norm_le (u : HminusOne) (v : HplusOne) :
    ‖pairing u v‖ ≤ ‖u‖ * ‖v‖ := by
  simpa only [pairing, BesselPotentialSpace.norm_toLp_eq] using
    norm_inner_le_norm u.toLp v.toLp

/-- Each H⁻¹ element acts continuously and linearly on H¹ through the
weighted-L² pairing. -/
def pairingCLM (u : HminusOne) : HplusOne →L[ℂ] ℂ :=
  (innerSL ℂ u.toLp).comp
    ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (1 : ℝ) 2).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem pairingCLM_apply (u : HminusOne) (v : HplusOne) :
    pairingCLM u v = pairing u v := rfl

/-- The functional norm is bounded by the H⁻¹ norm. -/
theorem pairingCLM_norm_le (u : HminusOne) : ‖pairingCLM u‖ ≤ ‖u‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact norm_nonneg _
  intro v
  simpa only [pairingCLM_apply] using pairing_norm_le u v


/-- The pairing separates H⁻¹ elements: vanishing against every H¹ vector
forces the distribution class to be zero. -/
theorem pairing_left_separating (u : HminusOne)
    (h : ∀ v : HplusOne, pairing u v = 0) : u = 0 := by
  let v : HplusOne :=
    (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (1 : ℝ) 2).symm u.toLp
  have hself : inner ℂ u.toLp u.toLp = 0 := by
    have hv := h v
    change inner ℂ u.toLp ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (1 : ℝ) 2) v) = 0 at hv
    simpa only [v, LinearIsometryEquiv.apply_symm_apply] using hv
  have hz : u.toLp = 0 := inner_self_eq_zero.mp hself
  exact (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).injective hz
end OperatorDerivativeRewrite.Foundation.IBMBesselDuality

