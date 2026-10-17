import Foundation.FourierPathDualTimeAtoms

/-! Native Bochner L^(2m) synthesis of actual time-gradient fields. -/
noncomputable section
open MeasureTheory
open scoped lp NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualTimeSeries
open L1SeriesSynthesis HigherHeatDyadicLaws FourierPathDualControls FourierPathDualTimeAtoms

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem term_bound (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖term (field levels ξ m T) i‖ ≤ 1+(T : ℝ)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  change ‖z • field levels ξ m T i‖ ≤ _
  rw [norm_smul]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (field_bound levels ξ m T hT i) (norm_nonneg z)

def series (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) :
    Coeff →L[ℂ] BochnerDualControlPairing.Field Coeff m :=
  (lp.tsumCLM ℂ ℕ (BochnerDualControlPairing.Field Coeff m)).comp
    (lp.mapCLM 1 (term (field levels ξ m T)) (by positivity) (term_bound levels ξ m T hT))

theorem series_bound (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) :
    ‖series levels ξ m T hT‖ ≤ 1+(T : ℝ)⁻¹ := by
  calc
    _ ≤ ‖lp.tsumCLM ℂ ℕ (BochnerDualControlPairing.Field Coeff m)‖ *
        ‖lp.mapCLM 1 (term (field levels ξ m T)) (by positivity) (term_bound levels ξ m T hT)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*(1+(T : ℝ)⁻¹) := mul_le_mul lp.norm_tsumCLM_le (lp.norm_mapCLM_le 1 _ _ _)
      (norm_nonneg _) (by positivity)
    _ = _ := one_mul _

theorem fields_summable (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) (a : Coeff) :
    Summable (fun i => a i • field levels ξ m T i) := by
  let b := lp.mapCLM 1 (term (field levels ξ m T)) (by positivity) (term_bound levels ξ m T hT) a
  apply Summable.of_norm
  simpa [b, term] using b.property.summable (by norm_num)

theorem series_pairing (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (a : Coeff) (u : Control m) :
    BochnerDualControlPairing.pairing Coeff m u (series levels ξ m T hT a) =
      FourierPathDualGradientSeries.family levels ξ m T hT a u := by
  have hp := (BochnerDualControlPairing.pairing Coeff m u).map_tsum
    (fields_summable levels ξ m T hT a)
  have he := (ContinuousLinearMap.apply ℝ Coeff u).map_tsum
    (FourierPathDualGradientSeries.atoms_summable levels ξ m T hT a)
  change BochnerDualControlPairing.pairing Coeff m u (∑' i, a i • field levels ξ m T i) = _
  rw [hp, FourierPathDualGradientSeries.family_tsum]
  simp_rw [pairing_complex_smul, field_pairing]
  exact he.symm

end OperatorDerivativeRewrite.Foundation.FourierPathDualTimeSeries
