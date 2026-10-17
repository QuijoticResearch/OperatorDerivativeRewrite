import Foundation.FourierPathTimeFieldAtoms

/-! Genuine Bochner L-one synthesis of time-gradient fields. -/
noncomputable section
open MeasureTheory
open scoped lp NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathTimeFieldSeries
open L1SeriesSynthesis HigherHeatDyadicLaws FourierPathBoundedControls
open BochnerTimeControlPairing FourierPathTimeFieldAtoms

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem term_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖term (field levels ξ m T) i‖ ≤ 1+(T:ℝ)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  change ‖z • field levels ξ m T i‖ ≤ _
  rw [norm_smul]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (field_bound levels ξ m hm T hT i) (norm_nonneg z)

def series (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Coeff →L[ℂ] BochnerTimeControlPairing.Field Coeff :=
  (lp.tsumCLM ℂ ℕ (BochnerTimeControlPairing.Field Coeff)).comp
    (lp.mapCLM 1 (term (field levels ξ m T)) (by positivity) (term_bound levels ξ m hm T hT))

theorem series_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ‖series levels ξ m hm T hT‖ ≤ 1+(T:ℝ)⁻¹ := by
  calc
    _ ≤ ‖lp.tsumCLM ℂ ℕ (BochnerTimeControlPairing.Field Coeff)‖ *
        ‖lp.mapCLM 1 (term (field levels ξ m T)) (by positivity) (term_bound levels ξ m hm T hT)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*(1+(T:ℝ)⁻¹) := mul_le_mul lp.norm_tsumCLM_le (lp.norm_mapCLM_le 1 _ _ _)
      (norm_nonneg _) (by positivity)
    _ = _ := one_mul _

theorem fields_summable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (a : Coeff) :
    Summable (fun i => a i • field levels ξ m T i) := by
  let b := lp.mapCLM 1 (term (field levels ξ m T)) (by positivity)
    (term_bound levels ξ m hm T hT) a
  apply Summable.of_norm
  simpa [b, term] using b.property.summable (by norm_num)

theorem pairing_complex_smul (u : Control) (c : ℂ) (f : BochnerTimeControlPairing.Field Coeff) :
    pairing Coeff u (c • f) = c • pairing Coeff u f := by
  rw [pairing_integral, pairing_integral, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with s hs
  rw [hs]
  exact smul_comm (u s) c (f s)

theorem series_pairing (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (a : Coeff) (u : Control) :
    pairing Coeff u (series levels ξ m hm T hT a) =
      FourierPathControlGradientSeries.family levels ξ m hm T hT a u := by
  have hp := (pairing Coeff u).map_tsum (fields_summable levels ξ m hm T hT a)
  have he := (ContinuousLinearMap.apply ℝ Coeff u).map_tsum
    (FourierPathControlGradientSeries.atoms_summable levels ξ m hm T hT a)
  change pairing Coeff u (∑' i, a i • field levels ξ m T i) = _
  rw [hp]
  simp_rw [pairing_complex_smul, field_pairing]
  exact he.symm

end OperatorDerivativeRewrite.Foundation.FourierPathTimeFieldSeries
