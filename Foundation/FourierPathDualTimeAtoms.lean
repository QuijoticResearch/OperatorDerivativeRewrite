import Foundation.BochnerDualControlPairing
import Foundation.FourierPathDualGradientSeries

/-! Concrete Bochner L^(2m) time-gradient atoms built from the actual tail-frequency controls. -/
noncomputable section
open MeasureTheory
open scoped lp NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualTimeAtoms
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatFourierBanach
open HigherHeatLpControls FourierPathDualGrid FourierPathDualDamping
open HigherHeatFourierPathDerivative HigherHeatFourierPathSemigroup FourierPathDirectionalCharacters

def singleMap (i : ℕ) : ℝ →L[ℝ] Coeff :=
  ((lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 1 i).restrictScalars ℝ).comp Complex.ofRealCLM

theorem singleMap_bound (i : ℕ) : ‖singleMap i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(lp.single 1 i (x : ℂ) : Coeff)‖ ≤ 1*‖x‖
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞)<1), Complex.norm_real, one_mul]

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def field (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (i : ℕ) : BochnerDualControlPairing.Field Coeff m :=
  (-Complex.I * multiplier levels ξ m T i) •
    (singleMap i).compLpL (power m) volume
      (step m (gridSize (spectrumLevels levels i)) (tail levels ξ i))

theorem field_bound (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖field levels ξ m T i‖ ≤ 1+(T : ℝ)⁻¹ := by
  have hs : ‖(singleMap i).compLpL (power m) (volume : Measure ℝ)‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le (p := power m) (μ := (volume : Measure ℝ)) (singleMap i)).trans
      (singleMap_bound i)
  have hc : ‖(singleMap i).compLpL (power m) volume
      (step m (gridSize (spectrumLevels levels i)) (tail levels ξ i))‖ ≤
      ‖step m (gridSize (spectrumLevels levels i)) (tail levels ξ i)‖ := by
    simpa only [one_mul] using ((singleMap i).compLpL (power m) volume).le_of_opNorm_le hs
      (step m (gridSize (spectrumLevels levels i)) (tail levels ξ i))
  rw [field, norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul]
  calc
    _ ≤ ‖multiplier levels ξ m T i‖ *
        ‖step m (gridSize (spectrumLevels levels i)) (tail levels ξ i)‖ :=
      mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ ≤ ‖multiplier levels ξ m T i‖ * (1+rate levels ξ m i) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [tail_clock] using norm_le_clock m
        (step m (gridSize (spectrumLevels levels i)) (tail levels ξ i))
    _ = (1+rate levels ξ m i)*Real.exp (-(T : ℝ)*rate levels ξ m i) := by
      rw [multiplier_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      ring
    _ ≤ _ := FourierPathLinearDirection.damped_rate_bound _ _ (by exact_mod_cast hT)
      (rate_nonneg levels ξ m i)

theorem pairing_complex_smul (m : ℕ) [Fact (0 < m)] (u : FourierPathDualControls.Control m)
    (c : ℂ) (f : BochnerDualControlPairing.Field Coeff m) :
    BochnerDualControlPairing.pairing Coeff m u (c • f) =
      c • BochnerDualControlPairing.pairing Coeff m u f := by
  rw [BochnerDualControlPairing.pairing_integral, BochnerDualControlPairing.pairing_integral,
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with s hs
  rw [hs]
  exact smul_comm (u s) c (f s)

theorem field_pairing (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (i : ℕ)
    (u : FourierPathDualControls.Control m) :
    BochnerDualControlPairing.pairing Coeff m u (field levels ξ m T i) =
      FourierPathDualGradientSeries.atom levels ξ m T i u := by
  rw [field, pairing_complex_smul, BochnerDualControlPairing.pairing_compLp]
  let b := step m (gridSize (spectrumLevels levels i)) (tail levels ξ i)
  have hp : BochnerDualControlPairing.pairing ℝ m u b = FourierPathDualControls.pairing m u b := by
    rw [BochnerDualControlPairing.pairing_integral, FourierPathDualControls.pairing_integral]
    rfl
  change (-Complex.I * multiplier levels ξ m T i) •
    (lp.single 1 i (BochnerDualControlPairing.pairing ℝ m u b : ℂ) : Coeff) =
      lp.single 1 i (FourierPathDualGradientSeries.symbolMap levels ξ m T i u)
  rw [hp, ← lp.single_smul]
  congr 1
  rw [FourierPathDualGradientSeries.symbolMap_apply, ← frequencyMap_apply]
  change _ = eigenvalue (-FourierPathDualControls.pairing m u b) * multiplier levels ξ m T i
  simp only [smul_eq_mul, eigenvalue, Complex.ofReal_neg]
  ring

end OperatorDerivativeRewrite.Foundation.FourierPathDualTimeAtoms
