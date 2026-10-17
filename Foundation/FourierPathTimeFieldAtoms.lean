import Foundation.BochnerDyadicTimeFields
import Foundation.FourierPathControlGradientSeries

/-! Concrete Bochner L-one time-gradient fields for the actual Fourier modes. -/
noncomputable section
open MeasureTheory
open scoped lp NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathTimeFieldAtoms
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatFourierBanach
open HigherHeatFourierPathSemigroup HigherHeatFourierPathDerivative
open FourierPathBoundedControls FourierPathDirectionalCharacters FourierPathControlSymbols
open BochnerTimeControlPairing BochnerDyadicTimeFields

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def frequencyStep (i : ℕ) (j : Fin (gridSize (spectrumLevels levels i))) : ℝ :=
  2*Real.pi*(∑ k ∈ Finset.univ.filter (fun k => j ≤ k), spectrumFrequency levels ξ i k)

def vectorStep (m : ℕ) (T : ℝ≥0) (i : ℕ) (j : Fin (gridSize (spectrumLevels levels i))) : Coeff :=
  lp.single 1 i (Complex.I*Complex.ofReal (-frequencyStep levels ξ i j)*multiplier levels ξ m T i)

def field (m : ℕ) (T : ℝ≥0) (i : ℕ) : BochnerTimeControlPairing.Field Coeff :=
  stepField (gridSize (spectrumLevels levels i)) (vectorStep levels ξ m T i)

theorem vectorStep_norm (m : ℕ) (T : ℝ≥0) (i : ℕ) (j : Fin (gridSize (spectrumLevels levels i))) :
    ‖vectorStep levels ξ m T i j‖ = |frequencyStep levels ξ i j| * ‖multiplier levels ξ m T i‖ := by
  rw [vectorStep, lp.norm_single (by norm_num : (0:ℝ≥0∞)<1)]
  simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem field_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖field levels ξ m T i‖ ≤ 1+(T:ℝ)⁻¹ := by
  have ha := FourierPathLipschitzDamping.average_abs_bound m hm
    (gridSize (spectrumLevels levels i)) (gridSize_pos _) (frequencyStep levels ξ i)
  calc
    _ ≤ (∑ j, ‖vectorStep levels ξ m T i j‖)/(gridSize (spectrumLevels levels i):ℝ) :=
      stepField_bound _ (gridSize_pos _) _
    _ = ((∑ j, |frequencyStep levels ξ i j|)/(gridSize (spectrumLevels levels i):ℝ))*
        ‖multiplier levels ξ m T i‖ := by simp_rw [vectorStep_norm]; rw [← Finset.sum_mul]; ring
    _ ≤ (1+rate levels ξ m i)*‖multiplier levels ξ m T i‖ :=
      mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ = (1+rate levels ξ m i)*Real.exp (-(T:ℝ)*rate levels ξ m i) := by
      rw [multiplier_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ _ := FourierPathLinearDirection.damped_rate_bound _ _ (by exact_mod_cast hT)
      (rate_nonneg levels ξ m i)

theorem field_pairing (m : ℕ) (T : ℝ≥0) (i : ℕ) (u : Control) :
    pairing Coeff u (field levels ξ m T i) = FourierPathControlGradientSeries.atom levels ξ m T i u := by
  rw [field, pairing_stepField]
  let L := lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℂ) 1 i
  have he : (∑ j, (∫ t in left (gridSize (spectrumLevels levels i)) j..
      right (gridSize (spectrumLevels levels i)) j, u t) • vectorStep levels ξ m T i j) =
      L (∑ j, (∫ t in left (gridSize (spectrumLevels levels i)) j..
        right (gridSize (spectrumLevels levels i)) j, u t) •
          (Complex.I*Complex.ofReal (-frequencyStep levels ξ i j)*multiplier levels ξ m T i)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (map_smul L _ _).symm
  rw [he]
  change (lp.single 1 i _ : Coeff) = (lp.single 1 i (symbolMap levels ξ m T i u) : Coeff)
  congr 1
  rw [symbolMap_apply, FourierPathLipschitzDamping.frequency_increment]
  simp_rw [FourierPathBoundedControls.direction_increment]
  simp only [frequencyStep, left, right]
  simp only [eigenvalue, Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul]
  simp only [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

end OperatorDerivativeRewrite.Foundation.FourierPathTimeFieldAtoms
