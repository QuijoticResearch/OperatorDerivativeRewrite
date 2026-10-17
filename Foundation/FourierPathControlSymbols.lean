import Foundation.FourierPathBoundedControls
import Foundation.FourierPathLipschitzDamping

/-! Bounded linear time-control symbols for the actual higher-heat path calculus. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathControlSymbols
open FourierPathBoundedControls HigherHeatDyadicLaws HigherHeatContinuousCylinders
open HigherHeatFourierBanach FourierPathDirectionalCharacters HigherHeatFourierPathSemigroup

theorem primitive_add (u v : Control) (t : ℝ) :
    primitive (u+v) t = primitive u t + primitive v t := by
  unfold primitive
  rw [intervalIntegral.integral_congr_ae ((Lp.coeFn_add u v).mono fun s hs _ => hs)]
  exact intervalIntegral.integral_add (interval_integrable u 0 t) (interval_integrable v 0 t)

theorem primitive_smul (c : ℝ) (u : Control) (t : ℝ) :
    primitive (c • u) t = c • primitive u t := by
  unfold primitive
  rw [intervalIntegral.integral_congr_ae ((Lp.coeFn_smul c u).mono fun s hs _ => hs)]
  exact intervalIntegral.integral_smul c u

def atTime (t : ℝ) : Control →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => primitive u t
      map_add' := fun u v => primitive_add u v t
      map_smul' := fun c u => primitive_smul c u t }
    |t| (fun u => by
      change ‖∫ s in (0:ℝ)..t, u s‖ ≤ |t| * ‖u‖
      simpa only [sub_zero, mul_comm] using
        intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := 0) (b := t)
          ((ae_bound u).mono fun s hs _ => hs))

theorem atTime_apply (t : ℝ) (u : Control) : atTime t u = ∫ s in (0:ℝ)..t, u s := rfl

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def frequencyMap (i : ℕ) : Control →L[ℝ] ℝ :=
  (-2*Real.pi) • ∑ j : Fin (gridSize (spectrumLevels levels i)),
    (spectrumFrequency levels ξ i j) • atTime (sampleTime (spectrumLevels levels i) j)

theorem frequencyMap_apply (i : ℕ) (u : Control) :
    frequencyMap levels ξ i u = frequency levels ξ (direction u) i := by
  simp only [frequencyMap, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    smul_eq_mul, atTime, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  unfold frequency
  change (-2*Real.pi)*(∑ j, spectrumFrequency levels ξ i j *
    primitive u (sampleTime (spectrumLevels levels i) j)) = _
  change _ = 2*Real.pi*(-∑ j, spectrumFrequency levels ξ i j *
    primitive u (sampleTime (spectrumLevels levels i) j))
  ring

def symbolMap (m : ℕ) (T : ℝ≥0) (i : ℕ) : Control →L[ℝ] ℂ :=
  (frequencyMap levels ξ i).smulRight (Complex.I*multiplier levels ξ m T i)

theorem symbolMap_apply (m : ℕ) (T : ℝ≥0) (i : ℕ) (u : Control) :
    symbolMap levels ξ m T i u = eigenvalue (frequency levels ξ (direction u) i)*
      multiplier levels ξ m T i := by
  simp only [symbolMap, ContinuousLinearMap.smulRight_apply, frequencyMap_apply,
    Complex.real_smul, eigenvalue]
  ring

theorem symbolMap_norm (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    ‖symbolMap levels ξ m T i‖ ≤ 1+(T:ℝ)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [symbolMap_apply, norm_mul, eigenvalue_norm, HigherHeatFourierPathDerivative.multiplier_exp,
    Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (‖u‖*(1+HigherHeatFourierPathDerivative.rate levels ξ m i))*
        Real.exp (-(T:ℝ)*HigherHeatFourierPathDerivative.rate levels ξ m i) :=
      mul_le_mul_of_nonneg_right
        (FourierPathLipschitzDamping.frequency_bound levels ξ (direction u) ‖u‖₊
          (direction_lipschitz u) m hm i) (Real.exp_pos _).le
    _ = ‖u‖*((1+HigherHeatFourierPathDerivative.rate levels ξ m i)*
        Real.exp (-(T:ℝ)*HigherHeatFourierPathDerivative.rate levels ξ m i)) := by ring
    _ ≤ ‖u‖*(1+(T:ℝ)⁻¹) := mul_le_mul_of_nonneg_left
      (FourierPathLinearDirection.damped_rate_bound _ _ (by exact_mod_cast hT)
        (HigherHeatFourierPathDerivative.rate_nonneg levels ξ m i)) (norm_nonneg u)
    _ = _ := mul_comm _ _

end OperatorDerivativeRewrite.Foundation.FourierPathControlSymbols
