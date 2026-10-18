import Foundation.CyclicExponentialTaylor
import Foundation.HigherEvenRenewalEnergy
import Foundation.HigherHeatL2
import Mathlib.Analysis.SpecificLimits.Basic

/-! Holomorphic transforms of actual complex processes converge to the higher-heat multiplier.
This is not weak convergence of positive path laws. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherEvenHeatTransformLimit
open HigherEvenRenewalEnergy

theorem amplitude_pos (n : ℕ) : 0 < smallAmplitude n := by
  unfold smallAmplitude
  positivity

theorem amplitude_le_one (n : ℕ) : smallAmplitude n ≤ 1 := by
  unfold smallAmplitude
  apply (inv_le_one₀ (by positivity : (0 : ℝ) < n+1)).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem amplitude_tendsto : Tendsto smallAmplitude atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝 0)
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0))

theorem symbol_tendsto (m : ℕ) [NeZero m] (w : ℂ) :
    Tendsto (fun n => HigherEvenRenewalTransform.normalizedSymbol m (smallAmplitude n) w)
      atTop (𝓝 ((-1 : ℂ)^(m+1)*w^(2*m))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => CyclicExponentialTaylor.normalized_error_bound m (smallAmplitude n)
      (amplitude_pos n) (amplitude_le_one n) w)
  simpa using (tendsto_const_nhds.mul amplitude_tendsto :
    Tendsto (fun n => ((Nat.factorial (2*m) : ℝ)*‖w‖^(2*m+1)*Real.exp ‖w‖)*smallAmplitude n)
      atTop (𝓝 (((Nat.factorial (2*m) : ℝ)*‖w‖^(2*m+1)*Real.exp ‖w‖)*0)))

theorem actual_transform_tendsto (m : ℕ) [NeZero m] (t : ℝ≥0) (w : ℂ) :
    Tendsto (fun n => ∫ ω, Complex.exp (w*HigherEvenRenewalProcess.process m
      (smallAmplitude n) (acceleratedTime m n t) ω)
        ∂HigherEvenRenewalProcess.probability m) atTop
      (𝓝 (Complex.exp ((t : ℂ)*((-1 : ℂ)^(m+1)*w^(2*m))))) := by
  have he (n : ℕ) := HigherEvenRenewalTransform.normalized_transform m
    (smallAmplitude n) (amplitude_pos n).ne' t w
  simp_rw [acceleratedTime,he]
  exact Complex.continuous_exp.continuousAt.tendsto.comp
    (tendsto_const_nhds.mul (symbol_tendsto m w))

theorem fourier_exponent (m : ℕ) (ξ : ℝ) :
    (-1 : ℂ)^(m+1)*(Complex.I*(ξ : ℂ))^(2*m) = -((ξ : ℂ)^(2*m)) := by
  have hs : (-1 : ℂ)^m*(-1 : ℂ)^(m+1) = -1 := by
    rw [pow_succ,← mul_assoc,← mul_pow]
    norm_num
  rw [mul_pow,pow_mul,Complex.I_sq]
  calc
    _ = ((-1 : ℂ)^m*(-1 : ℂ)^(m+1))*(ξ : ℂ)^(2*m) := by ring
    _ = _ := by rw [hs]; ring

theorem actual_fourier_transform_tendsto (m : ℕ) [NeZero m] (t : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n => ∫ ω, Complex.exp (Complex.I*((2*Real.pi*ξ : ℝ) : ℂ)*
      HigherEvenRenewalProcess.process m (smallAmplitude n) (acceleratedTime m n t) ω)
        ∂HigherEvenRenewalProcess.probability m) atTop (𝓝 (HigherHeatL2.symbol m t ξ)) := by
  have h := actual_transform_tendsto m t (Complex.I*((2*Real.pi*ξ : ℝ) : ℂ))
  rw [fourier_exponent] at h
  convert h using 1
  unfold HigherHeatL2.symbol
  rw [Complex.ofReal_exp]
  congr 2
  push_cast
  ring

end OperatorDerivativeRewrite.Foundation.HigherEvenHeatTransformLimit
