import Foundation.HigherEvenHeatTransformLimit
import Foundation.MarkedRenewalFourierTests

/-! All-even-order higher-heat limits of actual expectations on compact Fourier bands. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherEvenBandHeatLimit
open HigherEvenRenewalEnergy HigherEvenHeatTransformLimit BandLimitedComplexExtension

def kernel (m : ℕ) [NeZero m] (n : ℕ) (t : ℝ≥0) (ξ : ℝ) : ℂ :=
  Complex.exp ((t : ℂ)*HigherEvenRenewalTransform.normalizedSymbol m
    (smallAmplitude n) (Complex.I*(ξ : ℂ)))

def bound (m : ℕ) (R : ℝ≥0) : ℝ :=
  (R : ℝ)^(2*m)+(Nat.factorial (2*m) : ℝ)*(R : ℝ)^(2*m+1)*Real.exp R

theorem symbol_bound (m : ℕ) [NeZero m] (n : ℕ) (R : ℝ≥0) (ξ : ℝ)
    (hξ : |ξ| ≤ (R : ℝ)) :
    ‖HigherEvenRenewalTransform.normalizedSymbol m (smallAmplitude n) (Complex.I*(ξ : ℂ))‖ ≤
      bound m R := by
  let S := HigherEvenRenewalTransform.normalizedSymbol m (smallAmplitude n) (Complex.I*(ξ : ℂ))
  let L := (-1 : ℂ)^(m+1)*(Complex.I*(ξ : ℂ))^(2*m)
  have he := CyclicExponentialTaylor.normalized_error_bound m (smallAmplitude n)
    (amplitude_pos n) (amplitude_le_one n) (Complex.I*(ξ : ℂ))
  have hw : ‖Complex.I*(ξ : ℂ)‖ = |ξ| := by simp
  rw [hw] at he
  have hcoef : 0 ≤ (Nat.factorial (2*m) : ℝ)*|ξ|^(2*m+1)*Real.exp |ξ| :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (abs_nonneg _) _)) (Real.exp_nonneg _)
  have hL : ‖L‖ = |ξ|^(2*m) := by
    simp [L,norm_pow]
  have hs : S = (S-L)+L := by ring
  calc
    _ = ‖(S-L)+L‖ := congrArg norm hs
    _ ≤ ‖S-L‖+‖L‖ := norm_add_le _ _
    _ ≤ ((Nat.factorial (2*m) : ℝ)*|ξ|^(2*m+1)*Real.exp |ξ|)*smallAmplitude n+
        |ξ|^(2*m) := add_le_add he hL.le
    _ ≤ ((Nat.factorial (2*m) : ℝ)*|ξ|^(2*m+1)*Real.exp |ξ|)+|ξ|^(2*m) := by
      exact add_le_add (mul_le_of_le_one_right hcoef (amplitude_le_one n)) le_rfl
    _ ≤ ((Nat.factorial (2*m) : ℝ)*(R : ℝ)^(2*m+1)*Real.exp R)+(R : ℝ)^(2*m) := by
      apply add_le_add
      · apply mul_le_mul
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg ξ) hξ _) (by positivity))
          (Real.exp_le_exp.mpr hξ) (Real.exp_nonneg _) (by positivity)
      · exact pow_le_pow_left₀ (abs_nonneg ξ) hξ _
    _ = _ := by unfold bound; ring

theorem kernel_bound (m : ℕ) [NeZero m] (n : ℕ) (t R : ℝ≥0) (ξ : ℝ)
    (hξ : |ξ| ≤ (R : ℝ)) :
    ‖kernel m n t ξ‖ ≤ Real.exp ((t : ℝ)*bound m R) := by
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg t.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (symbol_bound m n R ξ hξ) t.coe_nonneg

theorem kernel_measurable (m : ℕ) [NeZero m] (n : ℕ) (t : ℝ≥0) :
    Measurable (kernel m n t) := by
  have hz : Measurable (HigherEvenRootInnovation.innovation m (smallAmplitude n)) :=
    measurable_of_countable _
  have hf : Measurable (fun p : ℝ × ZMod (2*m) => Complex.exp
      (Complex.I*(p.1 : ℂ)*HigherEvenRootInnovation.innovation m (smallAmplitude n) p.2)) :=
    Complex.continuous_exp.measurable.comp
      ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_fst)).mul
        (hz.comp measurable_snd))
  exact Complex.continuous_exp.measurable.comp
    (measurable_const.mul (measurable_const.mul (((hf.stronglyMeasurable.integral_prod_right'
      (ν := CyclicRootProbabilityNoise.probability (2*m))).measurable.sub measurable_const))))

theorem kernel_tendsto (m : ℕ) [NeZero m] (t : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n => kernel m n t ξ) atTop
      (𝓝 ((Real.exp (-(t : ℝ)*ξ^(2*m)) : ℝ) : ℂ)) := by
  have h := Complex.continuous_exp.continuousAt.tendsto.comp
    ((symbol_tendsto m (Complex.I*(ξ : ℂ))).const_mul (t : ℂ))
  rw [fourier_exponent] at h
  have he : Complex.exp ((t : ℂ)*(-(ξ : ℂ)^(2*m))) =
      ((Real.exp (-(t : ℝ)*ξ^(2*m)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simpa only [Function.comp_def,kernel,he] using h

theorem frequency_integral_tendsto (m : ℕ) [NeZero m] (t R : ℝ≥0)
    (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    Tendsto (fun n => ∫ ξ, φ ξ*kernel m n t ξ ∂band R) atTop
      (𝓝 (∫ ξ, φ ξ*(Real.exp (-(t : ℝ)*ξ^(2*m)) : ℂ) ∂band R)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ξ => ‖φ ξ‖*Real.exp ((t : ℝ)*bound m R)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun n => hφ.aestronglyMeasurable.mul
      (kernel_measurable m n t).aestronglyMeasurable
  · exact Eventually.of_forall fun n => (frequency_bound R).mono fun ξ hξ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (kernel_bound m n t R ξ hξ) (norm_nonneg _)
  · exact hφ.norm.mul_const _
  · exact Eventually.of_forall fun ξ => (kernel_tendsto m t ξ).const_mul (φ ξ)

theorem process_mean (m : ℕ) [NeZero m] (a : ℝ) (t R : ℝ≥0)
    (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    (∫ ω, extension R φ (HigherEvenRenewalProcess.process m a t ω)
      ∂HigherEvenRenewalProcess.probability m) =
    ∫ ξ, φ ξ*Complex.exp ((t : ℂ)*HigherEvenRenewalTransform.symbol m a (Complex.I*(ξ : ℂ)))
      ∂band R :=
  MarkedRenewalFourierTests.process_mean (CyclicRootProbabilityNoise.probability (2*m))
    (HigherEvenRootInnovation.innovation m a) (measurable_of_countable _) |a|
    (fun k => (HigherEvenRenewalProcess.innovation_norm m a k).le) t R φ hφ

theorem actual_expectation_tendsto (m : ℕ) [NeZero m] (t R : ℝ≥0)
    (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    Tendsto (fun n => ∫ ω, extension R φ (HigherEvenRenewalProcess.process m
      (smallAmplitude n) (acceleratedTime m n t) ω) ∂HigherEvenRenewalProcess.probability m)
      atTop (𝓝 (∫ ξ, φ ξ*(Real.exp (-(t : ℝ)*ξ^(2*m)) : ℂ) ∂band R)) := by
  have he (n : ℕ) (ξ : ℝ) :
      Complex.exp (((acceleratedTime m n t : ℝ≥0) : ℂ)*
        HigherEvenRenewalTransform.symbol m (smallAmplitude n) (Complex.I*(ξ : ℂ))) =
      kernel m n t ξ := by
    rw [← HigherEvenRenewalTransform.process_transform]
    unfold acceleratedTime
    rw [HigherEvenRenewalTransform.normalized_transform m (smallAmplitude n) (amplitude_pos n).ne']
    rfl
  simpa only [process_mean m _ _ R φ hφ,he] using frequency_integral_tendsto m t R φ hφ

end OperatorDerivativeRewrite.Foundation.HigherEvenBandHeatLimit
