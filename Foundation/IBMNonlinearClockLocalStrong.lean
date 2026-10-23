import Foundation.IBMNonlinearClockContraction
import Foundation.BochnerCoefficientCauchy

/-! Strong localized convergence in the FULL coefficient-valued Gaussian L2
space. The summable coefficient majorant is the actual linear occupation trace. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearClockLocalStrong
open InfiniteGaussian IBMClockPhysicalOccupation IBMNonlinearClockLocalization
open IBMNonlinearSpatialOperator BochnerCoefficientParseval
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem finiteField_norm_le (h : CoefficientSpace) (n : ℕ) (χ : ℝ → ℝ)
    (hc : Continuous χ) (hs : HasCompactSupport χ) {a b : ℝ} (hab : a ≤ b) (T : ℝ≥0) :
    ‖finiteField h n χ hc hs hab T‖ ≤
      (Real.sqrt (1+4*(b-a))*‖cutoffInput χ hc hs a b‖)*‖kernel h T‖ := by
  let L := cutoffInput χ hc hs a b
  let u := L.compLpL 2 gaussianProduct (kernel h T)
  change ‖(operator n hab).compLp u‖ ≤ _
  calc
    _ ≤ ‖operator n hab‖*‖u‖ := (operator n hab).norm_compLp_le u
    _ ≤ Real.sqrt (1+4*(b-a))*‖u‖ :=
      mul_le_mul_of_nonneg_right (operator_norm_le n hab) (norm_nonneg _)
    _ ≤ Real.sqrt (1+4*(b-a))*(‖L‖*‖kernel h T‖) :=
      mul_le_mul_of_nonneg_left (L.norm_compLp_le (kernel h T)) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem localized_cauchy (χ : ℝ → ℝ) (hc : Continuous χ) (hs : HasCompactSupport χ)
    (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) {a b : ℝ} (hab : a ≤ b)
    (hwin : ∀ r, r ∉ Ioc a b → χ r = 0) (T : ℝ≥0) :
    CauchySeq (fun n => IBMNonlinearClockTailEnergy.average (fun x => χ |x|) n T) := by
  let M := Real.sqrt (1+4*(b-a))*‖cutoffInput χ hc hs a b‖
  have hk : Summable (fun i => ‖kernel (basis i) T‖^2) := by
    simpa only [kernel_norm] using (directional_hasSum (gradient T)).summable
  apply BochnerCoefficientCauchy.cauchy_of_coordinates _
    (fun i => M^2*‖kernel (basis i) T‖^2) (hk.mul_left (M^2))
  · intro n i
    rw [IBMNonlinearClockContraction.average_contraction (basis i) χ hc hs h0 h1,
      ← finiteField_eq_native (basis i) n χ hc hs hab hwin T]
    have hb := pow_le_pow_left₀ (norm_nonneg _)
      (finiteField_norm_le (basis i) n χ hc hs hab T) 2
    simpa only [M,mul_pow] using hb
  · intro i
    exact (IBMNonlinearClockContraction.contraction_tendsto (basis i) χ hc hs h0 h1
      hab hwin T).cauchySeq

theorem exists_localized_limit (χ : ℝ → ℝ) (hc : Continuous χ) (hs : HasCompactSupport χ)
    (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) {a b : ℝ} (hab : a ≤ b)
    (hwin : ∀ r, r ∉ Ioc a b → χ r = 0) (T : ℝ≥0) :
    ∃ v : IBMClockAverageCandidate.Target,
      Tendsto (fun n => IBMNonlinearClockTailEnergy.average (fun x => χ |x|) n T)
        atTop (𝓝 v) :=
  cauchySeq_tendsto_of_complete (localized_cauchy χ hc hs h0 h1 hab hwin T)

end OperatorDerivativeRewrite.Foundation.IBMNonlinearClockLocalStrong
