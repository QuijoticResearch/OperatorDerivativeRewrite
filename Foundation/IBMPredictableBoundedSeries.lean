import Foundation.IBMPredictableBoundedApproximation
import Mathlib.Analysis.InnerProductSpace.Subspace

/-! Actual bounded G-channel grids and series in the completed predictable domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableBoundedSeries
open IBMPredictableRectangles IBMPredictableCoefficientLift IBMPredictableLpDictionary
open IBMPredictableBoundedApproximation IBMTimeAveragedObservable
open IBMIntrinsicRightGerm IBMRightGermFiltration IBMGermPredictableStep
open IBMIntrinsicMartingaleStep (Coefficient)
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable

theorem finite_integral {ι : Type*} (F : JointL2) (I : Finset ι)
    (s t : ι → ℝ≥0) (hst : ∀ i, s i ≤ t i) (a : ∀ i, Coefficient (s i)) :
    IBMFullPredictableIntegral.integral F (∑ i ∈ I, coefficientLp F (hst i) (a i)) =
      IBMGermIndicatorSupport.sumClass F I s t a := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => integral_identification F (hst i) (a i)

def incrementSpace (τ : ℕ → ℝ≥0) (i : ℕ) : Submodule ℝ JointL2 :=
  rightPast (τ (i+1)) ⊓ (rightPast (τ i))ᗮ

theorem increment_orthogonal (τ : ℕ → ℝ≥0) (hτ : Monotone τ) :
    OrthogonalFamily ℝ (fun i => incrementSpace τ i)
      (fun i => (incrementSpace τ i).subtypeₗᵢ) := by
  intro i j hij f g
  rcases lt_or_gt_of_ne hij with h | h
  · exact Submodule.inner_right_of_mem_orthogonal
      (rightPast_mono (hτ (Nat.succ_le_of_lt h)) f.property.1) g.property.2
  · rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      (rightPast_mono (hτ (Nat.succ_le_of_lt h)) g.property.1) f.property.2

def component (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i)) (i : ℕ) : incrementSpace τ i :=
  ⟨stepClass F (τ i) (τ (i+1)) (a i), stepClass_mem_rightPast F (hτ (Nat.le_succ i)) (a i),
    fun g hg => past_inner_step_zero F (hτ (Nat.le_succ i)) (a i) g hg⟩

theorem stochastic_summable (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass F (τ i) (τ (i+1)) (a i)‖ ^ 2)) :
    Summable (fun i => stepClass F (τ i) (τ (i+1)) (a i)) :=
  ((increment_orthogonal τ hτ).summable_iff_norm_sq_summable (component F τ hτ a)).mpr ha

theorem integrand_summable (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass F (τ i) (τ (i+1)) (a i)‖ ^ 2)) :
    Summable (fun i => coefficientLp F (hτ (Nat.le_succ i)) (a i)) := by
  have hs := stochastic_summable F τ hτ a ha
  rw [summable_iff_cauchySeq_finset] at hs ⊢
  simpa only [NormedAddCommGroup.cauchySeq_iff,
    ← (IBMFullPredictableIntegral.integral F).norm_map, map_sub, map_add, map_neg, map_sum,
    integral_identification] using hs

theorem countable_integral (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass F (τ i) (τ (i+1)) (a i)‖ ^ 2)) :
    IBMFullPredictableIntegral.integral F
      (∑' i, coefficientLp F (hτ (Nat.le_succ i)) (a i)) =
      ∑' i, stepClass F (τ i) (τ (i+1)) (a i) := by
  have h := (integrand_summable F τ hτ a ha).map_tsum
    (IBMFullPredictableIntegral.integral F).toLinearMap.toAddMonoidHom
    (IBMFullPredictableIntegral.integral F).continuous
  change IBMFullPredictableIntegral.integral F
    (∑' i, coefficientLp F (hτ (Nat.le_succ i)) (a i)) =
    ∑' i, IBMFullPredictableIntegral.integral F (coefficientLp F (hτ (Nat.le_succ i)) (a i)) at h
  simpa only [integral_identification] using h

theorem countable_approximation (F : JointL2) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (a : ∀ i, Coefficient (τ i))
    (ha : Summable (fun i => ‖stepClass F (τ i) (τ (i+1)) (a i)‖ ^ 2)) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, coefficientLp F (hτ (Nat.le_succ i)) (a i))
      atTop (𝓝 (∑' i, coefficientLp F (hτ (Nat.le_succ i)) (a i))) ∧
    Tendsto (fun n => ∑ i ∈ Finset.range n, stepClass F (τ i) (τ (i+1)) (a i))
      atTop (𝓝 (IBMFullPredictableIntegral.integral F
        (∑' i, coefficientLp F (hτ (Nat.le_succ i)) (a i)))) := by
  refine ⟨(integrand_summable F τ hτ a ha).hasSum.tendsto_sum_nat, ?_⟩
  rw [countable_integral F τ hτ a ha]
  exact (stochastic_summable F τ hτ a ha).hasSum.tendsto_sum_nat

end OperatorDerivativeRewrite.Foundation.IBMPredictableBoundedSeries
