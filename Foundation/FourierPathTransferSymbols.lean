import Foundation.FourierPathDirectionalOperator
import Foundation.HigherHeatFourierPathSemigroup

/-! Necessary spectral bounds for genuine expectation/derivative transfer. -/
noncomputable section
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathTransferSymbols
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathDirectionalCharacters FourierPathDirectionalOperator
open HigherHeatFourierPathSemigroup

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem generator_bound (i : ℕ) : ‖generator levels ξ i‖ ≤ 1 := by
  calc
    ‖generator levels ξ i‖ ≤ ‖(lp.single 1 i (1:ℂ) : Coeff)‖ := Submodule.Quotient.norm_mk_le _ _
    _ = 1 := by simp

theorem expectation_generator (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    expectation levels ξ m hm T hT (generator levels ξ i)=multiplier levels ξ m T i := by
  rw [generator, expectation_mk, coefficientExpectation, synthesis_apply, tsum_eq_single i]
  · rw [lp.coeFn_single, Pi.single_eq_same, one_smul, multiplier_expected]
  · intro j hj
    rw [lp.coeFn_single, Pi.single_eq_of_ne hj, zero_smul]

def derivativeTest (h : Path) (i : ℕ) : TestSpace levels ξ :=
  eigenvalue (frequency levels ξ h i) • generator levels ξ i

theorem derivativeTest_graph (h : Path) (i : ℕ) :
    (generator levels ξ i,derivativeTest levels ξ h i) ∈ graph levels ξ h :=
  generator_mem_graph levels ξ h i

theorem expectation_derivativeTest (h : Path) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (i : ℕ) :
    expectation levels ξ m hm T hT (derivativeTest levels ξ h i)=
      eigenvalue (frequency levels ξ h i)*multiplier levels ξ m T i := by
  rw [derivativeTest, map_smul, expectation_generator, smul_eq_mul]

theorem bound_symbols (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ z ∈ graph levels ξ h, ‖expectation levels ξ m hm T hT z.2‖ ≤ C*‖z.1‖) (i : ℕ) :
    ‖eigenvalue (frequency levels ξ h i)*multiplier levels ξ m T i‖ ≤ C := by
  have hh := hb (generator levels ξ i,derivativeTest levels ξ h i) (derivativeTest_graph levels ξ h i)
  change ‖expectation levels ξ m hm T hT (derivativeTest levels ξ h i)‖ ≤ C*‖generator levels ξ i‖ at hh
  rw [expectation_derivativeTest] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (generator_bound levels ξ i) hC).trans_eq (mul_one C))

theorem continuous_transfer_bound (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (L : TestSpace levels ξ →L[ℝ] ℂ)
    (hL : ∀ z ∈ graph levels ξ h, expectation levels ξ m hm T hT z.2=L z.1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ graph levels ξ h,
      ‖expectation levels ξ m hm T hT z.2‖ ≤ C*‖z.1‖ := by
  refine ⟨‖L‖,norm_nonneg _,?_⟩
  intro z hz
  rw [hL z hz]
  exact L.le_opNorm z.1

end OperatorDerivativeRewrite.Foundation.FourierPathTransferSymbols
