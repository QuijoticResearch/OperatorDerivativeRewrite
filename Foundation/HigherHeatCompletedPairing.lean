import Foundation.HigherHeatCommonDampedProduct
import Foundation.HigherHeatDilationLaw
import Foundation.HigherHeatCompletedSignedMean

/-! A bounded symmetric signed pairing extending actual products of polynomial cylinders.
This is not a positive inner product or a chronological stochastic integral. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCompletedPairing
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCylinderDilation
open HigherHeatDilationLaw HigherHeatCompletedSignedMean
open scoped NNReal

def pairing (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Domain →L[ℝ] Domain →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ Domain Domain ℝ)
    (mean m hm (horizon m T) (horizon_pos m T hT))).comp HigherHeatCommonDampedProduct.product

theorem pairing_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u v : Domain) :
    pairing m hm T hT u v = mean m hm (horizon m T) (horizon_pos m T hT)
      (HigherHeatCommonDampedProduct.product u v) := rfl

theorem pairing_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u v : Domain) :
    |pairing m hm T hT u v| ≤ Real.exp ((horizon m T:ℝ≥0):ℝ)*‖u‖*‖v‖ := by
  rw [pairing_apply]
  calc
    _ ≤ Real.exp (horizon m T:ℝ) * ‖HigherHeatCommonDampedProduct.product u v‖ := mean_bound _ _ _ _ _
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (HigherHeatCommonDampedProduct.product_bound u v)
        (Real.exp_pos _).le

theorem pairing_core_complex (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (F G : Cylinder) :
    (pairing m hm T hT (core F) (core G) : ℂ) = cylindricalExpectation m hm T hT (F*G) := by
  rw [pairing_apply, HigherHeatCommonDampedProduct.product_core, mean_core_complex, cylinder_dilation]

theorem pairing_core_real (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (F G : Cylinder) :
    pairing m hm T hT (core F) (core G) = (cylindricalExpectation m hm T hT (F*G)).re := by
  simpa only [Complex.ofReal_re] using congrArg Complex.re (pairing_core_complex m hm T hT F G)

theorem pairing_comm (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u v : Domain) :
    pairing m hm T hT u v = pairing m hm T hT v u := by
  rw [pairing_apply, HigherHeatCommonDampedProduct.product_comm, pairing_apply]

theorem pairing_unique (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (B : Domain →L[ℝ] Domain →L[ℝ] ℝ)
    (hB : ∀ F G, (B (core F) (core G):ℂ) = cylindricalExpectation m hm T hT (F*G)) :
    B = pairing m hm T hT := by
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer B.continuous (pairing m hm T hT).continuous
  funext F
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer (B (core F)).continuous (pairing m hm T hT (core F)).continuous
  funext G
  apply Complex.ofReal_injective
  exact (hB F G).trans (pairing_core_complex m hm T hT F G).symm

theorem pairing_one (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Domain) :
    pairing m hm T hT u (core 1) = mean m hm T hT u := by
  refine core_dense.induction_on u ?_ ?_
  · exact isClosed_eq (by fun_prop) (mean m hm T hT).continuous
  · intro F
    rw [pairing_core_real, mul_one, mean_core_real]

theorem pairing_biharmonic_square (T : ℝ≥0) (hT : 0 < T) :
    pairing 2 (by norm_num) T hT (core (terminalCylinder^2)) (core (terminalCylinder^2)) =
      -24*(T:ℝ) := by
  rw [pairing_core_real, ← mean_core_real 2 (by norm_num) T hT, ← pow_add]
  exact mean_biharmonic_fourth T hT

theorem pairing_not_positive (T : ℝ≥0) (hT : 0 < T) :
    ∃ u : Domain, pairing 2 (by norm_num) T hT u u < 0 := by
  refine ⟨core (terminalCylinder^2), ?_⟩
  rw [pairing_biharmonic_square]
  exact mul_neg_of_neg_of_pos (by norm_num) (by exact_mod_cast hT)

end OperatorDerivativeRewrite.Foundation.HigherHeatCompletedPairing
