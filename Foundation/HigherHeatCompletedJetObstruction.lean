import Foundation.SignedSchwartzPolynomialPairing

/-! The highest jet cannot reconstruct centered polynomials in the actual completed domain. -/
noncomputable section
open MeasureTheory Polynomial Filter
open scoped SchwartzMap NNReal Topology

namespace OperatorDerivativeRewrite.Foundation.HigherHeatCompletedJetObstruction
open HigherHeatSignedLaws HigherHeatPolynomialRealization SignedSchwartzL2Rigging
open SignedSchwartzPolynomialL2 SignedSchwartzPolynomialPairing SignedSchwartzPolynomialJets

theorem polynomialDomain_injective (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (r : ℕ) :
    Function.Injective (polynomialDomain (realKernel m hm t ht) r) := by
  intro P Q he
  apply higherHeat_polynomialMap_injective m hm t ht
  exact congrArg (SignedSchwartzJetDomain.value (realKernel m hm t ht) r) he

theorem polynomialL2_zero (K : 𝓢(ℝ, ℝ)) : polynomialL2 K 0 = 0 :=
  (polynomialMap K).map_zero

theorem linear_nonzero (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    polynomialL2 (realKernel m hm t ht) X ≠ 0 := by
  intro he
  have hp : polynomialMap (realKernel m hm t ht) X =
      polynomialMap (realKernel m hm t ht) 0 := by
    rw [polynomialMap_apply, polynomialMap_apply, he, polynomialL2_zero]
  exact Polynomial.X_ne_zero (higherHeat_polynomialMap_injective m hm t ht hp)

theorem linear_mean_zero (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    kernelExpectation m hm t ht X = 0 := by
  rw [kernelExpectation_eq_moments]
  exact PseudoClarkOconeObstruction.linear_mean_zero (2*m) (by omega) _

theorem linear_highest_jet_zero (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    SignedSchwartzJetDomain.component (realKernel m hm t ht) (2*m) ⟨2*m, by omega⟩
      (polynomialDomain (realKernel m hm t ht) (2*m) X) = 0 := by
  rw [polynomialDomain_component]
  change polynomialL2 (realKernel m hm t ht) (Polynomial.derivative^[2*m] X) = 0
  rw [Polynomial.iterate_derivative_X (by omega), polynomialL2_zero]

theorem no_highest_jet_reconstruction (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (R : H (realKernel m hm t ht) → H (realKernel m hm t ht)) :
    ¬ ∀ P : Polynomial ℝ,
      R (SignedSchwartzJetDomain.component (realKernel m hm t ht) (2*m) ⟨2*m, by omega⟩
        (polynomialDomain (realKernel m hm t ht) (2*m) P)) =
      polynomialL2 (realKernel m hm t ht) (P-C (kernelExpectation m hm t ht P)) := by
  intro h
  have hzero := h 0
  rw [polynomialDomain_component, Polynomial.iterate_derivative_zero,
    polynomialL2_zero, map_zero, map_zero, sub_zero, polynomialL2_zero] at hzero
  have hx := h X
  rw [linear_highest_jet_zero, linear_mean_zero, map_zero, sub_zero, hzero] at hx
  exact linear_nonzero m hm t ht hx.symm

theorem no_highest_jet_bound (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    ¬ ∃ c : ℝ, ∀ P : Polynomial ℝ,
      ‖polynomialL2 (realKernel m hm t ht) (P-C (kernelExpectation m hm t ht P))‖ ≤
      c * ‖SignedSchwartzJetDomain.component (realKernel m hm t ht) (2*m) ⟨2*m, by omega⟩
        (polynomialDomain (realKernel m hm t ht) (2*m) P)‖ := by
  rintro ⟨c, hc⟩
  have hx := hc X
  rw [linear_mean_zero, map_zero, sub_zero, linear_highest_jet_zero, norm_zero, mul_zero] at hx
  exact linear_nonzero m hm t ht (norm_eq_zero.mp (le_antisymm hx (norm_nonneg _)))

end OperatorDerivativeRewrite.Foundation.HigherHeatCompletedJetObstruction
