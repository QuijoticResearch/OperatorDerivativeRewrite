import Foundation.HigherHeatIteratedLeibniz
import Foundation.HigherHeatThirdChannelSteps

/-! All finite signed product channels for arbitrary even heat order.
The last channel is the drift. Native and every finer signed kernel probe are
identified before extending equality to the completed analytic test dual. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAllProductChannels
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatWeakTimeAdjoint HigherHeatWeakStepFields HigherHeatDyadicStepAgreement
open HigherHeatCompletedPairing HigherHeatSecondChannelSteps HigherHeatThirdChannelSteps
open HigherHeatGridDoubling HigherHeatStepRefinement MultivariateFactorialDomain
open HigherHeatPairedDualCausality HigherHeatTimeDerivative HigherHeatIteratedLeibniz

def productChannel (m : ℕ) (T : ℝ≥0) (k : ℕ) : Field timeMeasure →L[ℝ] Dual :=
  (coefficient m T * ((2*m-1).choose k:ℝ)) • transpose timeMeasure (2*m-1-k)

theorem productChannel_coefficientField (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (k : ℕ) (j : Fin (size n)) (F G : Test n) :
    productChannel m T k (coefficientField n m hm T hT j F) (core (cylinderOf n G)) =
      coefficient m T * ((2*m-1).choose k:ℝ) * (HigherHeatDyadicLaws.duration 1 n:ℝ) *
        pairing m hm T hT (core (cylinderOf n F))
          (core (cylinderOf n
            ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[2*m-1-k] G))) := by
  change (coefficient m T * ((2*m-1).choose k:ℝ)) * transpose timeMeasure (2*m-1-k)
    (step _ _ _ _ _) (core (cylinderOf n G)) = _
  rw [transpose_step_constant timeMeasure (2*m-1-k) (gridCell n j)
    (gridCell_measurable n j) (gridCell_finite n j) _ _ _
    ((MeasureTheory.ae_restrict_mem (gridCell_measurable n j)).mono (fun t ht =>
      derivative_core_on_cell n j t ht (2*m-1-k) G)), gridCell_measure]
  ring

def correction (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) : Dual :=
  ∑ k ∈ Finset.range (2*m), productChannel m T k (coefficientField n m hm T hT j
    ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[k] F))

theorem native_agreement (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F G : Test n) :
    pairing m hm T hT (core (cylinderOf n (F*MvPolynomial.X j))) (core (cylinderOf n G)) =
      correction n m hm T hT j F (core (cylinderOf n G)) := by
  have hp (A B : Test n) :
      pairing m hm T hT (core (cylinderOf n A)) (core (cylinderOf n B)) =
        (HigherHeatMultivariateMoments.mean m hm
          (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)
          (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) (A*B)).re := by
    rw [pairing_core_real, ← map_mul (cylinderOf n), cylindricalExpectation_apply]
    rfl
  have hs := MultivariateConditionalStein.actual_coordinate_stein m hm
    (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)
    (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) j (F*G)
  have he : 2*m-1+1=2*m := by omega
  rw [derivative_iterate_mul, he, map_sum] at hs
  simp only [correction, sum_apply]
  simp_rw [productChannel_coefficientField, hp]
  simp_rw [map_nsmul] at hs
  rw [show (F*MvPolynomial.X j)*G=MvPolynomial.X j*(F*G) by ring, hs]
  simp only [Complex.real_smul, Complex.re_sum, Complex.re_nsmul, nsmul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.natCast_re, Complex.natCast_im, PureOrderPolynomialConditioning.parameters, coefficient]
  rw [← HigherHeatDyadicStepAgreement.duration_scale T n]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem correction_split (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) :
    correction n m hm T hT j F =
      correction (n+1) m hm T hT (evenIndex j) (HigherHeatPolynomialCylinders.step n F) +
      correction (n+1) m hm T hT (oddIndex j) (HigherHeatPolynomialCylinders.step n F) := by
  have hl : pairBlock (evenIndex j) = j := by apply Fin.ext; simp [pairBlock, evenIndex]
  have hr : pairBlock (oddIndex j) = j := by apply Fin.ext; dsimp [pairBlock, oddIndex]; omega
  simp only [correction, derivative_iterate_step n j _ hl F,
    derivative_iterate_step n j _ hr F]
  simp_rw [coefficientField_split n m hm T hT j]
  simp only [map_add, Finset.sum_add_distrib]

theorem agreement_finer (d n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (G : Test (n + d)) :
    pairing m hm T hT (core (cylinderOf n (F*MvPolynomial.X j)))
      (core (cylinderOf (n + d) G)) = correction n m hm T hT j F (core (cylinderOf (n + d) G)) := by
  induction d generalizing n with
  | zero => exact native_agreement n m hm T hT j F G
  | succ d ih =>
    have he : n+(d+1)=(n+1)+d := by omega
    revert G
    rw [he]
    intro G
    have hL := ih (n+1) (evenIndex j) (HigherHeatPolynomialCylinders.step n F) G
    have hR := ih (n+1) (oddIndex j) (HigherHeatPolynomialCylinders.step n F) G
    rw [stochastic_polynomial_split n j F, correction_split]
    simp only [map_add, add_apply]
    exact congrArg₂ (fun a b : ℝ => a+b) hL hR

theorem agreement_dual (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) :
    pairing m hm T hT (core (cylinderOf n (F*MvPolynomial.X j))) =
      correction n m hm T hT j F := by
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext G
  apply HigherHeatCylindricalConditioning.tail_induction n (fun G =>
    pairing m hm T hT (core (cylinderOf n (F*MvPolynomial.X j))) (core G) =
      correction n m hm T hT j F (core G)) _ G
  intro N hn P
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact agreement_finer d n m hm T hT j F P

theorem productChannel_bound (m : ℕ) (T : ℝ≥0) (k : ℕ) (A : Field timeMeasure) :
    ‖productChannel m T k A‖ ≤ ((2*m:ℕ):ℝ)*(T:ℝ)*((2*m-1).choose k:ℝ)*‖A‖ := by
  have hc : |coefficient m T * ((2*m-1).choose k:ℝ)| =
      ((2*m:ℕ):ℝ)*(T:ℝ)*((2*m-1).choose k:ℝ) := by
    simp [coefficient, abs_mul, abs_pow, abs_of_nonneg T.coe_nonneg]
  change ‖(coefficient m T * ((2*m-1).choose k:ℝ)) •
    transpose timeMeasure (2*m-1-k) A‖ ≤ _
  calc
    _ ≤ ‖coefficient m T * ((2*m-1).choose k:ℝ)‖ * ‖transpose timeMeasure (2*m-1-k) A‖ :=
      ContinuousLinearMap.opNorm_smul_le (𝕜 := ℝ) (𝕜₂ := ℝ) _ _
    _ = _ := by rw [Real.norm_eq_abs, hc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (transpose_bound timeMeasure (2*m-1-k) A) (by positivity)

theorem first_channel (m : ℕ) (T : ℝ≥0) : productChannel m T 0 = firstChannel m T := by
  simp [productChannel, firstChannel]

theorem drift_channel (m : ℕ) (T : ℝ≥0) :
    productChannel m T (2*m-1) = coefficient m T • transpose timeMeasure 0 := by
  simp [productChannel]

end OperatorDerivativeRewrite.Foundation.HigherHeatAllProductChannels
