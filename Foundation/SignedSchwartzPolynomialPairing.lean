import Foundation.SignedSchwartzPolynomialJets
import Foundation.SignedSchwartzMeanProjection
import Foundation.PureOrderAppellPairing

/-! Continuous actual signed polynomial tests on the positive marginal completion. -/
noncomputable section
open MeasureTheory Polynomial Filter
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzPolynomialPairing
open SignedSchwartzL2Rigging SignedSchwartzPolynomialL2 SignedSchwartzFundamentalSymmetry

def polynomialMap (K : 𝓢(ℝ, ℝ)) : Polynomial ℝ →ₗ[ℝ] H K where
  toFun := polynomialL2 K
  map_add' P Q := by
    apply Lp.ext
    filter_upwards [polynomialL2_ae K (P+Q), polynomialL2_ae K P,
      polynomialL2_ae K Q, Lp.coeFn_add (polynomialL2 K P) (polynomialL2 K Q)] with x ha hp hq hs
    simp only [ha, hs, hp, hq, eval_add, Complex.ofReal_add, Pi.add_apply]
  map_smul' c P := by
    apply Lp.ext
    filter_upwards [polynomialL2_ae K (c • P), polynomialL2_ae K P,
      Lp.coeFn_smul c (polynomialL2 K P)] with x ha hp hs
    simp only [ha, hs, hp, eval_smul, smul_eq_mul, RingHom.id_apply,
      Complex.ofReal_mul, Complex.real_smul, Pi.smul_apply]

theorem polynomialMap_apply (K : 𝓢(ℝ, ℝ)) (P : Polynomial ℝ) :
    polynomialMap K P = polynomialL2 K P := rfl

theorem form_polynomial_density (K : 𝓢(ℝ, ℝ)) (P Q : Polynomial ℝ) :
    form K (polynomialL2 K P) (polynomialL2 K Q) =
      ∫ x : ℝ, K x * P.eval x * Q.eval x := by
  have he : form K (polynomialL2 K P) (polynomialL2 K Q) =
      ∫ x, sign K x * P.eval x * Q.eval x ∂measure K := by
    rw [form_apply, L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [symmetry_ae K (polynomialL2 K P), polynomialL2_ae K P,
      polynomialL2_ae K Q] with x hs hp hq
    change inner ℝ ((symmetry K (polynomialL2 K P)) x) ((polynomialL2 K Q) x) = _
    rw [hs, hp, hq, real_inner_smul_left]
    rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
    change sign K x * ((((Q.eval x : ℝ) : ℂ) * star (((P.eval x : ℝ) : ℂ))).re) = _
    simp [mul_assoc, mul_comm, mul_left_comm]
  rw [he, SignedSchwartzMeanProjection.weighted_integral]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change |K x| * (sign K x * P.eval x * Q.eval x) = _
    rw [← mul_assoc, ← mul_assoc, sign_density])

def test (K : 𝓢(ℝ, ℝ)) (Q : Polynomial ℝ) : H K →L[ℝ] ℝ :=
  form K (polynomialL2 K Q)

theorem test_polynomial (K : 𝓢(ℝ, ℝ)) (P Q : Polynomial ℝ) :
    test K Q (polynomialL2 K P) = ∫ x : ℝ, K x * Q.eval x * P.eval x :=
  form_polynomial_density K Q P

theorem test_norm_bound (K : 𝓢(ℝ, ℝ)) (Q : Polynomial ℝ) (u : H K) :
    |test K Q u| ≤ ‖polynomialL2 K Q‖ * ‖u‖ := by
  exact (abs_real_inner_le_norm (symmetry K (polynomialL2 K Q)) u).trans_eq (by rw [symmetry_norm])

theorem higherHeat_test (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (P Q : Polynomial ℝ) :
    test (HigherHeatSignedLaws.realKernel m hm t ht) Q
      (polynomialL2 (HigherHeatSignedLaws.realKernel m hm t ht) P) =
      HigherHeatPolynomialRealization.kernelExpectation m hm t ht (Q*P) := by
  rw [test_polynomial]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by simp only [eval_mul]; ring)

theorem higherHeat_polynomialMap_injective (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    Function.Injective (polynomialMap (HigherHeatSignedLaws.realKernel m hm t ht)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro P hP
  apply PureOrderAppellPairing.full_pairing_nondegenerate (2*m) (by omega)
    ((-1:ℝ)^(m+1)*(t:ℝ))
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (by exact_mod_cast ht)))
  intro Q
  have he := higherHeat_test m hm t ht P Q
  rw [← polynomialMap_apply, hP, map_zero,
    HigherHeatPolynomialRealization.kernelExpectation_eq_moments] at he
  exact he.symm

end OperatorDerivativeRewrite.Foundation.SignedSchwartzPolynomialPairing
