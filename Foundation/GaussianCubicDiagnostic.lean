import Foundation.GaussianScalarPolynomialIto

/-! An explicit distinction between the terminal martingale representer and
the running spatial derivative in polynomial Itô. This diagnoses the invalid
projection substitution in the manuscript; it does not claim a bounded-C³ counterexample. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianCubicDiagnostic
open InfiniteGaussian GaussianTimeSpaceHermite GaussianHermiteRepresentation
open GaussianHermiteIntegrand GaussianPredictableFull GaussianPredictableAdjoint
open GaussianTimeProductL2 GaussianProductDerivative GaussianPolynomialProcess GaussianPolynomialIto
open GaussianPolynomialDifferentiation GaussianScalarPolynomialIto

theorem value_three (x t : ℝ) : value 3 x t = x ^ 3 - 3 * t * x := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, value_recursion]
  norm_num [value_two, value_one]
  ring

theorem cubic_expansion (T : ℝ≥0) :
    polynomialValue T (Polynomial.X ^ 3) = (brownianCore T 3 : GaussianL2) +
      (3 * (T : ℝ)) • (brownianCore T 1 : GaussianL2) := by
  apply Lp.ext
  filter_upwards [polynomialValue_coeFn T (Polynomial.X ^ 3), brownianCore_coeFn T 3,
    brownianCore_coeFn T 1, Lp.coeFn_add (brownianCore T 3 : GaussianL2)
      ((3 * (T : ℝ)) • (brownianCore T 1 : GaussianL2)),
    Lp.coeFn_smul (3 * (T : ℝ)) (brownianCore T 1 : GaussianL2)] with ω hp h3 h1 ha hs
  rw [hp, ha]
  simp only [Pi.add_apply, hs, Pi.smul_apply, h3, h1, value_three, value_one,
    Polynomial.eval_pow, Polynomial.eval_X, smul_eq_mul]
  ring

def cubicIntegrand (T : ℝ≥0) : fullPredictable :=
  (3 : ℝ) • hermiteIntegrand 2 T + (3 * (T : ℝ)) • hermiteIntegrand 0 T

theorem integral_cubicIntegrand (T : ℝ≥0) :
    itoIntegral (cubicIntegrand T) = polynomialValue T (Polynomial.X ^ 3) := by
  rw [cubicIntegrand, map_add, map_smul, map_smul, integral_hermiteIntegrand,
    integral_hermiteIntegrand, cubic_expansion]
  norm_num [smul_smul]

theorem cubic_predictableAdjoint (T : ℝ≥0) :
    predictableAdjoint (polynomialValue T (Polynomial.X ^ 3)) = cubicIntegrand T := by
  rw [← integral_cubicIntegrand, predictableAdjoint_integral]

theorem cubicIntegrand_slices (T : ℝ≥0) :
    scalarCurry (cubicIntegrand T : TimeProbabilityL2) =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (fun x =>
        (3 : ℝ) • (brownianCore x.toNNReal 2 : GaussianL2) + (3 * (T : ℝ)) • gaussianOne) := by
  change scalarCurry ((3 : ℝ) • (hermiteIntegrand 2 T : TimeProbabilityL2) +
    (3 * (T : ℝ)) • (hermiteIntegrand 0 T : TimeProbabilityL2)) =ᵐ[volume] _
  rw [map_add, map_smul, map_smul]
  filter_upwards [Lp.coeFn_add ((3 : ℝ) • scalarCurry (hermiteIntegrand 2 T))
    ((3 * (T : ℝ)) • scalarCurry (hermiteIntegrand 0 T)),
    Lp.coeFn_smul (3 : ℝ) (scalarCurry (hermiteIntegrand 2 T)),
    Lp.coeFn_smul (3 * (T : ℝ)) (scalarCurry (hermiteIntegrand 0 T)),
    hermiteIntegrand_slices 2 T, hermiteIntegrand_slices 0 T] with x ha h2 h0 hs2 hs0
  rw [ha]
  change ((3 : ℝ) • scalarCurry (hermiteIntegrand 2 T)) x +
    ((3 * (T : ℝ)) • scalarCurry (hermiteIntegrand 0 T)) x = _
  rw [h2, h0]
  change (3 : ℝ) • scalarCurry (hermiteIntegrand 2 T) x +
    (3 * (T : ℝ)) • scalarCurry (hermiteIntegrand 0 T) x = _
  rw [hs2, hs0]
  by_cases hx : x ∈ Ioc 0 (T : ℝ) <;> simp [horizonValue, hx, brownianCore_zero_degree]

theorem cubic_spatial_value (t : ℝ≥0) :
    valueL2 t (MvPolynomial.pderiv 1 (spatialPolynomial (Polynomial.X ^ 3))) =
      (3 : ℝ) • (brownianCore t 2 : GaussianL2) + (3 * (t : ℝ)) • gaussianOne := by
  rw [spatialPolynomial_spatial]
  apply Lp.ext
  filter_upwards [polynomialValue_coeFn t (Polynomial.X ^ 3).derivative,
    brownianCore_coeFn t 2, gaussianOne_coeFn,
    Lp.coeFn_add ((3 : ℝ) • (brownianCore t 2 : GaussianL2)) ((3 * (t : ℝ)) • gaussianOne),
    Lp.coeFn_smul (3 : ℝ) (brownianCore t 2 : GaussianL2),
    Lp.coeFn_smul (3 * (t : ℝ)) gaussianOne] with ω hp h2 h1 ha hs2 hs0
  change polynomialValue t (Polynomial.X ^ 3).derivative ω = _
  rw [hp, ha]
  simp only [Pi.add_apply, hs2, hs0, Pi.smul_apply, h2, h1, value_two,
    Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, smul_eq_mul]
  norm_num
  ring

theorem cubic_projection_difference_slices (T : ℝ≥0) :
    scalarCurry (predictableAdjoint (polynomialValue T (Polynomial.X ^ 3)) : TimeProbabilityL2) -
      spatialField T (spatialPolynomial (Polynomial.X ^ 3)) =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (fun x => (3 * ((T : ℝ) - x)) • gaussianOne) := by
  rw [cubic_predictableAdjoint]
  filter_upwards [Lp.coeFn_sub (scalarCurry (cubicIntegrand T))
    (spatialField T (spatialPolynomial (Polynomial.X ^ 3))), cubicIntegrand_slices T,
    spatialField_coeFn T (spatialPolynomial (Polynomial.X ^ 3))] with x hd hc hs
  rw [hd]
  change scalarCurry (cubicIntegrand T) x - spatialField T (spatialPolynomial (Polynomial.X ^ 3)) x = _
  rw [hc, hs]
  by_cases hx : x ∈ Ioc 0 (T : ℝ)
  · simp only [indicator_of_mem hx, cubic_spatial_value, Real.coe_toNNReal _ hx.1.le]
    module
  · simp [hx]

/-- Quantitative failure of the terminal-projection/running-derivative substitution. -/
theorem cubic_projection_difference_norm_sq (T : ℝ≥0) :
    ‖scalarCurry (predictableAdjoint (polynomialValue T (Polynomial.X ^ 3)) : TimeProbabilityL2) -
      spatialField T (spatialPolynomial (Polynomial.X ^ 3))‖ ^ 2 = 3 * (T : ℝ) ^ 3 := by
  have h1 : ‖gaussianOne‖ ^ 2 = (1 : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, GaussianDeterministicGraphCore.gaussianOne_inner_self]
  rw [BochnerL2Dominated.norm_sq_integral]
  calc
    _ = ∫ x, (Ioc 0 (T : ℝ)).indicator (fun x => (3 * ((T : ℝ) - x)) ^ 2) x := by
      apply integral_congr_ae
      filter_upwards [cubic_projection_difference_slices T] with x hx
      rw [hx]
      by_cases hxt : x ∈ Ioc 0 (T : ℝ)
      · simp only [indicator_of_mem hxt, norm_smul, mul_pow, h1, mul_one,
          Real.norm_eq_abs, sq_abs]
      · simp [hxt]
    _ = ∫ x in 0..(T : ℝ), (3 * ((T : ℝ) - x)) ^ 2 := by
      rw [integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le T.coe_nonneg]
    _ = _ := by
      have hd (x : ℝ) : HasDerivAt (fun x => -3 * ((T : ℝ) - x) ^ 3)
          ((3 * ((T : ℝ) - x)) ^ 2) x := by
        convert (((hasDerivAt_const x (T : ℝ)).sub (hasDerivAt_id x)).pow 3).const_mul (-3) using 1 <;>
          (try funext y) <;> simp <;> ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
        ((continuous_const.mul (continuous_const.sub continuous_id)).pow 2 |>.intervalIntegrable _ _)]
      simp

theorem cubic_projection_ne_running_derivative (T : ℝ≥0) (hT : 0 < T) :
    scalarCurry (predictableAdjoint (polynomialValue T (Polynomial.X ^ 3)) : TimeProbabilityL2) ≠
      spatialField T (spatialPolynomial (Polynomial.X ^ 3)) := by
  intro he
  have h := cubic_projection_difference_norm_sq T
  rw [he, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  have hp : 0 < 3 * (T : ℝ) ^ 3 := by positivity
  linarith

end OperatorDerivativeRewrite.Foundation.GaussianCubicDiagnostic
