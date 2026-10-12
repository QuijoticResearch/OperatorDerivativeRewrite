import Foundation.GaussianLocalIncrementEnergy

/-! Exact second-chaos covariance from genuine Gaussian IBP. These are the
random squared-increment estimates needed for quadratic variation, rather
than a replacement of random squares by expected energies. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticIncrement
open InfiniteGaussian GaussianTimePolynomialPairing GaussianTimeSensitivity
open GaussianTimeDivergence GaussianTimeFieldNorm GaussianDeterministicGraphCore

def oneCore : polynomialCylindricalDomain :=
  pastCoefficient (fun _ : Fin 0 => 0) (MvPolynomial.C 1)

theorem oneCore_eq : (oneCore : GaussianL2) = gaussianOne := by
  simpa only [oneCore, one_smul] using constant_pastCoefficient 1

theorem oneCore_derivative : polynomialDerivative oneCore = 0 :=
  polynomialDerivative_empty _ _

def centeredSquare (h : CoefficientSpace) : polynomialCylindricalDomain :=
  polynomialProduct (firstChaosPolynomial h) (firstChaosPolynomial h) - ‖h‖ ^ 2 • oneCore

theorem centeredSquare_coeFn (h : CoefficientSpace) :
    (centeredSquare h : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => (firstChaosEmbedding h ω) ^ 2 - ‖h‖ ^ 2 := by
  filter_upwards [Lp.coeFn_sub
    (polynomialProduct (firstChaosPolynomial h) (firstChaosPolynomial h) : GaussianL2)
    (‖h‖ ^ 2 • (oneCore : GaussianL2)),
    polynomialProductL2_coeFn (firstChaosPolynomial h) (firstChaosPolynomial h),
    firstChaosPolynomial_coeFn h, Lp.coeFn_smul (‖h‖ ^ 2) (oneCore : GaussianL2),
    (oneCore_eq.symm ▸ gaussianOne_coeFn)] with ω hsub hp hf hs h1
  change (centeredSquare h : GaussianL2) ω = _ at hsub
  rw [hsub]
  change polynomialProductL2 (firstChaosPolynomial h) (firstChaosPolynomial h) ω -
    (‖h‖ ^ 2 • (oneCore : GaussianL2)) ω = _
  rw [hp, hf, hs]
  simp only [Pi.smul_apply, h1, smul_eq_mul, mul_one, pow_two]

theorem centeredSquare_derivative (h : CoefficientSpace) :
    polynomialDerivative (centeredSquare h) = (2 : ℝ) • scalarTensor h (firstChaosPolynomial h) := by
  rw [centeredSquare, map_sub, map_smul, oneCore_derivative, smul_zero, sub_zero,
    polynomialDerivative_product, polynomialTimesDerivative_firstChaos]
  rw [two_smul ℝ]

theorem centeredSquare_eq_rankDivergence (h : CoefficientSpace) :
    (centeredSquare h : GaussianL2) = rankDivergence (firstChaosPolynomial h) h := by
  apply Lp.ext
  filter_upwards [centeredSquare_coeFn h, rankDivergence_coeFn (firstChaosPolynomial h) h,
    firstChaosPolynomial_coeFn h, firstChaosPolynomial_derivative_coeFn h] with ω hc hr hf hd
  rw [hc, hr, hf, hd, real_inner_self_eq_norm_sq, pow_two]

theorem centeredSquare_centered (h : CoefficientSpace) :
    inner ℝ gaussianOne (centeredSquare h : GaussianL2) = 0 := by
  have hi := polynomialDerivative_rank_pairing oneCore (firstChaosPolynomial h) h
  rw [oneCore_derivative, oneCore_eq, ← centeredSquare_eq_rankDivergence] at hi
  simpa using hi.symm

/-- Wick's second-chaos covariance is derived from the proved actual derivative
and adjoint pairing, without a fourth-moment assumption. -/
theorem centeredSquare_inner (h k : CoefficientSpace) :
    inner ℝ (centeredSquare h : GaussianL2) (centeredSquare k : GaussianL2) =
      2 * (inner ℝ h k) ^ 2 := by
  have hi := polynomialDerivative_rank_pairing (centeredSquare h) (firstChaosPolynomial k) k
  rw [centeredSquare_derivative, real_inner_smul_left, scalarTensor_pair_inner,
    ← centeredSquare_eq_rankDivergence] at hi
  have hf : inner ℝ (firstChaosPolynomial h : GaussianL2) (firstChaosPolynomial k : GaussianL2) =
      inner ℝ h k := by
    rw [Lp.ext (firstChaosPolynomial_coeFn h), Lp.ext (firstChaosPolynomial_coeFn k)]
    exact firstChaosEmbedding.inner_map_map h k
  rw [hf] at hi
  rw [← hi]
  ring

theorem centeredSquare_norm_sq (h : CoefficientSpace) :
    ‖(centeredSquare h : GaussianL2)‖ ^ 2 = 2 * (‖h‖ ^ 2) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, centeredSquare_inner, real_inner_self_eq_norm_sq]

def incrementSquareError (s t : ℝ≥0) : GaussianL2 :=
  centeredSquare (incrementDirection s t)

theorem incrementSquareError_coeFn (s t : ℝ≥0) (hst : s ≤ t) :
    incrementSquareError s t =ᵐ[gaussianProduct] fun ω =>
      (GaussianTimeProcess.process t ω - GaussianTimeProcess.process s ω) ^ 2 - ((t : ℝ) - s) := by
  filter_upwards [centeredSquare_coeFn (incrementDirection s t),
    GaussianTimeProcess.process_increment_ae s t hst] with ω hc hi
  change firstChaosEmbedding (incrementDirection s t) ω = _ at hi
  change incrementSquareError s t ω = _ at hc
  rw [hc, hi, incrementDirection_norm_sq s t hst]

theorem incrementSquareError_norm_sq (s t : ℝ≥0) (hst : s ≤ t) :
    ‖incrementSquareError s t‖ ^ 2 = 2 * ((t : ℝ) - s) ^ 2 := by
  rw [incrementSquareError, centeredSquare_norm_sq, incrementDirection_norm_sq s t hst]

end OperatorDerivativeRewrite.Foundation.GaussianQuadraticIncrement
