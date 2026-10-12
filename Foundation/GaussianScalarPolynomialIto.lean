import Foundation.GaussianPolynomialIto
import Foundation.GaussianPolynomialDifferentiation

/-! Standard univariate polynomial Itô, including the exact factor 1/2 and B_0=0.
Drift integrals are genuine Bochner integrals in scalar Gaussian L². -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set MvPolynomial
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianScalarPolynomialIto
open InfiniteGaussian GaussianPolynomialHeat GaussianPolynomialProcess GaussianPolynomialIto
open GaussianPolynomialDifferentiation GaussianPredictableFull GaussianTimeProductL2
open GaussianProductDerivative GaussianTimeProcess

def polynomialValue (T : ℝ≥0) (p : Polynomial ℝ) : GaussianL2 :=
  valueL2 T (spatialPolynomial p)

theorem polynomialValue_coeFn (T : ℝ≥0) (p : Polynomial ℝ) :
    polynomialValue T p =ᵐ[gaussianProduct] fun ω => p.eval (process T ω) := by
  filter_upwards [valueL2_coeFn T (spatialPolynomial p)] with ω hω
  exact hω.trans (spatialPolynomial_eval p T (process T ω))

theorem polynomialValue_zero (p : Polynomial ℝ) :
    polynomialValue 0 p = p.eval 0 • gaussianOne := by
  apply Lp.ext
  filter_upwards [polynomialValue_coeFn 0 p, process_zero_ae,
    Lp.coeFn_smul (p.eval 0) gaussianOne, gaussianOne_coeFn] with ω hp hz hs h1
  simp only [hp, hz, hs, Pi.smul_apply, h1, smul_eq_mul, mul_one]

theorem polynomialValue_intervalIntegrable (p : Polynomial ℝ) (T : ℝ≥0) :
    IntervalIntegrable (fun t => polynomialValue t.toNNReal p) volume 0 T :=
  valueL2_intervalIntegrable (spatialPolynomial p) T

/-- No growth assumptions are added: all univariate real polynomials are included.
The ONE actual predictable U has slice p'(B_t) and the asserted stochastic identity. -/
theorem scalar_polynomial_ito (p : Polynomial ℝ) (T : ℝ≥0) :
    ∃! U : fullPredictable,
      (scalarCurry (U : TimeProbabilityL2) =ᵐ[volume]
        (Ioc 0 (T : ℝ)).indicator (fun t => polynomialValue t.toNNReal p.derivative)) ∧
      polynomialValue T p - p.eval 0 • gaussianOne = itoIntegral U +
        (1 / 2 : ℝ) • ∫ t in 0..(T : ℝ), polynomialValue t.toNNReal p.derivative.derivative := by
  obtain ⟨U, hU, _⟩ := polynomial_ito T (spatialPolynomial p)
  have hUs : scalarCurry (U : TimeProbabilityL2) =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (fun t => polynomialValue t.toNNReal p.derivative) := by
    rw [hU.1]
    simpa only [spatialPolynomial_spatial, polynomialValue] using
      spatialField_coeFn T (spatialPolynomial p)
  have hUi : polynomialValue T p - p.eval 0 • gaussianOne = itoIntegral U +
      (1 / 2 : ℝ) • ∫ t in 0..(T : ℝ), polynomialValue t.toNNReal p.derivative.derivative := by
    have hi := hU.2
    simp only [spatialPolynomial_heat, map_smul, intervalIntegral.integral_smul] at hi
    change polynomialValue T p - polynomialValue 0 p = _ at hi
    rwa [polynomialValue_zero] at hi
  refine ⟨U, ⟨hUs, hUi⟩, ?_⟩
  intro V hV
  apply Subtype.ext
  exact scalarCurry.injective (Lp.ext (hV.1.trans hUs.symm))

end OperatorDerivativeRewrite.Foundation.GaussianScalarPolynomialIto
