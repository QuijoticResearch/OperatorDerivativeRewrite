import Foundation.GaussianHermiteTimeKernel

/-! Deterministic C¹ weights in the genuine Hermite stochastic integral.
The field is built in the original predictable space and then identified by its time slices. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianWeightedTimeHermite
open InfiniteGaussian GaussianTimeSpaceHermite GaussianHermiteStochasticSums
open GaussianHermiteRepresentation GaussianHermiteIntegrand GaussianHermiteTimeIntegral
open GaussianHermiteTimeKernel GaussianPredictableFull GaussianTimeProductL2 GaussianProductDerivative
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

def weightedIntegrand (a q : ℝ → ℝ) (n : ℕ) (T : ℝ≥0) : fullPredictable :=
  a T • hermiteIntegrand n T - integratedHermite q n T

theorem weightedIntegrand_slices (a q : ℝ → ℝ) (hq : Continuous q)
    (haq : ∀ t, HasDerivAt a (q t) t) (n : ℕ) (T : ℝ≥0) :
    scalarCurry (weightedIntegrand a q n T : TimeProbabilityL2) =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (fun x => a x • (brownianCore x.toNNReal n : GaussianL2)) := by
  have ha : Continuous a := continuous_iff_continuousAt.mpr (fun t => (haq t).continuousAt)
  change scalarCurry (a T • (hermiteIntegrand n T : TimeProbabilityL2) -
    (integratedHermite q n T : TimeProbabilityL2)) =ᵐ[volume] _
  rw [map_sub, map_smul, integratedHermite_slices a q ha hq haq]
  filter_upwards [Lp.coeFn_sub (a T • scalarCurry (hermiteIntegrand n T)) (tailField a ha n T),
    Lp.coeFn_smul (a T) (scalarCurry (hermiteIntegrand n T)),
    hermiteIntegrand_slices n T, tailField_coeFn a ha n T] with x hsub hsm hh ht
  rw [hsub]
  simp only [Pi.sub_apply, hsm, Pi.smul_apply, hh, ht, horizonValue]
  by_cases hx : x ∈ Ioc 0 (T : ℝ)
  · simp only [indicator_of_mem hx]
    module
  · simp [hx]

/-- Time-dependent Hermite Itô identity, obtained by proved stochastic Fubini.
No classical Itô formula or PRP is used in this calculation. -/
theorem weighted_hermite_identity (a q : ℝ → ℝ) (hq : Continuous q)
    (n : ℕ) (T : ℝ≥0) :
    a T • (brownianCore T (n + 1) : GaussianL2) =
      (n + 1 : ℝ) • itoIntegral (weightedIntegrand a q n T) +
        ∫ t in 0..(T : ℝ), q t • (brownianCore t.toNNReal (n + 1) : GaussianL2) := by
  change _ = (n + 1 : ℝ) • itoIntegral
    (a T • hermiteIntegrand n T - integratedHermite q n T) + _
  rw [map_sub, map_smul, integral_hermiteIntegrand, integral_integratedHermite q hq]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  simp only [smul_sub, smul_smul]
  rw [mul_left_comm (n + 1 : ℝ) (a T) _, mul_inv_cancel₀ hn, mul_one,
    one_smul, sub_add_cancel]

/-- The actual deterministic-weighted field is square integrable on time times probability. -/
theorem weightedIntegrand_integrable_sq (a q : ℝ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Integrable (fun z => ((weightedIntegrand a q n T : TimeProbabilityL2) z) ^ 2)
      timeProbability := (Lp.memLp _).integrable_sq

/-- A single predictable field has both the prescribed running coefficient and the
stochastic identity. Here the coefficient derivative is the actual Mathlib derivative. -/
theorem weighted_hermite_ito (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a) (n : ℕ) (T : ℝ≥0) :
    ∃ U : fullPredictable,
      (scalarCurry (U : TimeProbabilityL2) =ᵐ[volume]
        (Ioc 0 (T : ℝ)).indicator (fun x => a x • (brownianCore x.toNNReal n : GaussianL2))) ∧
      a T • (brownianCore T (n + 1) : GaussianL2) =
        (n + 1 : ℝ) • itoIntegral U +
          ∫ t in 0..(T : ℝ), deriv a t • (brownianCore t.toNNReal (n + 1) : GaussianL2) := by
  refine ⟨weightedIntegrand a (deriv a) n T, ?_, weighted_hermite_identity a (deriv a)
    (ha.continuous_deriv (by simp)) n T⟩
  exact weightedIntegrand_slices a (deriv a) (ha.continuous_deriv (by simp))
    (fun t => (ha.differentiable (by simp) t).hasDerivAt) n T

end OperatorDerivativeRewrite.Foundation.GaussianWeightedTimeHermite
