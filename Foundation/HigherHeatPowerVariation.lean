import Foundation.HigherHeatCoordinatePolynomials

/-! Actual finite-grid signed power moments for biharmonic increments. -/
noncomputable section
open MeasureTheory Polynomial Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPowerVariation
open HigherHeatSignedLaws HigherHeatPolynomialRealization HigherHeatCoordinatePolynomials

variable {ι : Type*} [Fintype ι]

def moment (t : ℝ≥0) (ht : 0 < t) (p : ℕ) : ℂ :=
  (kernelExpectation 2 (by norm_num) t ht (X^p) : ℂ)

def powerSum (p : ℕ) (x : ι → ℝ) : ℂ := ∑ i, (x i : ℂ)^p

theorem moment_eq_integral (t : ℝ≥0) (ht : 0 < t) (p : ℕ) :
    moment t ht p = ((∫ x : ℝ, x^p * realKernel 2 (by norm_num) t ht x : ℝ) : ℂ) := by
  simp only [moment, kernelExpectation, LinearMap.coe_mk, AddHom.coe_mk, eval_pow, eval_X]

theorem moment_two (t : ℝ≥0) (ht : 0 < t) : moment t ht 2 = 0 := by
  rw [moment_eq_integral, actual_off_order 2 (by norm_num) t ht 2 (by norm_num), Complex.ofReal_zero]

theorem moment_four (t : ℝ≥0) (ht : 0 < t) : moment t ht 4 = -24*(t : ℝ) := by
  rw [moment_eq_integral, biharmonic_fourth_moment]
  push_cast
  ring

theorem moment_eight (t : ℝ≥0) (ht : 0 < t) : moment t ht 8 = 20160*(t : ℝ)^2 := by
  rw [moment_eq_integral, biharmonic_eighth_moment]
  push_cast
  ring

variable [DecidableEq ι] (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)

theorem power_integrable (p : ℕ) (i : ι) :
    (incrementLaw 2 (by norm_num) t ht).Integrable (fun x => (x i : ℂ)^p) := by
  have he : (fun x : ι → ℝ => ((((X^p : Polynomial ℝ).eval (x i)) : ℝ) : ℂ)) =
      (fun x => (x i : ℂ)^p) := by funext x; simp
  rw [← he]
  exact coordinate_integrable 2 (by norm_num) t ht i (X^p)

theorem power_integral (p : ℕ) (i : ι) :
    (∫ᵛ x, (x i : ℂ)^p ∂<•incrementLaw 2 (by norm_num) t ht) = moment (t i) (ht i) p := by
  simpa only [eval_pow, eval_X, Complex.ofReal_pow, moment] using
    coordinate_integral 2 (by norm_num) t ht i (X^p)

theorem pair_integrable (p q : ℕ) (i j : ι) :
    (incrementLaw 2 (by norm_num) t ht).Integrable
      (fun x => (x i : ℂ)^p * (x j : ℂ)^q) := by
  have he : (fun x : ι → ℝ => ((((X^p : Polynomial ℝ).eval (x i)) : ℝ) : ℂ) *
      ((((X^q : Polynomial ℝ).eval (x j)) : ℝ) : ℂ)) =
      (fun x => (x i : ℂ)^p * (x j : ℂ)^q) := by funext x; simp
  rw [← he]
  exact mixed_integrable 2 (by norm_num) t ht i j (X^p) (X^q)

theorem pair_integral (p q : ℕ) (i j : ι) :
    (∫ᵛ x, (x i : ℂ)^p * (x j : ℂ)^q ∂<•incrementLaw 2 (by norm_num) t ht) =
      if i = j then moment (t i) (ht i) (p+q)
      else moment (t i) (ht i) p * moment (t j) (ht j) q := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [ite_true, ← pow_add]
    exact power_integral t ht (p+q) i
  · rw [if_neg hij]
    simpa only [eval_pow, eval_X, Complex.ofReal_pow, moment] using
      mixed_integral 2 (by norm_num) t ht i j hij (X^p) (X^q)

theorem sum_integrable (p : ℕ) :
    (incrementLaw 2 (by norm_num) t ht).Integrable (powerSum p) := by
  unfold powerSum
  unfold VectorMeasure.Integrable
  exact integrable_finsetSum Finset.univ (fun i _ => power_integrable t ht p i)

theorem sum_integral (p : ℕ) :
    (∫ᵛ x, powerSum p x ∂<•incrementLaw 2 (by norm_num) t ht) =
      ∑ i, moment (t i) (ht i) p := by
  unfold powerSum
  rw [VectorMeasure.integral_finsetSum Finset.univ (fun i _ => power_integrable t ht p i)]
  simp_rw [power_integral]

theorem square_sum_integral (p : ℕ) :
    (∫ᵛ x, (powerSum p x)^2 ∂<•incrementLaw 2 (by norm_num) t ht) =
      ∑ i, ∑ j, if i = j then moment (t i) (ht i) (p+p)
        else moment (t i) (ht i) p * moment (t j) (ht j) p := by
  have he : (fun x : ι → ℝ => (powerSum p x)^2) =
      (fun x => ∑ i, ∑ j, (x i : ℂ)^p * (x j : ℂ)^p) := by
    funext x
    simp only [powerSum, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he]
  rw [VectorMeasure.integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => pair_integrable t ht p p i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [VectorMeasure.integral_finsetSum Finset.univ (fun j _ => pair_integrable t ht p p i j)]
  simp_rw [pair_integral]

theorem quadratic_sum_second_moment :
    (∫ᵛ x, (powerSum 2 x)^2 ∂<•incrementLaw 2 (by norm_num) t ht) =
      -24 * ∑ i, (t i : ℝ) := by
  classical
  rw [square_sum_integral]
  simp only [show 2+2=4 from rfl, moment_four, moment_two, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Complex.ofReal_sum, Finset.mul_sum]

theorem quartic_sum_mean :
    (∫ᵛ x, powerSum 4 x ∂<•incrementLaw 2 (by norm_num) t ht) =
      -24 * ∑ i, (t i : ℝ) := by
  rw [sum_integral]
  simp only [moment_four]
  rw [Complex.ofReal_sum, Finset.mul_sum]

end OperatorDerivativeRewrite.Foundation.HigherHeatPowerVariation
