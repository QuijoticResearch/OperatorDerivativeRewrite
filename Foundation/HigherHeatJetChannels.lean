import Foundation.HigherHeatCoordinatePolynomials

/-! Actual intermediate power-channel pairings under finite signed higher-heat laws. -/
noncomputable section
open MeasureTheory Polynomial
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatJetChannels
open HigherHeatSignedLaws HigherHeatPolynomialRealization HigherHeatCoordinatePolynomials

variable {ι : Type*} [Fintype ι]

def powerSum (r : ℕ) (x : ι → ℝ) : ℂ := ∑ i, (x i : ℂ)^r

def cumulant (m : ℕ) : ℂ := ((2 * m).factorial: ℂ)*(-1: ℂ)^(m + 1)

theorem low_moment_zero (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (r : ℕ) (hr : 0 < r) (hrp : r < 2 * m) : kernelExpectation m hm t ht (X^r) = 0 := by
  rw [kernelExpectation_eq_moments, PseudoPolynomialStein.expectation_X_pow]
  apply PseudoPolynomialStein.moment_off_order (2 * m) (by omega)
  intro h
  have := Nat.le_of_dvd hr h
  omega

theorem middle_moment (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (d : ℕ) (hd : 0 < d) (hdp : d < 4 * m) :
    (kernelExpectation m hm t ht (X^d): ℂ) =
      if d = 2 * m then cumulant m * (t: ℝ) else 0 := by
  rw [kernelExpectation_eq_moments, PseudoPolynomialStein.expectation_X_pow]
  by_cases he : d = 2 * m
  · subst d
    rw [PseudoPolynomialStein.moment_leading (2 * m) (by omega)]
    simp only [ite_true, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
      Complex.ofReal_one, Complex.ofReal_natCast, cumulant]
    ring
  · have hnot : ¬ 2 * m ∣ d := by
      rintro ⟨k,hk⟩
      have hk0 : 0 < k := by nlinarith
      have hk2 : k < 2 := by nlinarith
      have hk1 : k = 1 := by omega
      simp only [hk1, mul_one] at hk
      exact he hk
    rw [PseudoPolynomialStein.moment_off_order (2 * m) (by omega) _ d hnot]
    simp [he]

theorem cell_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (r s : ℕ) (i j : ι) : (incrementLaw m hm t ht).Integrable
      (fun x => (x i: ℂ)^r * (x j: ℂ)^s) := by
  simpa only [eval_pow, eval_X, Complex.ofReal_pow] using
    mixed_integrable m hm t ht i j (X^r) (X^s)

open Classical in
theorem cell_pairing (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (r s : ℕ) (hr : 0 < r) (hrp : r < 2 * m) (hs : 0 < s) (hsp : s < 2 * m) (i j : ι) :
    (∫ᵛ x, (x i: ℂ)^r * (x j: ℂ)^s ∂<•incrementLaw m hm t ht) =
      if i = j ∧ r + s = 2 * m then cumulant m * (t i : ℝ) else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [← pow_add]
    have he := coordinate_integral m hm t ht i (X^(r + s))
    simp only [eval_pow, eval_X, Complex.ofReal_pow] at he
    rw [he, middle_moment m hm (t i) (ht i) (r + s) (by omega) (by omega)]
    simp
  · have he := mixed_integral m hm t ht i j hij (X^r) (X^s)
    simp only [eval_pow, eval_X, Complex.ofReal_pow] at he
    rw [he, low_moment_zero m hm _ _ r hr hrp, low_moment_zero m hm _ _ s hs hsp]
    simp [hij]

theorem cross_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (r s : ℕ) : (incrementLaw m hm t ht).Integrable
      (fun x => powerSum r x * powerSum s x) := by
  have he : (fun x : ι → ℝ => powerSum r x * powerSum s x) =
      (fun x => ∑ i, ∑ j, (x i: ℂ)^r * (x j: ℂ)^s) := by
    funext x
    simp only [powerSum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => cell_integrable m hm t ht r s i j))

theorem cross_pairing (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (r s : ℕ) (hr : 0 < r) (hrp : r < 2 * m) (hs : 0 < s) (hsp : s < 2 * m) :
    (∫ᵛ x, powerSum r x * powerSum s x ∂<•incrementLaw m hm t ht) =
      if r + s = 2 * m then cumulant m * (((∑ i, (t i : ℝ)): ℝ): ℂ) else 0 := by
  classical
  have he : (fun x : ι → ℝ => powerSum r x * powerSum s x) =
      (fun x => ∑ i, ∑ j, (x i: ℂ)^r * (x j: ℂ)^s) := by
    funext x
    simp only [powerSum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he, VectorMeasure.integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => cell_integrable m hm t ht r s i j))]
  have hj (i : ι) : (∫ᵛ x, (∑ j, (x i: ℂ)^r * (x j: ℂ)^s) ∂<•incrementLaw m hm t ht) =
      ∑ j, if i = j ∧ r + s = 2 * m then cumulant m * (t i : ℝ) else 0 := by
    rw [VectorMeasure.integral_finsetSum Finset.univ (fun j _ => cell_integrable m hm t ht r s i j)]
    simp_rw [cell_pairing m hm t ht r s hr hrp hs hsp]
  simp_rw [hj]
  by_cases h : r + s = 2 * m
  · simp only [h, and_true, ite_true, Finset.sum_ite_eq, Finset.mem_univ]
    rw [Complex.ofReal_sum, Finset.mul_sum]
  · simp [h]


theorem powerSum_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (r : ℕ) : (incrementLaw m hm t ht).Integrable (powerSum r) := by
  have hi (i : ι) : (incrementLaw m hm t ht).Integrable (fun x => (x i: ℂ)^r) := by
    simpa only [eval_pow, eval_X, Complex.ofReal_pow] using
      coordinate_integrable m hm t ht i (X^r)
  exact integrable_finsetSum Finset.univ (fun i _ => hi i)

theorem powerSum_mean_zero (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (r : ℕ) (hr : 0 < r) (hrp : r < 2 * m) :
    (∫ᵛ x, powerSum r x ∂<•incrementLaw m hm t ht) = 0 := by
  have hi (i : ι) : (incrementLaw m hm t ht).Integrable (fun x => (x i: ℂ)^r) := by
    simpa only [eval_pow, eval_X, Complex.ofReal_pow] using
      coordinate_integrable m hm t ht i (X^r)
  have he (i : ι) : (∫ᵛ x, (x i: ℂ)^r ∂<•incrementLaw m hm t ht) = 0 := by
    have h := coordinate_integral m hm t ht i (X^r)
    rw [low_moment_zero m hm _ _ r hr hrp] at h
    simpa only [eval_pow, eval_X, Complex.ofReal_pow, Complex.ofReal_zero] using h
  simp only [powerSum]
  rw [VectorMeasure.integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [he, Finset.sum_const_zero]

end OperatorDerivativeRewrite.Foundation.HigherHeatJetChannels
