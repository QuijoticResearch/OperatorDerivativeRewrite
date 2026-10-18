import Foundation.HigherHeatJetPairing

/-! Finite chronological monomials have zero same-order Gram form but admit
higher-power coefficient probes under the actual signed increment laws. -/
noncomputable section
open MeasureTheory Polynomial
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatChronologicalProbes
open HigherHeatSignedLaws HigherHeatPolynomialRealization HigherHeatProductPolynomials
  HigherHeatJetChannels HigherHeatJetPairing
variable {ι : Type*} [Fintype ι]

def powers (d : ι → ℕ) (x : ι → ℝ) : ℂ := ∏ i, (x i : ℂ) ^ d i

theorem powers_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (d : ι → ℕ) :
    (incrementLaw m hm t ht).Integrable (powers d) := by
  have he : observable (fun i => (X : Polynomial ℝ) ^ d i) = powers d := by
    funext x
    simp [observable, powers]
  rw [← he]
  exact product_signed_integrable m hm t ht _

theorem powers_integral (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (d : ι → ℕ) :
    (∫ᵛ x, powers d x ∂<•incrementLaw m hm t ht) =
      ∏ i, (kernelExpectation m hm (t i) (ht i) (X ^ d i) : ℂ) := by
  simpa only [observable, eval_pow, eval_X, Complex.ofReal_pow, powers] using
    product_signed_integral m hm t ht (fun i => X ^ d i)

theorem powers_mul (d e : ι → ℕ) (x : ι → ℝ) :
    powers d x * powers e x = powers (fun i => d i + e i) x := by
  simp [powers, pow_add, Finset.prod_mul_distrib]

open Classical in
def exponent (I : Finset ι) (r : ℕ) (i : ι) : ℕ := if i ∈ I then r else 0

def monomial (I : Finset ι) (x : ι → ℝ) : ℂ := powers (exponent I 1) x

def probe (m : ℕ) (I : Finset ι) (x : ι → ℝ) : ℂ := powers (exponent I (2*m-1)) x

theorem product_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (I J : Finset ι) (r s : ℕ) :
    (incrementLaw m hm t ht).Integrable
      (fun x => powers (exponent I r) x * powers (exponent J s) x) := by
  simp_rw [powers_mul]
  exact powers_integrable m hm t ht _

theorem gram_zero (m : ℕ) (hm : 2 ≤ m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (I J : Finset ι) (hI : I.Nonempty) :
    (∫ᵛ x, monomial I x * monomial J x ∂<•incrementLaw m (by omega) t ht) = 0 := by
  classical
  simp only [monomial, powers_mul, powers_integral]
  obtain ⟨i, hi⟩ := hI
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hd : 0 < exponent I 1 i + exponent J 1 i := by simp [exponent, hi]
  have hb : exponent I 1 i + exponent J 1 i < 2*m := by
    by_cases hj : i ∈ J <;> simp [exponent, hi, hj] <;> omega
  rw [low_moment_zero m (by omega) _ _ _ hd hb]
  rfl

open Classical in
theorem dual_pairing (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (I J : Finset ι) :
    (∫ᵛ x, monomial J x * probe m I x ∂<•incrementLaw m hm t ht) =
      if J = I then ∏ i ∈ I, cumulant m * (t i : ℝ) else 0 := by
  classical
  simp only [monomial, probe, powers_mul, powers_integral]
  by_cases he : J = I
  · subst J
    simp only [ite_true]
    have hf (i : ι) :
        (kernelExpectation m hm (t i) (ht i)
          (X ^ (exponent I 1 i + exponent I (2*m-1) i)) : ℂ) =
          if i ∈ I then cumulant m * (t i : ℝ) else 1 := by
      by_cases hi : i ∈ I
      · have hn : exponent I 1 i + exponent I (2*m-1) i = 2*m := by
          simp [exponent, hi]; omega
        rw [hn, middle_moment m hm _ _ _ (by omega) (by omega)]
        simp [hi]
      · simp [exponent, hi, kernelExpectation_one]
    simp_rw [hf]
    exact Finset.prod_ite_mem_eq I _
  · simp only [he, ite_false]
    have hex : ∃ i, (i ∈ J ∧ i ∉ I) ∨ (i ∈ I ∧ i ∉ J) := by
      by_contra hn
      apply he
      ext i
      have hh := not_exists.mp hn i
      tauto
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hd : 0 < exponent J 1 i + exponent I (2*m-1) i := by
      rcases hi with ⟨hj, hi⟩ | ⟨hi, hj⟩ <;> simp [exponent, hi, hj] <;> omega
    have hb : exponent J 1 i + exponent I (2*m-1) i < 2*m := by
      rcases hi with ⟨hj, hi⟩ | ⟨hi, hj⟩ <;> simp [exponent, hi, hj] <;> omega
    rw [low_moment_zero m hm _ _ _ hd hb]
    rfl


def chronological (A : Finset (Finset ι)) (c : Finset ι → ℝ) (x : ι → ℝ) : ℂ :=
  ∑ I ∈ A, c I • monomial I x

theorem chronological_probe_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (A : Finset (Finset ι)) (c : Finset ι → ℝ) (I : Finset ι) :
    (incrementLaw m hm t ht).Integrable
      (fun x => chronological A c x * probe m I x) := by
  simp only [chronological, Finset.sum_mul, smul_mul_assoc]
  exact integrable_finsetSum A (fun J _ =>
    (product_integrable m hm t ht J I 1 (2*m-1)).smul (c J))

theorem coefficient_integral (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (A : Finset (Finset ι)) (c : Finset ι → ℝ)
    (I : Finset ι) (hI : I ∈ A) :
    (∫ᵛ x, chronological A c x * probe m I x ∂<•incrementLaw m hm t ht) =
      c I • (∏ i ∈ I, cumulant m * (t i : ℝ)) := by
  classical
  simp only [chronological, Finset.sum_mul, smul_mul_assoc]
  have hi (J : Finset ι) : (incrementLaw m hm t ht).Integrable
      (fun x => c J • (monomial J x * probe m I x)) :=
    (product_integrable m hm t ht J I 1 (2*m-1)).smul (c J)
  rw [VectorMeasure.integral_finsetSum A (fun J _ => hi J)]
  simp_rw [VectorMeasure.integral_fun_smul, dual_pairing]
  simp [hI]

omit [Fintype ι] in
theorem probe_factor_ne_zero (m : ℕ) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (I : Finset ι) : (∏ i ∈ I, cumulant m * (t i : ℝ)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact mul_ne_zero (cumulant_ne_zero m)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (ht i)))

theorem coefficients_separated (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (A : Finset (Finset ι)) (c : Finset ι → ℝ)
    (h : ∀ I ∈ A, (∫ᵛ x, chronological A c x * probe m I x
      ∂<•incrementLaw m hm t ht) = 0) : ∀ I ∈ A, c I = 0 := by
  intro I hI
  have he := h I hI
  rw [coefficient_integral m hm t ht A c I hI, Complex.real_smul] at he
  exact Complex.ofReal_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_right (probe_factor_ne_zero m t ht I))

theorem chronological_mul (A B : Finset (Finset ι)) (c d : Finset ι → ℝ)
    (x : ι → ℝ) : chronological A c x * chronological B d x =
      ∑ I ∈ A, ∑ J ∈ B, c I • (d J • (monomial I x * monomial J x)) := by
  change (∑ I ∈ A, c I • monomial I x) * (∑ J ∈ B, d J • monomial J x) = _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  simp only [smul_mul_assoc, mul_smul_comm]
  exact smul_comm _ _ _

theorem chronological_product_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (A B : Finset (Finset ι)) (c d : Finset ι → ℝ) :
    (incrementLaw m hm t ht).Integrable
      (fun x => chronological A c x * chronological B d x) := by
  simp_rw [chronological_mul]
  exact integrable_finsetSum A (fun I _ => integrable_finsetSum B (fun J _ =>
    ((product_integrable m hm t ht I J 1 1).smul (d J)).smul (c I)))

theorem chronological_gram_zero (m : ℕ) (hm : 2 ≤ m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (A B : Finset (Finset ι)) (c d : Finset ι → ℝ)
    (hA : ∀ I ∈ A, I.Nonempty) :
    (∫ᵛ x, chronological A c x * chronological B d x
      ∂<•incrementLaw m (by omega) t ht) = 0 := by
  simp_rw [chronological_mul]
  have hi (I J : Finset ι) : (incrementLaw m (by omega) t ht).Integrable
      (fun x => c I • (d J • (monomial I x * monomial J x))) :=
    ((product_integrable m (by omega) t ht I J 1 1).smul (d J)).smul (c I)
  rw [VectorMeasure.integral_finsetSum A (fun I _ =>
    integrable_finsetSum B (fun J _ => hi I J))]
  apply Finset.sum_eq_zero
  intro I hI
  rw [VectorMeasure.integral_finsetSum B (fun J _ => hi I J)]
  apply Finset.sum_eq_zero
  intro J _
  rw [VectorMeasure.integral_fun_smul, VectorMeasure.integral_fun_smul,
    gram_zero m hm t ht I J (hA I hI)]
  simp


theorem ae_zero_unique (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (A : Finset (Finset ι)) (c : Finset ι → ℝ)
    (h : chronological A c =ᵐ[(incrementLaw m hm t ht).variation] 0) :
    ∀ I ∈ A, c I = 0 := by
  apply coefficients_separated m hm t ht A c
  intro I _
  have he : (fun x => chronological A c x * probe m I x) =ᵐ[
      (incrementLaw m hm t ht).variation] (fun _ => (0 : ℂ)) := by
    filter_upwards [h] with x hx
    change chronological A c x = 0 at hx
    rw [hx, zero_mul]
  rw [VectorMeasure.integral_congr_ae he, VectorMeasure.integral_zero]

end OperatorDerivativeRewrite.Foundation.HigherHeatChronologicalProbes
