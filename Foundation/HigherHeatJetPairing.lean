import Foundation.HigherHeatJetChannels
import Mathlib.Data.Fin.Rev

/-! A nondegenerate finite signed jet pairing, distinct from positive Hermitian energy. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatJetPairing
open HigherHeatSignedLaws HigherHeatJetChannels

variable {ι : Type*} [Fintype ι]

def kernel (m : ℕ) (u : Fin (2 * m - 1) → ℝ) (x : ι → ℝ) : ℂ :=
  ∑ r, u r • powerSum (r.val + 1) x

theorem complement_iff (m : ℕ) (r j : Fin (2 * m - 1)) :
    (j.val + 1)+(r.rev.val + 1)=2 * m ↔ j = r := by
  have hr := r.is_lt
  have hj := j.is_lt
  rw [Fin.val_rev]
  constructor
  · intro h
    apply Fin.ext
    omega
  · intro h
    subst j
    omega

theorem kernel_probe_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (u : Fin (2 * m - 1) → ℝ) (r : Fin (2 * m - 1)) :
    (incrementLaw m hm t ht).Integrable
      (fun x => kernel m u x * powerSum (r.rev.val + 1) x) := by
  simp only [kernel, Finset.sum_mul, smul_mul_assoc]
  exact integrable_finsetSum Finset.univ (fun j _ =>
    (cross_integrable m hm t ht (j.val + 1) (r.rev.val + 1)).smul (u j))

theorem coefficient_integral (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (u : Fin (2 * m - 1) → ℝ) (r : Fin (2 * m - 1)) :
    (∫ᵛ x, kernel m u x * powerSum (r.rev.val + 1) x ∂<•incrementLaw m hm t ht) =
      (cumulant m * (((∑ i, (t i : ℝ)): ℝ): ℂ)) * (u r: ℂ) := by
  simp only [kernel, Finset.sum_mul, smul_mul_assoc]
  have hi (j : Fin (2 * m - 1)) : (incrementLaw m hm t ht).Integrable
      (fun x => u j • (powerSum (j.val + 1) x * powerSum (r.rev.val + 1) x)) :=
    (cross_integrable m hm t ht (j.val + 1) (r.rev.val + 1)).smul (u j)
  rw [VectorMeasure.integral_finsetSum Finset.univ (fun j _ => hi j)]
  have he (j : Fin (2 * m - 1)) :
      (∫ᵛ x, u j • (powerSum (j.val + 1) x * powerSum (r.rev.val + 1) x)
        ∂<•incrementLaw m hm t ht) =
      if j = r then u r • (cumulant m * (((∑ i, (t i : ℝ)): ℝ): ℂ)) else 0 := by
    rw [VectorMeasure.integral_fun_smul,
      cross_pairing m hm t ht (j.val + 1) (r.rev.val + 1) (by omega)
        (by have := j.is_lt; omega) (by omega) (by have := r.rev.is_lt; omega)]
    simp only [complement_iff]
    by_cases hj : j = r
    · subst j; simp
    · simp [hj]
  simp_rw [he]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Complex.real_smul]
  ring

theorem cumulant_ne_zero (m : ℕ) : cumulant m ≠ 0 := by
  unfold cumulant
  exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (2 * m))
    (pow_ne_zero _ (by norm_num))

theorem coefficients_separated (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (hT : (∑ i, (t i : ℝ)) ≠ 0) (u : Fin (2 * m - 1) → ℝ)
    (h : ∀ r : Fin (2 * m - 1), (∫ᵛ x, kernel m u x * powerSum (r.rev.val + 1) x
      ∂<•incrementLaw m hm t ht) = 0) : u = 0 := by
  funext r
  have he := h r
  rw [coefficient_integral] at he
  have hC : cumulant m * (((∑ i, (t i : ℝ)): ℝ): ℂ) ≠ 0 :=
    mul_ne_zero (cumulant_ne_zero m) (Complex.ofReal_ne_zero.mpr hT)
  have hu : (u r: ℂ)=0 := (mul_eq_zero.mp he).resolve_left hC
  exact Complex.ofReal_injective hu

theorem zero_kernel_unique (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (hT : (∑ i, (t i : ℝ)) ≠ 0) (u : Fin (2 * m - 1) → ℝ)
    (h : ∀ x : ι → ℝ, kernel m u x = 0) : u = 0 := by
  apply coefficients_separated m hm t ht hT u
  intro r
  simp only [h, zero_mul, VectorMeasure.integral_zero]


theorem ae_zero_kernel_unique (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (hT : (∑ i, (t i : ℝ)) ≠ 0) (u : Fin (2 * m - 1) → ℝ)
    (h : kernel m u =ᵐ[(incrementLaw m hm t ht).variation] 0) : u = 0 := by
  apply coefficients_separated m hm t ht hT u
  intro r
  have he : (fun x => kernel m u x * powerSum (r.rev.val + 1) x) =ᵐ[
      (incrementLaw m hm t ht).variation] (fun _ => (0: ℂ)) := by
    filter_upwards [h] with x hx
    change kernel m u x = 0 at hx
    rw [hx, zero_mul]
  rw [VectorMeasure.integral_congr_ae he, VectorMeasure.integral_zero]


theorem bilinear_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (u v : Fin (2 * m - 1) → ℝ) : (incrementLaw m hm t ht).Integrable
      (fun x => kernel m u x * kernel m v x) := by
  have he : (fun x : ι → ℝ => kernel m u x * kernel m v x) =
      (fun x => ∑ r, v r • (kernel m u x * powerSum (r.val + 1) x)) := by
    funext x
    simp only [kernel, Finset.mul_sum, mul_smul_comm]
  rw [he]
  apply integrable_finsetSum Finset.univ
  intro r _
  have hi := kernel_probe_integrable m hm t ht u r.rev
  simpa only [Fin.rev_rev] using VectorMeasure.Integrable.fun_smul (v r) hi

theorem bilinear_energy (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (u v : Fin (2 * m - 1) → ℝ) :
    (∫ᵛ x, kernel m u x * kernel m v x ∂<•incrementLaw m hm t ht) =
      (cumulant m * (((∑ i, (t i : ℝ)): ℝ): ℂ)) * (((∑ r, v r*u r.rev): ℝ): ℂ) := by
  have he : (fun x : ι → ℝ => kernel m u x * kernel m v x) =
      (fun x => ∑ r, v r • (kernel m u x * powerSum (r.val + 1) x)) := by
    funext x
    simp only [kernel, Finset.mul_sum, mul_smul_comm]
  have hi (r : Fin (2 * m - 1)) : (incrementLaw m hm t ht).Integrable
      (fun x => v r • (kernel m u x * powerSum (r.val + 1) x)) := by
    have hh := kernel_probe_integrable m hm t ht u r.rev
    simpa only [Fin.rev_rev] using VectorMeasure.Integrable.fun_smul (v r) hh
  rw [he, VectorMeasure.integral_finsetSum Finset.univ (fun r _ => hi r)]
  have hj (r : Fin (2 * m - 1)) :
      (∫ᵛ x, v r • (kernel m u x * powerSum (r.val + 1) x) ∂<•incrementLaw m hm t ht) =
      (cumulant m * (((∑ i, (t i : ℝ)): ℝ): ℂ)) * ((v r*u r.rev: ℝ): ℂ) := by
    rw [VectorMeasure.integral_fun_smul]
    have hh := coefficient_integral m hm t ht u r.rev
    simp only [Fin.rev_rev] at hh
    rw [hh]
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring
  simp_rw [hj]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum]


theorem kernel_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (u : Fin (2 * m - 1) → ℝ) : (incrementLaw m hm t ht).Integrable (kernel m u) := by
  exact integrable_finsetSum Finset.univ (fun r _ =>
    VectorMeasure.Integrable.fun_smul (u r) (powerSum_integrable m hm t ht (r.val + 1)))

theorem kernel_mean_zero (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (u : Fin (2 * m - 1) → ℝ) :
    (∫ᵛ x, kernel m u x ∂<•incrementLaw m hm t ht) = 0 := by
  simp only [kernel]
  rw [VectorMeasure.integral_finsetSum Finset.univ (fun r _ =>
    VectorMeasure.Integrable.fun_smul (u r) (powerSum_integrable m hm t ht (r.val + 1)))]
  apply Finset.sum_eq_zero
  intro r _
  rw [VectorMeasure.integral_fun_smul,
    powerSum_mean_zero m hm t ht (r.val + 1) (by omega) (by have := r.is_lt; omega), smul_zero]

end OperatorDerivativeRewrite.Foundation.HigherHeatJetPairing
