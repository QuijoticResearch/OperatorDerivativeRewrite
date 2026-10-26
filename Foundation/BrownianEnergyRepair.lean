import Foundation.BrownianCovariancePowers
import Mathlib.Analysis.SpecialFunctions.Exp
import Foundation.FiniteFourierTorusAverage
import Foundation.FiniteFourierReality

/-! Finite complex Fourier Gram energies with actual normalized torus averages.
The repaired summed bound uses phase-dependent Fourier tails. It does not assert
independent curvature-mode evolution or completed generator domains. -/
noncomputable section
open Finset
namespace OperatorDerivativeRewrite.Foundation.BrownianEnergyRepair.Coefficients
open OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers

theorem exp_tangent (x y : ℝ) :
    Real.exp x * (1 + y - x) ≤ Real.exp y := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y-x)) (Real.exp_nonneg x)
  rw [← Real.exp_add] at h
  convert h using 1 <;> congr 1 <;> ring

theorem sum_exp_lower (n : ℕ) (x : ℝ) (y : ℕ → ℝ)
    (h : ∑ j ∈ range n, y j = n*x) :
    n * Real.exp x ≤ ∑ j ∈ range n, Real.exp (y j) := by
  have hi := sum_le_sum (s := range n) (fun j _ => exp_tangent x (y j))
  have he : (∑ j ∈ range n, Real.exp x * (1 + y j - x)) = n * Real.exp x := by
    rw [← mul_sum]
    simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
    rw [h]
    ring
  rwa [he] at hi

theorem innovation_exp_lower (n : ℕ) (t : ℝ) :
    n * Real.exp (-2 * n * t) ≤
      ∑ j ∈ range n, Real.exp (-2 * innovation 2 j * t) := by
  apply sum_exp_lower
  calc
    (∑ j ∈ range n, -2 * innovation 2 j * t) =
        -2 * (∑ j ∈ range n, innovation 2 j) * t := by
      rw [← sum_mul, ← mul_sum]
    _ = n * (-2 * n * t) := by
      rw [innovation_sum 2 (by norm_num)]
      ring

theorem finite_weighted_energy_repair (N : ℕ) (t : ℝ) (w : ℕ → ℝ)
    (hw : ∀ n ∈ range N, 0 ≤ w n) :
    (∑ n ∈ range N, w n * ((n+1:ℕ):ℝ) * Real.exp (-2 * ((n+1:ℕ):ℝ) * t)) ≤
      ∑ n ∈ range N, w n *
        ∑ j ∈ range (n+1), Real.exp (-2 * innovation 2 j * t) := by
  apply sum_le_sum
  intro n hn
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (innovation_exp_lower (n+1) t) (hw n hn)

theorem triangular_sum (N : ℕ) (w e : ℕ → ℝ) :
    (∑ n ∈ range N, w n * ∑ j ∈ range (n+1), e j) =
      ∑ j ∈ range N, e j * ∑ n ∈ range N, if j ≤ n then w n else 0 := by
  calc
    _ = ∑ n ∈ range N, ∑ j ∈ range N, if j ≤ n then w n * e j else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [← prefix_sum e N (n+1) (by simpa using mem_range.mp hn), mul_sum]
      apply sum_congr rfl
      intro j hj
      by_cases h : j ≤ n
      · simp [h, show j < n+1 by omega]
      · simp [h, show ¬ j < n+1 by omega]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      by_cases h : j ≤ n <;> simp [h, mul_comm]

theorem tail_energy_repair (N : ℕ) (t : ℝ) (w : ℕ → ℝ)
    (hw : ∀ n ∈ range N, 0 ≤ w n) :
    (∑ n ∈ range N, w n * ((n+1:ℕ):ℝ) * Real.exp (-2 * ((n+1:ℕ):ℝ) * t)) ≤
      ∑ j ∈ range N, Real.exp (-2 * innovation 2 j * t) *
        ∑ n ∈ range N, if j ≤ n then w n else 0 := by
  rw [← triangular_sum]
  exact finite_weighted_energy_repair N t w hw

theorem innovation_exp_lower_fin {N : ℕ} (i : Fin N) (t : ℝ) :
    ((i.val+1:ℕ):ℝ) * Real.exp (-2 * ((i.val+1:ℕ):ℝ) * t) ≤
      ∑ j : Fin N, if j.val ≤ i.val then Real.exp (-2 * innovation 2 j.val * t) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    if j ≤ i.val then Real.exp (-2 * innovation 2 j * t) else 0)]
  simp only [show ∀ j : ℕ, j ≤ i.val ↔ j < i.val+1 by omega]
  rw [prefix_sum _ N (i.val+1) (by omega)]
  exact innovation_exp_lower (i.val+1) t

theorem finite_tail_energy_repair {N : ℕ} (t : ℝ) (w : Fin N → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * ((i.val+1:ℕ):ℝ) * Real.exp (-2 * ((i.val+1:ℕ):ℝ) * t)) ≤
      ∑ j : Fin N, Real.exp (-2 * innovation 2 j.val * t) *
        ∑ i : Fin N, if j.val ≤ i.val then w i else 0 := by
  calc
    _ ≤ ∑ i : Fin N, w i * ∑ j : Fin N,
        if j.val ≤ i.val then Real.exp (-2 * innovation 2 j.val * t) else 0 := by
      apply sum_le_sum
      intro i hi
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (innovation_exp_lower_fin i t) (hw i)
    _ = _ := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro i hi
      by_cases h : j.val ≤ i.val <;> simp [h, mul_comm]

end OperatorDerivativeRewrite.Foundation.BrownianEnergyRepair.Coefficients

noncomputable section
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.BrownianEnergyRepair.Torus
open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage

def axisWave (n : ℤ) : Wave := fun j => if j = 0 then n else 0

theorem axisWave_injective : Function.Injective axisWave := by
  intro n m h
  simpa [axisWave] using congrFun h 0

theorem character_pair_average (n m : ℤ) (c : ℂ) :
    boxAverage (fun x => c * character (axisWave n - axisWave m) x) =
      if n = m then c else 0 := by
  have h := boxAverage_synthesis
    (AddMonoidAlgebra.single (axisWave n - axisWave m) c)
  simp only [synthesis_single, constantTrace_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply] at h
  have he : axisWave n - axisWave m = 0 ↔ n = m := by
    rw [sub_eq_zero]
    exact axisWave_injective.eq_iff
  simpa only [he] using h

def gramPolynomial {N : ℕ} (C : Fin N → Fin N → ℂ) : Fourier :=
  ∑ i, ∑ j, AddMonoidAlgebra.single
    (axisWave (j.val : ℤ) - axisWave (i.val : ℤ)) (C i j)

theorem synthesis_gramPolynomial {N : ℕ} (C : Fin N → Fin N → ℂ) (x : Space) :
    synthesis x (gramPolynomial C) =
      ∑ i, ∑ j, C i j * character
        (axisWave (j.val : ℤ) - axisWave (i.val : ℤ)) x := by
  simp [gramPolynomial, map_sum, synthesis_single]

theorem gram_average {N : ℕ} (C : Fin N → Fin N → ℂ) :
    boxAverage (fun x => ∑ i, ∑ j, C i j * character
        (axisWave (j.val : ℤ) - axisWave (i.val : ℤ)) x) = ∑ i, C i i := by
  have h := boxAverage_synthesis (gramPolynomial C)
  rw [show (fun x => synthesis x (gramPolynomial C)) =
      (fun x => ∑ i, ∑ j, C i j * character
        (axisWave (j.val : ℤ) - axisWave (i.val : ℤ)) x) from
      funext (synthesis_gramPolynomial C)] at h
  rw [h]
  simp only [gramPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he (j : Fin N) : axisWave (j.val : ℤ) - axisWave (i.val : ℤ) = 0 ↔ j = i := by
    rw [sub_eq_zero, axisWave_injective.eq_iff]
    simp only [Nat.cast_inj, Fin.val_inj]
  simp only [constantTrace_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, he]
  simp

def gramEnergy {N : ℕ} (M : Fin N → Fin N → ℝ) (a : Fin N → ℂ) (x : Space) : ℂ :=
  ∑ i, ∑ j, ((M i j : ℂ) * (conj (a i) * a j)) * character
    (axisWave (j.val : ℤ) - axisWave (i.val : ℤ)) x

theorem gramEnergy_average {N : ℕ} (M : Fin N → Fin N → ℝ) (a : Fin N → ℂ) :
    boxAverage (gramEnergy M a) = ((∑ i, M i i * ‖a i‖^2 : ℝ) : ℂ) := by
  unfold gramEnergy
  rw [gram_average]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm (conj (a i)) (a i), Complex.mul_conj']

def brownianMatrix (N : ℕ) (i j : Fin N) : ℝ := (min i.val j.val + 1 : ℕ)

theorem brownianEnergy_average {N : ℕ} (a : Fin N → ℂ) :
    boxAverage (gramEnergy (brownianMatrix N) a) =
      ((∑ i, ((i.val+1:ℕ):ℝ) * ‖a i‖^2 : ℝ) : ℂ) := by
  rw [gramEnergy_average]
  simp [brownianMatrix]

def tailMatrix {N : ℕ} (r : ℕ) (i j : Fin N) : ℝ :=
  if r ≤ i.val ∧ r ≤ j.val then 1 else 0

theorem tailEnergy_average {N : ℕ} (r : ℕ) (a : Fin N → ℂ) :
    boxAverage (gramEnergy (tailMatrix r) a) =
      ((∑ i, if r ≤ i.val then ‖a i‖^2 else 0 : ℝ) : ℂ) := by
  rw [gramEnergy_average]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : r ≤ i.val <;> simp [tailMatrix, h]

def tailValue {N : ℕ} (r : ℕ) (a : Fin N → ℂ) (x : Space) : ℂ :=
  ∑ i, if r ≤ i.val then a i * character (axisWave (i.val : ℤ)) x else 0

theorem tailEnergy_square {N : ℕ} (r : ℕ) (a : Fin N → ℂ) (x : Space) :
    gramEnergy (tailMatrix r) a x = conj (tailValue r a x) * tailValue r a x := by
  unfold gramEnergy tailValue
  rw [map_sum]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hri : r ≤ i.val <;> by_cases hrj : r ≤ j.val
  · simp only [tailMatrix, hri, hrj, and_self, ite_true, Complex.ofReal_one, one_mul,
      map_mul, sub_eq_add_neg, character_add, FiniteFourierReality.character_neg]
    ring
  · simp [tailMatrix, hri, hrj]
  · simp [tailMatrix, hri, hrj]
  · simp [tailMatrix, hri, hrj]

end OperatorDerivativeRewrite.Foundation.BrownianEnergyRepair.Torus

namespace OperatorDerivativeRewrite.Foundation.BrownianEnergyRepair.Integrated
open OperatorDerivativeRewrite.Foundation
open FiniteFourierTorusAverage
open OperatorDerivativeRewrite.Foundation.BrownianEnergyRepair.Torus OperatorDerivativeRewrite.Foundation.BrownianEnergyRepair.Coefficients

def cauchyFlow {N : ℕ} (t : ℝ) (a : Fin N → ℂ) (i : Fin N) : ℂ :=
  (Real.exp (-((i.val+1:ℕ):ℝ)*t) : ℂ) * a i

theorem cauchyFlow_norm_sq {N : ℕ} (t : ℝ) (a : Fin N → ℂ) (i : Fin N) :
    ‖cauchyFlow t a i‖^2 = Real.exp (-2*((i.val+1:ℕ):ℝ)*t) * ‖a i‖^2 := by
  simp only [cauchyFlow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  rw [pow_two (Real.exp _), ← Real.exp_add]
  congr 2
  ring

theorem actual_integrated_energy_repair {N : ℕ} (t : ℝ) (a : Fin N → ℂ) :
    (boxAverage (gramEnergy (brownianMatrix N) (cauchyFlow t a))).re ≤
      ∑ j : Fin N, Real.exp (-2 * BrownianCovariancePowers.innovation 2 j.val * t) *
        (boxAverage (gramEnergy (tailMatrix j.val) a)).re := by
  rw [brownianEnergy_average]
  simp only [Complex.ofReal_re]
  simp_rw [tailEnergy_average, Complex.ofReal_re, cauchyFlow_norm_sq]
  have h := finite_tail_energy_repair t (fun i => ‖a i‖^2) (fun i => sq_nonneg _)
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

end OperatorDerivativeRewrite.Foundation.BrownianEnergyRepair.Integrated

namespace OperatorDerivativeRewrite.Foundation.BrownianEnergyRepair.Integrated
open OperatorDerivativeRewrite.Foundation
open OperatorDerivativeRewrite.Foundation.BrownianEnergyRepair.Torus

theorem brownianMatrix_original (N : ℕ) : brownianMatrix N =
    BrownianCovariancePowers.covariance N 1 := by
  funext i j
  simp [brownianMatrix, BrownianCovariancePowers.covariance]

theorem tailMatrix_sum {N : ℕ} (i j : Fin N) :
    (∑ r ∈ Finset.range N, tailMatrix r i j) = brownianMatrix N i j := by
  have he (r : ℕ) : (r ≤ i.val ∧ r ≤ j.val) ↔ r < min i.val j.val + 1 := by omega
  simp only [tailMatrix, he]
  rw [BrownianCovariancePowers.prefix_sum (fun _ => 1) N (min i.val j.val+1) (by omega)]
  simp [brownianMatrix]

end OperatorDerivativeRewrite.Foundation.BrownianEnergyRepair.Integrated
