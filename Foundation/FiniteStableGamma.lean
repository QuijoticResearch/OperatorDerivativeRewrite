import Foundation.FiniteFourierReality
import Foundation.FractionalCovarianceMatrices
import Mathlib.Basic.Complex.Basic

/-! Actual finite Fourier Gamma recursion, its fractional covariance kernel,
and complex phase-energy positivity. This is a finite polynomial core, not a
completed generator-domain or stochastic-process realization. -/
noncomputable section
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.FiniteStableGamma.Core
open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FiniteFourierReality

def generator (a : Wave → ℝ) : Fourier →ₗ[ℂ] Fourier :=
  (Finsupp.linearCombination ℂ (fun k : Wave =>
    (-(a k : ℂ)) • (AddMonoidAlgebra.single k 1 : Fourier))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem generator_single (a : Wave → ℝ) (k : Wave) (c : ℂ) :
    generator a (AddMonoidAlgebra.single k c) = AddMonoidAlgebra.single k (-(a k : ℂ)*c) := by
  simp [generator, Finsupp.linearCombination_single, mul_comm]

def kernel (a : Wave → ℝ) (k l : Wave) : ℝ := (a k + a l - a (l-k))/2

def gammaIter (a : Wave → ℝ) : ℕ → Fourier → Fourier → Fourier
  | 0, f, g => reflection f * g
  | n+1, f, g => (1/2 : ℂ) •
      (generator a (gammaIter a n f g) - gammaIter a n (generator a f) g -
        gammaIter a n f (generator a g))

theorem gammaIter_single (a : Wave → ℝ) (n : ℕ) (k l : Wave) (c d : ℂ) :
    gammaIter a n (AddMonoidAlgebra.single k c) (AddMonoidAlgebra.single l d) =
      AddMonoidAlgebra.single (l-k) ((kernel a k l : ℂ)^n * conj c * d) := by
  induction n generalizing c d with
  | zero =>
    simp [gammaIter, reflection_single, AddMonoidAlgebra.single_mul_single,
      sub_eq_add_neg, add_comm]
  | succ n ih =>
    simp only [gammaIter, generator_single, ih]
    ext w
    by_cases hw : l-k = w
    · subst w
      simp [kernel, pow_succ, map_mul]
      ring
    · simp [AddMonoidAlgebra.coeff_single, hw]

theorem gammaIter_zero_left (a : Wave → ℝ) (n : ℕ) (g : Fourier) :
    gammaIter a n 0 g = 0 := by
  induction n generalizing g with
  | zero => simp [gammaIter]
  | succ n ih => simp [gammaIter, ih]

theorem gammaIter_zero_right (a : Wave → ℝ) (n : ℕ) (f : Fourier) :
    gammaIter a n f 0 = 0 := by
  induction n generalizing f with
  | zero => simp [gammaIter]
  | succ n ih => simp [gammaIter, ih]

theorem gammaIter_add_left (a : Wave → ℝ) (n : ℕ) (f f' g : Fourier) :
    gammaIter a n (f+f') g = gammaIter a n f g + gammaIter a n f' g := by
  induction n generalizing f f' g with
  | zero => simp [gammaIter, add_mul]
  | succ n ih =>
    simp only [gammaIter, map_add, ih]
    module

theorem gammaIter_add_right (a : Wave → ℝ) (n : ℕ) (f g g' : Fourier) :
    gammaIter a n f (g+g') = gammaIter a n f g + gammaIter a n f g' := by
  induction n generalizing f g g' with
  | zero => simp [gammaIter, mul_add]
  | succ n ih =>
    simp only [gammaIter, map_add, ih]
    module

def stableSymbol (γ : ℝ) (k : Wave) : ℝ := |(k 0 : ℝ)|^γ

theorem stable_kernel_covariance (γ : ℝ) (k l : Wave) :
    kernel (stableSymbol γ) k l = FractionalSpectralGeometry.covariance (γ/2) (k 0) (l 0) := by
  unfold kernel stableSymbol FractionalSpectralGeometry.covariance
  have he : 2*(γ/2) = γ := by ring
  simp [he, Pi.sub_apply, Int.cast_sub]

theorem gammaIter_sum_left {ι : Type*} (a : Wave → ℝ) (n : ℕ)
    (s : Finset ι) (f : ι → Fourier) (g : Fourier) :
    gammaIter a n (∑ i ∈ s, f i) g = ∑ i ∈ s, gammaIter a n (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gammaIter_zero_left]
  | @insert i s hi ih => simp [Finset.sum_insert hi, gammaIter_add_left, ih]

theorem gammaIter_sum_right {ι : Type*} (a : Wave → ℝ) (n : ℕ)
    (s : Finset ι) (f : Fourier) (g : ι → Fourier) :
    gammaIter a n f (∑ i ∈ s, g i) = ∑ i ∈ s, gammaIter a n f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gammaIter_zero_right]
  | @insert i s hi ih => simp [Finset.sum_insert hi, gammaIter_add_right, ih]

theorem gammaIter_finite {ι κ : Type*} (a : Wave → ℝ) (n : ℕ)
    (s : Finset ι) (t : Finset κ) (k : ι → Wave) (l : κ → Wave)
    (c : ι → ℂ) (d : κ → ℂ) :
    gammaIter a n (∑ i ∈ s, AddMonoidAlgebra.single (k i) (c i))
      (∑ j ∈ t, AddMonoidAlgebra.single (l j) (d j)) =
      ∑ i ∈ s, ∑ j ∈ t, AddMonoidAlgebra.single (l j-k i)
        ((kernel a (k i) (l j) : ℂ)^n * conj (c i) * d j) := by
  simp only [gammaIter_sum_left, gammaIter_sum_right, gammaIter_single]
  rw [Finset.sum_comm]

theorem stable_gamma_synthesis {ι κ : Type*} (γ : ℝ) (n : ℕ)
    (s : Finset ι) (t : Finset κ) (k : ι → Wave) (l : κ → Wave)
    (c : ι → ℂ) (d : κ → ℂ) (x : FiniteFourierSynthesis.Space) :
    FiniteFourierSynthesis.synthesis x
      (gammaIter (stableSymbol γ) n (∑ i ∈ s, AddMonoidAlgebra.single (k i) (c i))
        (∑ j ∈ t, AddMonoidAlgebra.single (l j) (d j))) =
      ∑ i ∈ s, ∑ j ∈ t,
        ((FractionalSpectralGeometry.covariance (γ/2) (k i 0) (l j 0) : ℂ)^n *
          conj (c i) * d j) * FiniteFourierSynthesis.character (l j-k i) x := by
  rw [gammaIter_finite]
  simp only [map_sum, FiniteFourierSynthesis.synthesis_single, stable_kernel_covariance]







end OperatorDerivativeRewrite.Foundation.FiniteStableGamma.Core

noncomputable section
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.FiniteStableGamma.ComplexEnergy
open OperatorDerivativeRewrite.Foundation
open FractionalSpectralGeometry FractionalCovarianceMatrices

def energy {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (b : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, (M i j : ℂ) * conj (b i) * b j

theorem energy_real {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (b : ι → ℂ)
    (hM : ∀ i j, M i j = M j i) : (energy M b).im = 0 := by
  have he : conj (energy M b) = energy M b := by
    unfold energy
    simp only [map_sum, map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp [hM j i]
    ring
  have hi := congrArg Complex.im he
  simp only [Complex.conj_im] at hi
  linarith

theorem energy_re {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (b : ι → ℂ) :
    (energy M b).re =
      (∑ i, ∑ j, (b i).re * (b j).re * M i j) +
      (∑ i, ∑ j, (b i).im * (b j).im * M i j) := by
  simp only [energy, Complex.re_sum, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem covariance_energy_nonneg {ι : Type*} [Fintype ι] (H : ℝ)
    (hH0 : 0 < H) (hH1 : H < 1) (t : ι → ℝ) (n : ℕ) (b : ι → ℂ) :
    0 ≤ (energy (covariancePower H t n) b).re := by
  rw [energy_re]
  exact add_nonneg (covariancePower_energy_nonneg H hH0 hH1 t n (fun i => (b i).re))
    (covariancePower_energy_nonneg H hH0 hH1 t n (fun i => (b i).im))

theorem covariance_energy_real {ι : Type*} [Fintype ι] (H : ℝ)
    (t : ι → ℝ) (n : ℕ) (b : ι → ℂ) :
    (energy (covariancePower H t n) b).im = 0 := by
  apply energy_real
  intro i j
  simp only [covariancePower, covariance_symm H (t i) (t j)]

end OperatorDerivativeRewrite.Foundation.FiniteStableGamma.ComplexEnergy

namespace OperatorDerivativeRewrite.Foundation.FiniteStableGamma.Bridge
open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierReality
open FractionalCovarianceMatrices
open OperatorDerivativeRewrite.Foundation.FiniteStableGamma.Core OperatorDerivativeRewrite.Foundation.FiniteStableGamma.ComplexEnergy

theorem stable_gamma_energy {ι : Type*} [Fintype ι] (γ : ℝ) (n : ℕ)
    (k : ι → Wave) (c : ι → ℂ) (x : Space) :
    synthesis x (gammaIter (stableSymbol γ) n
      (∑ i, AddMonoidAlgebra.single (k i) (c i))
      (∑ i, AddMonoidAlgebra.single (k i) (c i))) =
      energy (covariancePower (γ/2) (fun i => (k i 0 : ℝ)) n)
        (fun i => c i * character (k i) x) := by
  rw [stable_gamma_synthesis]
  unfold energy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [covariancePower, Complex.ofReal_pow, map_mul, sub_eq_add_neg,
    character_add, character_neg]
  ring

theorem stable_gamma_nonnegative {ι : Type*} [Fintype ι] (γ : ℝ)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (n : ℕ) (k : ι → Wave) (c : ι → ℂ) (x : Space) :
    let z := synthesis x (gammaIter (stableSymbol γ) n
      (∑ i, AddMonoidAlgebra.single (k i) (c i))
      (∑ i, AddMonoidAlgebra.single (k i) (c i)))
    z.im = 0 ∧ 0 ≤ z.re := by
  dsimp only
  rw [stable_gamma_energy]
  exact ⟨covariance_energy_real _ _ _ _,
    covariance_energy_nonneg _ (by linarith) (by linarith) _ _ _⟩

end OperatorDerivativeRewrite.Foundation.FiniteStableGamma.Bridge
