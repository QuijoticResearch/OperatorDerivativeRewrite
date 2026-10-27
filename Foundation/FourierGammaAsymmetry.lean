import Foundation.FourierGammaNormalization
/-! An unnormalized asymmetric Fourier symbol with positive real Gamma. -/
open scoped BigOperators ComplexConjugate
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourierGammaAsymmetry
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
open FiniteStableGamma.Core FiniteStableGamma.ComplexEnergy
open FourierGammaCovariance FourierGammaCriterion FourierCovarianceCriterion

def offsetSymbol (k : Wave) : ℝ := 2 + (k 0 : ℝ)^2 + (k 0 : ℝ)

theorem offset_kernel (k l : Wave) :
    kernel offsetSymbol k l = 1 + (k 0 : ℝ)*(l 0 : ℝ) + (k 0 : ℝ) := by
  simp only [kernel, offsetSymbol, Pi.sub_apply, Int.cast_sub]
  ring

theorem offset_real_energy_nonnegative {ι : Type} [Fintype ι]
    (k : ι → Wave) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * kernel offsetSymbol (k i) (k j) := by
  let S : ℝ := ∑ i, c i
  let T : ℝ := ∑ i, c i * (k i 0 : ℝ)
  have he : (∑ i, ∑ j, c i * c j * kernel offsetSymbol (k i) (k j)) =
      S*S + T*T + T*S := by
    simp only [offset_kernel]
    have hA : (∑ i, ∑ j, c i * c j) = S*S := by
      dsimp [S]
      symm
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    have hB : (∑ i, ∑ j, (c i * (k i 0 : ℝ)) *
        (c j * (k j 0 : ℝ))) = T*T := by
      dsimp [T]
      symm
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    have hC : (∑ i, ∑ j, (c i * (k i 0 : ℝ)) * c j) = T*S := by
      dsimp [T,S]
      symm
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    calc
      _ = (∑ i, ∑ j, c i * c j) +
          (∑ i, ∑ j, (c i * (k i 0 : ℝ)) * (c j * (k j 0 : ℝ))) +
          (∑ i, ∑ j, (c i * (k i 0 : ℝ)) * c j) := by
            simp only [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = S*S + T*T + T*S := by rw [hA,hB,hC]
  rw [he]
  nlinarith [sq_nonneg (2*T+S), sq_nonneg S]

theorem offset_complex_energy_nonnegative {ι : Type} [Fintype ι]
    (k : ι → Wave) (b : ι → ℂ) :
    0 ≤ (energy (fun i j => kernel offsetSymbol (k i) (k j)) b).re := by
  have he := energy_re ((fun i j => kernel offsetSymbol (k i) (k j)) : Matrix ι ι ℝ) b
  rw [he]
  exact add_nonneg (offset_real_energy_nonnegative k (fun i => (b i).re))
    (offset_real_energy_nonnegative k (fun i => (b i).im))

theorem offset_gamma_real_nonnegative (f : Fourier) (x : Space) :
    0 ≤ (synthesis x (gammaIter offsetSymbol 1 f f)).re := by
  classical
  have hf : (∑ k : f.coeff.support,
      AddMonoidAlgebra.single k.val (f.coeff k.val)) = f :=
    (Finset.sum_attach f.coeff.support (fun k => AddMonoidAlgebra.single k (f.coeff k))).trans
      (AddMonoidAlgebra.sum_coeff_single f)
  rw [← hf, gamma_energy]
  simpa only [pow_one] using offset_complex_energy_nonnegative
    (fun k : f.coeff.support => k.val)
    (fun k => f.coeff k.val * character k.val x)

theorem offset_symbol_not_even :
    ¬ ∀ k : Wave, offsetSymbol (-k) = offsetSymbol k := by
  intro h
  have hh := h (fun _ => 1)
  norm_num [offsetSymbol] at hh

def imaginaryWitness : Fourier :=
  AddMonoidAlgebra.single (0 : Wave) 1 +
    AddMonoidAlgebra.single (fun _ => 1) Complex.I

theorem offset_gamma_imaginary :
    (synthesis (0 : Space)
      (gammaIter offsetSymbol 1 imaginaryWitness imaginaryWitness)).im = -1 := by
  unfold imaginaryWitness
  have h := gamma_energy offsetSymbol 1
    (![0,(fun _ => 1)] : Fin 2 → Wave) (![1,Complex.I] : Fin 2 → ℂ) (0 : Space)
  have him := congrArg Complex.im h
  have he : (synthesis (0 : Space)
      (gammaIter offsetSymbol 1
        (AddMonoidAlgebra.single (0 : Wave) 1 +
          AddMonoidAlgebra.single (fun _ => 1) Complex.I)
        (AddMonoidAlgebra.single (0 : Wave) 1 +
          AddMonoidAlgebra.single (fun _ => 1) Complex.I))).im =
      (energy (fun i j => kernel offsetSymbol
        ((![0,(fun _ => 1)] : Fin 2 → Wave) i)
        ((![0,(fun _ => 1)] : Fin 2 → Wave) j))
        (fun i => (![1,Complex.I] : Fin 2 → ℂ) i)).im := by
    simpa [Fin.sum_univ_two, FourierGammaCriterion.character_at_origin] using him
  rw [he]
  norm_num [energy, Fin.sum_univ_two, offset_kernel]

theorem offset_not_covariance : ¬ CovarianceSymbol offsetSymbol := by
  intro h
  have hi := (FourierGammaCovariance.gamma_nonnegative offsetSymbol h 1
    imaginaryWitness (0 : Space)).1
  rw [offset_gamma_imaginary] at hi
  norm_num at hi

theorem offset_real_positive_not_covariance :
    (∀ f : Fourier, ∀ x : Space,
      0 ≤ (synthesis x (gammaIter offsetSymbol 1 f f)).re) ∧
      ¬ CovarianceSymbol offsetSymbol :=
  ⟨offset_gamma_real_nonnegative, offset_not_covariance⟩

end OperatorDerivativeRewrite.Foundation.FourierGammaAsymmetry
