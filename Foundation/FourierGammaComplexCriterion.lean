import Foundation.FourierGammaAsymmetry
/-! Complex reality completes the unnormalized finite Fourier Gamma criterion. -/
open scoped BigOperators ComplexConjugate
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourierGammaComplexCriterion
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
open FiniteStableGamma.Core FiniteStableGamma.ComplexEnergy
open FourierGammaCovariance FourierGammaCriterion FourierCovarianceCriterion

def imaginaryPair (k l : Wave) : Fourier :=
  AddMonoidAlgebra.single k 1 + AddMonoidAlgebra.single l Complex.I

theorem pair_gamma_imaginary (ψ : Wave → ℝ) (k l : Wave) :
    (synthesis (0 : Space)
      (gammaIter ψ 1 (imaginaryPair k l) (imaginaryPair k l))).im =
        kernel ψ k l - kernel ψ l k := by
  unfold imaginaryPair
  have h := gamma_energy ψ 1 (![k,l] : Fin 2 → Wave)
    (![1,Complex.I] : Fin 2 → ℂ) (0 : Space)
  have him := congrArg Complex.im h
  have he : (synthesis (0 : Space)
      (gammaIter ψ 1
        (AddMonoidAlgebra.single k 1 + AddMonoidAlgebra.single l Complex.I)
        (AddMonoidAlgebra.single k 1 + AddMonoidAlgebra.single l Complex.I))).im =
      (energy (fun i j => kernel ψ
        ((![k,l] : Fin 2 → Wave) i)
        ((![k,l] : Fin 2 → Wave) j))
        (fun i => (![1,Complex.I] : Fin 2 → ℂ) i)).im := by
    simpa [Fin.sum_univ_two, FourierGammaCriterion.character_at_origin] using him
  rw [he]
  norm_num [energy, Fin.sum_univ_two]
  ring

theorem kernel_symmetric_of_pair_real (ψ : Wave → ℝ)
    (h : ∀ k l : Wave,
      (synthesis (0 : Space)
        (gammaIter ψ 1 (imaginaryPair k l) (imaginaryPair k l))).im = 0) :
    ∀ k l, kernel ψ k l = kernel ψ l k := by
  intro k l
  have hh := h k l
  rw [pair_gamma_imaginary] at hh
  exact sub_eq_zero.mp hh

theorem symbol_even_of_pair_real (ψ : Wave → ℝ)
    (h : ∀ k l : Wave,
      (synthesis (0 : Space)
        (gammaIter ψ 1 (imaginaryPair k l) (imaginaryPair k l))).im = 0) :
    ∀ k, ψ (-k) = ψ k := by
  intro k
  have hs := kernel_symmetric_of_pair_real ψ h 0 k
  simp only [kernel, zero_sub, sub_zero] at hs
  linarith

theorem covariance_of_gamma_complex (ψ : Wave → ℝ)
    (hreal : ∀ k l : Wave,
      (synthesis (0 : Space)
        (gammaIter ψ 1 (imaginaryPair k l) (imaginaryPair k l))).im = 0)
    (hpos : ∀ f : Fourier,
      0 ≤ (synthesis (0 : Space) (gammaIter ψ 1 f f)).re) :
    CovarianceSymbol ψ := by
  intro ι _ _ k
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change kernel ψ (k j) (k i) = kernel ψ (k i) (k j)
    exact kernel_symmetric_of_pair_real ψ hreal _ _
  · intro c
    have h := hpos (∑ i, AddMonoidAlgebra.single (k i) (c i : ℂ))
    rw [real_gamma_energy] at h
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h

theorem gamma_complex_iff_covariance (ψ : Wave → ℝ) :
    ((∀ k l : Wave,
      (synthesis (0 : Space)
        (gammaIter ψ 1 (imaginaryPair k l) (imaginaryPair k l))).im = 0) ∧
      (∀ f : Fourier,
        0 ≤ (synthesis (0 : Space) (gammaIter ψ 1 f f)).re)) ↔
      CovarianceSymbol ψ := by
  constructor
  · rintro ⟨hr,hp⟩
    exact covariance_of_gamma_complex ψ hr hp
  · intro hcov
    constructor
    · intro k l
      exact (gamma_nonnegative ψ hcov 1 (imaginaryPair k l) 0).1
    · intro f
      exact (gamma_nonnegative ψ hcov 1 f 0).2

theorem gamma_full_iff_covariance (ψ : Wave → ℝ) :
    (∀ f : Fourier,
      (synthesis (0 : Space) (gammaIter ψ 1 f f)).im = 0 ∧
      0 ≤ (synthesis (0 : Space) (gammaIter ψ 1 f f)).re) ↔
      CovarianceSymbol ψ := by
  constructor
  · intro h
    apply (gamma_complex_iff_covariance ψ).mp
    exact ⟨(fun k l => (h (imaginaryPair k l)).1),
      (fun f => (h f).2)⟩
  · intro hcov f
    exact gamma_nonnegative ψ hcov 1 f 0

end OperatorDerivativeRewrite.Foundation.FourierGammaComplexCriterion
