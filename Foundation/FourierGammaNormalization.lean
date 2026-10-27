import Foundation.FourierGammaCriterion
/-! Origin Gamma tests force symmetry for normalized symbols.
A two-frequency polynomial tests the odd part of the symbol.
Conditional negativity alone permits odd symbols; the exact criterion records evenness.
No completed domain, positive curvature constant or process is inferred. -/
open scoped BigOperators
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourierGammaNormalization
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
open FiniteStableGamma.Core FourierGammaCriterion FourierCovarianceCriterion

def pairWaves (k : Wave) : Fin 2 → Wave := ![0,k]
def pairCoefficients (t : ℝ) : Fin 2 → ℝ := ![t,1]
def pairPolynomial (k : Wave) (t : ℝ) : Fourier :=
  ∑ i : Fin 2, AddMonoidAlgebra.single (pairWaves k i) (pairCoefficients t i : ℂ)

theorem pair_gamma_energy (ψ : Wave → ℝ) (h0 : ψ 0 = 0) (k : Wave) (t : ℝ) :
    (synthesis (0 : Space) (gammaIter ψ 1 (pairPolynomial k t) (pairPolynomial k t))).re =
      ψ k + t * ((ψ k - ψ (-k))/2) := by
  unfold pairPolynomial
  rw [real_gamma_energy]
  simp [Fin.sum_univ_two, pairWaves, pairCoefficients, kernel, h0]
  ring

theorem even_of_gamma_positive (ψ : Wave → ℝ) (h0 : ψ 0 = 0)
    (hp : ∀ f : Fourier, 0 ≤ (synthesis (0 : Space) (gammaIter ψ 1 f f)).re) :
    ∀ k, ψ (-k) = ψ k := by
  intro k
  have ht (t : ℝ) : 0 ≤ ψ k + t * ((ψ k - ψ (-k))/2) := by
    simpa only [pair_gamma_energy ψ h0 k t] using hp (pairPolynomial k t)
  by_contra hn
  have hd : ψ k - ψ (-k) ≠ 0 := by
    intro h
    apply hn
    exact (sub_eq_zero.mp h).symm
  have hh := ht (-(ψ k + 1) * 2 / (ψ k - ψ (-k)))
  have he : (-(ψ k + 1) * 2 / (ψ k - ψ (-k))) * (ψ k - ψ (-k)) =
      -(ψ k + 1) * 2 := div_mul_cancel₀ _ hd
  have he' : (-(ψ k + 1) * 2 / (ψ k - ψ (-k))) * ((ψ k - ψ (-k))/2) =
      -(ψ k + 1) := by
    calc
      _ = ((-(ψ k + 1) * 2 / (ψ k - ψ (-k))) * (ψ k - ψ (-k))) / 2 := by ring
      _ = -(ψ k + 1) := by rw [he]; ring
  rw [he'] at hh
  linarith

theorem normalized_gamma_iff_negative_even (ψ : Wave → ℝ) (h0 : ψ 0 = 0) :
    (∀ f : Fourier, 0 ≤ (synthesis (0 : Space) (gammaIter ψ 1 f f)).re) ↔
      NegativeSymbol ψ ∧ (∀ k, ψ (-k) = ψ k) := by
  constructor
  · intro hp
    have he := even_of_gamma_positive ψ h0 hp
    exact ⟨(gamma_positive_iff_negative ψ h0 he).mp hp, he⟩
  · rintro ⟨hn, he⟩
    exact (gamma_positive_iff_negative ψ h0 he).mpr hn

theorem normalized_gamma_iff_covariance (ψ : Wave → ℝ) (h0 : ψ 0 = 0) :
    (∀ f : Fourier, 0 ≤ (synthesis (0 : Space) (gammaIter ψ 1 f f)).re) ↔
      CovarianceSymbol ψ := by
  constructor
  · intro hp
    exact covariance_of_gamma_positive ψ (even_of_gamma_positive ψ h0 hp) hp
  · intro hcov f
    exact (FourierGammaCovariance.gamma_nonnegative ψ hcov 1 f 0).2

theorem antisymmetric_energy_zero {ι : Type} [Fintype ι]
    (d : ι → ι → ℝ) (hd : ∀ i j, d i j = -d j i) (c : ι → ℝ) :
    AnchoredCovariance.energy d c = 0 := by
  unfold AnchoredCovariance.energy
  have he : (∑ i, ∑ j, c i * c j * d i j) =
      ∑ i, ∑ j, c i * c j * d j i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hz : (∑ i, ∑ j, c i * c j * d i j) =
      -(∑ i, ∑ j, c i * c j * d i j) := by
    calc
      _ = (∑ i, ∑ j, c i * c j * d j i) := he
      _ = ∑ i, ∑ j, c i * c j * (-d i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hd j i]
      _ = -(∑ i, ∑ j, c i * c j * d i j) := by
        simp only [mul_neg, Finset.sum_neg_distrib]
  linarith

theorem odd_symbol_negative (ψ : Wave → ℝ)
    (ho : ∀ k, ψ (-k) = -ψ k) : NegativeSymbol ψ := by
  intro ι _ _ k c hc
  have hz := antisymmetric_energy_zero
    (fun i j => ψ (k j-k i))
    (by
      intro i j
      rw [show k j-k i = -(k i-k j) by abel, ho]) c
  rw [hz]

def linearSymbol (k : Wave) : ℝ := (k 0 : ℝ)

theorem linear_symbol_negative : NegativeSymbol linearSymbol := by
  apply odd_symbol_negative
  intro k
  simp [linearSymbol]

theorem linear_symbol_gamma_negative :
    (synthesis (0 : Space) (gammaIter linearSymbol 1
      (pairPolynomial (fun _ => 1) (-2))
      (pairPolynomial (fun _ => 1) (-2)))).re = -1 := by
  rw [pair_gamma_energy linearSymbol (by simp [linearSymbol])]
  norm_num [linearSymbol]

theorem linear_negative_not_gamma_positive :
    NegativeSymbol linearSymbol ∧
      ¬ (∀ f : Fourier, 0 ≤ (synthesis (0 : Space) (gammaIter linearSymbol 1 f f)).re) := by
  refine ⟨linear_symbol_negative, ?_⟩
  intro hp
  have h := hp (pairPolynomial (fun _ => 1) (-2))
  rw [linear_symbol_gamma_negative] at h
  norm_num at h

end OperatorDerivativeRewrite.Foundation.FourierGammaNormalization
