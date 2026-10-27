import Foundation.FourierGammaCovariance
/-! The finite Fourier Gamma1 positivity criterion and a quartic witness.
At the spatial origin, real Fourier coefficients recover the exact matrix form.
Even symbols yield an iff; the quartic symbol gives a negative value.
No completed domain, positive curvature constant or process is inferred. -/
open scoped BigOperators
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourierGammaCriterion
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
open FiniteStableGamma.Core FiniteStableGamma.ComplexEnergy
open FourierCovarianceCriterion FourierGammaCovariance

theorem character_at_origin (k : Wave) : character k (0 : Space) = 1 := by
  simp [character, phase]

theorem real_gamma_energy {ι : Type} [Fintype ι] (ψ : Wave → ℝ)
    (k : ι → Wave) (c : ι → ℝ) :
    (synthesis (0 : Space) (gammaIter ψ 1
      (∑ i, AddMonoidAlgebra.single (k i) (c i : ℂ))
      (∑ i, AddMonoidAlgebra.single (k i) (c i : ℂ)))).re =
      ∑ i, ∑ j, c i * c j * kernel ψ (k i) (k j) := by
  rw [gamma_energy]
  simp only [character_at_origin, mul_one, pow_one]
  have hh := energy_re ((fun i j => kernel ψ (k i) (k j)) : Matrix ι ι ℝ)
    (fun i => (c i : ℂ))
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    Finset.sum_const_zero, add_zero] at hh
  rw [hh]

theorem covariance_of_gamma_positive (ψ : Wave → ℝ)
    (he : ∀ k, ψ (-k) = ψ k)
    (hp : ∀ (f : Fourier), 0 ≤ (synthesis (0 : Space) (gammaIter ψ 1 f f)).re) :
    CovarianceSymbol ψ := by
  intro ι _ _ k
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change kernel ψ (k j) (k i) = kernel ψ (k i) (k j)
    simp only [kernel]
    rw [show k i-k j = -(k j-k i) by abel, he]
    ring
  · intro c
    have h := hp (∑ i, AddMonoidAlgebra.single (k i) (c i : ℂ))
    rw [real_gamma_energy] at h
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using h

theorem gamma_positive_iff_covariance (ψ : Wave → ℝ)
    (he : ∀ k, ψ (-k) = ψ k) :
    (∀ (f : Fourier), 0 ≤ (synthesis (0 : Space) (gammaIter ψ 1 f f)).re) ↔
      CovarianceSymbol ψ := by
  constructor
  · exact covariance_of_gamma_positive ψ he
  · intro hp f
    exact (gamma_nonnegative ψ hp 1 f 0).2

theorem gamma_positive_iff_negative (ψ : Wave → ℝ)
    (h0 : ψ 0 = 0) (he : ∀ k, ψ (-k) = ψ k) :
    (∀ (f : Fourier), 0 ≤ (synthesis (0 : Space) (gammaIter ψ 1 f f)).re) ↔
      NegativeSymbol ψ := by
  exact (gamma_positive_iff_covariance ψ he).trans (symbol_iff ψ h0 he)

def quarticWaves : Fin 3 → Wave := ![0, (fun _ => 1), (fun _ => 2)]
def quarticCoefficients : Fin 3 → ℝ := ![-1,2,-1]
def quarticWitness : Fourier :=
  ∑ i : Fin 3, AddMonoidAlgebra.single (quarticWaves i) (quarticCoefficients i : ℂ)

theorem quartic_gamma_negative :
    (synthesis (0 : Space)
      (gammaIter (stableSymbol 4) 1 quarticWitness quarticWitness)).re = -12 := by
  unfold quarticWitness
  rw [real_gamma_energy]
  norm_num [Fin.sum_univ_succ, quarticWaves, quarticCoefficients,
    kernel, stableSymbol, Pi.sub_apply, Real.rpow_natCast]

theorem quartic_not_gamma_positive :
    ¬ ∀ f : Fourier, 0 ≤ (synthesis (0 : Space) (gammaIter (stableSymbol 4) 1 f f)).re := by
  intro h
  have hh := h quarticWitness
  rw [quartic_gamma_negative] at hh
  norm_num at hh

end OperatorDerivativeRewrite.Foundation.FourierGammaCriterion
