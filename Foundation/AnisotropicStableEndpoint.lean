import Foundation.AnisotropicStableGamma
/-! The sharp positive-exponent covariance/Gamma boundary for a pure
coordinate symbol: 0 < γ ≤ 2 works, γ > 2 fails by a three-frequency
conditional-negative-energy witness. Nonnegative mixed coordinate sums remain
positive with individual 0 < γ_j ≤ 2, including quadratic Brownian axes.
This is Fourier/Gamma algebra, not a stochastic-process construction. -/
open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
open FiniteStableGamma.Core FourierCovarianceCriterion
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.AnisotropicStableEndpoint

theorem axis_kernel_two (j : Fin 3) (k l : Wave) :
    kernel (AnisotropicStableGamma.axisSymbol 2 j) k l =
      (k j : ℝ) * (l j : ℝ) := by
  simp [kernel,AnisotropicStableGamma.axisSymbol,
    Pi.sub_apply,Int.cast_sub,sq_abs]
  ring

theorem axis_covariance_two (j : Fin 3) :
    CovarianceSymbol (AnisotropicStableGamma.axisSymbol 2 j) := by
  apply FourierCovarianceCriterion.hilbert_covariance
    (v := fun k : Wave => (k j : ℝ))
  · intro k
    simp [AnisotropicStableGamma.axisSymbol,
      Real.norm_eq_abs,sq_abs]
  · intro k l
    simp [AnisotropicStableGamma.axisSymbol,
      Real.norm_eq_abs,Pi.sub_apply,Int.cast_sub,sq_abs]

theorem quadratic_kernel (a : Fin 3 → ℝ) (k l : Wave) :
    kernel (AnisotropicStableGamma.anisotropicSymbol a (fun _ => 2)) k l =
      ∑ j : Fin 3, a j * (k j : ℝ) * (l j : ℝ) := by
  have h : kernel (AnisotropicStableGamma.anisotropicSymbol a (fun _ => 2)) k l =
      ∑ j : Fin 3, a j * kernel (AnisotropicStableGamma.axisSymbol 2 j) k l := by
    unfold kernel AnisotropicStableGamma.anisotropicSymbol
    simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  rw [axis_kernel_two]
  ring

theorem axis_covariance_le_two (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ ≤ 2)
    (j : Fin 3) : CovarianceSymbol (AnisotropicStableGamma.axisSymbol γ j) := by
  rcases lt_or_eq_of_le hγ2 with hlt | heq
  · exact AnisotropicStableGamma.axis_covariance γ hγ0 hlt j
  · subst γ
    exact axis_covariance_two j

theorem anisotropic_covariance_le_two (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j) (hγ2 : ∀ j, γ j ≤ 2) :
    CovarianceSymbol (AnisotropicStableGamma.anisotropicSymbol a γ) := by
  have h := AnisotropicStableGamma.covariance_sum (Finset.univ : Finset (Fin 3))
    (fun j k => a j * AnisotropicStableGamma.axisSymbol (γ j) j k) (by
      intro j hj
      exact AnisotropicStableGamma.covariance_scale (a j) (ha j) _
        (axis_covariance_le_two (γ j) (hγ0 j) (hγ2 j) j))
  change CovarianceSymbol
    (fun k => ∑ j, a j * AnisotropicStableGamma.axisSymbol (γ j) j k)
  exact h

theorem anisotropic_negative_le_two (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j) (hγ2 : ∀ j, γ j ≤ 2) :
    NegativeSymbol (AnisotropicStableGamma.anisotropicSymbol a γ) := by
  exact (FourierCovarianceCriterion.symbol_iff _
    (AnisotropicStableGamma.anisotropic_zero a γ hγ0)
    (AnisotropicStableGamma.anisotropic_even a γ)).mp
      (anisotropic_covariance_le_two a γ ha hγ0 hγ2)

theorem anisotropic_gamma_le_two (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j) (hγ2 : ∀ j, γ j ≤ 2)
    (n : ℕ) (f : Fourier) (x : Space) :
    (synthesis x (gammaIter (AnisotropicStableGamma.anisotropicSymbol a γ) n f f)).im = 0 ∧
      0 ≤ (synthesis x (gammaIter (AnisotropicStableGamma.anisotropicSymbol a γ) n f f)).re :=
  FourierGammaCovariance.gamma_nonnegative _
    (anisotropic_covariance_le_two a γ ha hγ0 hγ2) n f x

def tripleWave : Fin 3 → Wave := ![0,(fun _ => 1),(fun _ => 2)]
def tripleWeights : Fin 3 → ℝ := ![1,-2,1]

theorem triple_sum : ∑ i : Fin 3, tripleWeights i = 0 := by
  norm_num [tripleWeights,Fin.sum_univ_succ]

theorem triple_energy (γ : ℝ) (hγ : 2 < γ) (j : Fin 3) :
    AnchoredCovariance.energy
      (fun i l => AnisotropicStableGamma.axisSymbol γ j
        (tripleWave l-tripleWave i)) tripleWeights =
      2*((2 : ℝ)^γ-4) := by
  have hγ0 : γ ≠ 0 := by linarith
  norm_num [AnchoredCovariance.energy,Fin.sum_univ_succ,tripleWave,
    tripleWeights,AnisotropicStableGamma.axisSymbol,Pi.sub_apply,
    Real.zero_rpow hγ0]
  ring

theorem axis_not_negative_above_two (γ : ℝ) (hγ : 2 < γ) (j : Fin 3) :
    ¬ NegativeSymbol (AnisotropicStableGamma.axisSymbol γ j) := by
  intro h
  have hn := h (Fin 3) tripleWave tripleWeights triple_sum
  rw [triple_energy γ hγ j] at hn
  have hp : (4:ℝ) < 2^γ := by
    have hp0 := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hγ
    norm_num at hp0
    exact hp0
  linarith

theorem axis_zero (γ : ℝ) (hγ : 0 < γ) (j : Fin 3) :
    AnisotropicStableGamma.axisSymbol γ j 0 = 0 := by
  simp [AnisotropicStableGamma.axisSymbol,Real.zero_rpow (ne_of_gt hγ)]

theorem axis_even (γ : ℝ) (j : Fin 3) (k : Wave) :
    AnisotropicStableGamma.axisSymbol γ j (-k) =
      AnisotropicStableGamma.axisSymbol γ j k := by
  simp [AnisotropicStableGamma.axisSymbol]

theorem axis_negative_iff_le_two (γ : ℝ) (hγ : 0 < γ) (j : Fin 3) :
    NegativeSymbol (AnisotropicStableGamma.axisSymbol γ j) ↔ γ ≤ 2 := by
  constructor
  · intro h
    by_contra hn
    exact (axis_not_negative_above_two γ (lt_of_not_ge hn) j) h
  · intro hle
    exact (FourierCovarianceCriterion.symbol_iff _ (axis_zero γ hγ j)
      (axis_even γ j)).mp (axis_covariance_le_two γ hγ hle j)

theorem axis_covariance_iff_le_two (γ : ℝ) (hγ : 0 < γ) (j : Fin 3) :
    CovarianceSymbol (AnisotropicStableGamma.axisSymbol γ j) ↔ γ ≤ 2 := by
  rw [FourierCovarianceCriterion.symbol_iff _ (axis_zero γ hγ j)
    (axis_even γ j)]
  exact axis_negative_iff_le_two γ hγ j

theorem axis_gamma1_positive_iff_le_two (γ : ℝ) (hγ : 0 < γ) (j : Fin 3) :
    (∀ f : Fourier, 0 ≤ (synthesis (0 : Space)
      (gammaIter (AnisotropicStableGamma.axisSymbol γ j) 1 f f)).re) ↔
      γ ≤ 2 := by
  exact (FourierGammaCriterion.gamma_positive_iff_negative _
    (axis_zero γ hγ j) (axis_even γ j)).trans
      (axis_negative_iff_le_two γ hγ j)

end OperatorDerivativeRewrite.Foundation.AnisotropicStableEndpoint
