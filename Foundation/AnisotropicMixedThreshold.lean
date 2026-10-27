import Foundation.AnisotropicStableEndpoint
/-! Exact mixed-coordinate stable covariance threshold. For nonnegative axis
weights and positive exponents, conditional negativity, anchored covariance
positivity, and polynomial first-Gamma positivity hold exactly when every
positive-weight axis has exponent at most two. A zero-weight coordinate is
irrelevant even when its nominal exponent exceeds two. This is Fourier-symbol
algebra; it does not construct a Markov process. -/
open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
open FiniteStableGamma.Core FourierCovarianceCriterion
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.AnisotropicMixedThreshold

def tripleIntegers : Fin 3 → ℤ := ![0,1,2]
def axisTriple (j : Fin 3) (i : Fin 3) : Wave := Pi.single j (tripleIntegers i)

theorem axis_single_sub (j : Fin 3) (i l : Fin 3) :
    axisTriple j l - axisTriple j i =
      Pi.single j (tripleIntegers l-tripleIntegers i) := by
  ext m
  by_cases hm : m = j <;>
    simp [axisTriple,Pi.sub_apply,hm]

theorem mixed_on_axis (a γ : Fin 3 → ℝ) (hγ0 : ∀ j, 0 < γ j)
    (j : Fin 3) (n : ℤ) :
    AnisotropicStableGamma.anisotropicSymbol a γ (Pi.single j n) =
      a j * |(n : ℝ)|^(γ j) := by
  unfold AnisotropicStableGamma.anisotropicSymbol
  rw [Finset.sum_eq_single j]
  · simp [AnisotropicStableGamma.axisSymbol]
  · intro m hm hmj
    have hz : (Pi.single j n : Wave) m = 0 := by
      simp [Ne.symm hmj]
    simp [AnisotropicStableGamma.axisSymbol,hz,Real.zero_rpow (ne_of_gt (hγ0 m))]
  · simp

theorem mixed_triple_energy (a γ : Fin 3 → ℝ) (hγ0 : ∀ j, 0 < γ j)
    (j : Fin 3) :
    AnchoredCovariance.energy
      (fun i l => AnisotropicStableGamma.anisotropicSymbol a γ
        (axisTriple j l-axisTriple j i))
      AnisotropicStableEndpoint.tripleWeights =
        a j * (2*((2 : ℝ)^(γ j)-4)) := by
  have ht (i l : Fin 3) :
      AnisotropicStableGamma.anisotropicSymbol a γ
        (axisTriple j l-axisTriple j i) =
          a j * |((tripleIntegers l-tripleIntegers i : ℤ) : ℝ)|^(γ j) := by
    rw [axis_single_sub,mixed_on_axis a γ hγ0 j]
  unfold AnchoredCovariance.energy
  simp_rw [ht]
  norm_num [Fin.sum_univ_succ,AnisotropicStableEndpoint.tripleWeights,
    tripleIntegers,Real.zero_rpow (ne_of_gt (hγ0 j))]
  ring

theorem mixed_not_negative_above_two (a γ : Fin 3 → ℝ)
    (hγ0 : ∀ j, 0 < γ j) (j : Fin 3) (ha : 0 < a j)
    (hγgt : 2 < γ j) :
    ¬ NegativeSymbol (AnisotropicStableGamma.anisotropicSymbol a γ) := by
  intro h
  have hn := h (Fin 3) (axisTriple j) AnisotropicStableEndpoint.tripleWeights
    AnisotropicStableEndpoint.triple_sum
  rw [mixed_triple_energy a γ hγ0 j] at hn
  have hp : (4:ℝ) < 2^(γ j) := by
    have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hγgt
    norm_num at hh
    exact hh
  have hh : 0 < a j * (2*((2:ℝ)^(γ j)-4)) := by
    apply mul_pos ha
    linarith
  linarith

theorem anisotropic_covariance_of_positive_axes (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j)
    (hactive : ∀ j, 0 < a j → γ j ≤ 2) :
    CovarianceSymbol (AnisotropicStableGamma.anisotropicSymbol a γ) := by
  have h := AnisotropicStableGamma.covariance_sum (Finset.univ : Finset (Fin 3))
    (fun j k => a j * AnisotropicStableGamma.axisSymbol (γ j) j k) (by
      intro j hj
      by_cases hz : a j = 0
      · simpa [hz] using AnisotropicStableGamma.covariance_zero
      · have hp : 0 < a j := lt_of_le_of_ne (ha j) (Ne.symm hz)
        exact AnisotropicStableGamma.covariance_scale (a j) (ha j) _
          (AnisotropicStableEndpoint.axis_covariance_le_two
            (γ j) (hγ0 j) (hactive j hp) j))
  change CovarianceSymbol
    (fun k => ∑ j, a j * AnisotropicStableGamma.axisSymbol (γ j) j k)
  exact h

theorem anisotropic_negative_iff_active (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j) :
    NegativeSymbol (AnisotropicStableGamma.anisotropicSymbol a γ) ↔
      ∀ j, 0 < a j → γ j ≤ 2 := by
  constructor
  · intro h j hj
    by_contra hn
    exact (mixed_not_negative_above_two a γ hγ0 j hj (lt_of_not_ge hn)) h
  · intro hactive
    exact (FourierCovarianceCriterion.symbol_iff _
      (AnisotropicStableGamma.anisotropic_zero a γ hγ0)
      (AnisotropicStableGamma.anisotropic_even a γ)).mp
        (anisotropic_covariance_of_positive_axes a γ ha hγ0 hactive)

theorem anisotropic_covariance_iff_active (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j) :
    CovarianceSymbol (AnisotropicStableGamma.anisotropicSymbol a γ) ↔
      ∀ j, 0 < a j → γ j ≤ 2 := by
  rw [FourierCovarianceCriterion.symbol_iff _
    (AnisotropicStableGamma.anisotropic_zero a γ hγ0)
    (AnisotropicStableGamma.anisotropic_even a γ)]
  exact anisotropic_negative_iff_active a γ ha hγ0

theorem anisotropic_gamma1_iff_active (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j) :
    (∀ f : Fourier, 0 ≤ (synthesis (0 : Space)
      (gammaIter (AnisotropicStableGamma.anisotropicSymbol a γ) 1 f f)).re) ↔
        ∀ j, 0 < a j → γ j ≤ 2 := by
  exact (FourierGammaCriterion.gamma_positive_iff_negative _
    (AnisotropicStableGamma.anisotropic_zero a γ hγ0)
    (AnisotropicStableGamma.anisotropic_even a γ)).trans
      (anisotropic_negative_iff_active a γ ha hγ0)

theorem anisotropic_gamma_of_positive_axes (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j)
    (hactive : ∀ j, 0 < a j → γ j ≤ 2)
    (n : ℕ) (f : Fourier) (x : Space) :
    (synthesis x (gammaIter (AnisotropicStableGamma.anisotropicSymbol a γ) n f f)).im = 0 ∧
      0 ≤ (synthesis x (gammaIter (AnisotropicStableGamma.anisotropicSymbol a γ) n f f)).re :=
  FourierGammaCovariance.gamma_nonnegative _
    (anisotropic_covariance_of_positive_axes a γ ha hγ0 hactive) n f x

end OperatorDerivativeRewrite.Foundation.AnisotropicMixedThreshold
