import Foundation.FiniteSchoenberg
import Foundation.FourierGammaCovariance

/-! Positive finite heat matrices make the finite Fourier heat action send
algebraic squares to pointwise nonnegative real trigonometric polynomials.
This is a finite-core statement; a completed
positive Markov semigroup or convolution probability law is not inferred. -/
open scoped ComplexConjugate BigOperators
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteHeatSquarePositivity
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierReality
open FiniteStableGamma.Core FiniteStableGamma.ComplexEnergy
open FourierGammaCovariance FiniteSchoenberg FourierCovarianceCriterion

def heatAction (ψ : Wave → ℝ) (t : ℝ) : Fourier →ₗ[ℂ] Fourier :=
  (Finsupp.linearCombination ℂ (fun k : Wave =>
    (Real.exp (-t*ψ k) : ℂ) • (AddMonoidAlgebra.single k 1 : Fourier))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem heatAction_single (ψ : Wave → ℝ) (t : ℝ) (k : Wave) (c : ℂ) :
    heatAction ψ t (AddMonoidAlgebra.single k c) =
      AddMonoidAlgebra.single k ((Real.exp (-t*ψ k) : ℂ)*c) := by
  simp [heatAction, Finsupp.linearCombination_single, mul_comm]

theorem heat_square_energy {ι : Type*} [Fintype ι]
    (ψ : Wave → ℝ) (t : ℝ) (k : ι → Wave) (c : ι → ℂ) (x : Space) :
    synthesis x (heatAction ψ t
      (reflection (∑ i, AddMonoidAlgebra.single (k i) (c i)) *
        (∑ i, AddMonoidAlgebra.single (k i) (c i)))) =
      energy (fun i j => Real.exp (-t*ψ (k j-k i)))
        (fun i => c i * character (k i) x) := by
  change synthesis x (heatAction ψ t
    (gammaIter ψ 0 (∑ i, AddMonoidAlgebra.single (k i) (c i))
      (∑ i, AddMonoidAlgebra.single (k i) (c i)))) = _
  rw [gammaIter_finite]
  simp only [map_sum, synthesis_single, heatAction_single]
  unfold energy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul, sub_eq_add_neg, character_add, character_neg]
  ring

theorem heat_square_nonnegative (ψ : Wave → ℝ)
    (hψ : CovarianceSymbol ψ) (t : ℝ) (ht : 0 ≤ t)
    (f : Fourier) (x : Space) :
    (synthesis x (heatAction ψ t (reflection f * f))).im = 0 ∧
      0 ≤ (synthesis x (heatAction ψ t (reflection f * f))).re := by
  classical
  have hf : (∑ k : f.coeff.support,
      AddMonoidAlgebra.single k.val (f.coeff k.val)) = f :=
    (Finset.sum_attach f.coeff.support
      (fun k => AddMonoidAlgebra.single k (f.coeff k))).trans
        (AddMonoidAlgebra.sum_coeff_single f)
  rw [← hf]
  rw [heat_square_energy]
  exact energy_nonnegative _
    (heat_multiplier_psd_of_covariance ψ hψ t ht
      (fun k : f.coeff.support => k.val)) _

theorem heat_square_real_energy_at_zero {ι : Type} [Fintype ι]
    (ψ : Wave → ℝ) (t : ℝ) (k : ι → Wave) (w : ι → ℝ) :
    (synthesis 0 (heatAction ψ t
      (reflection (∑ i, AddMonoidAlgebra.single (k i) (w i : ℂ)) *
        (∑ i, AddMonoidAlgebra.single (k i) (w i : ℂ))))).re =
      expEnergy (fun i j => ψ (k j-k i)) w t := by
  rw [heat_square_energy]
  simp [energy, expEnergy, character, phase, ← Complex.ofReal_exp]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem heat_square_negative_of_energy {ι : Type} [Fintype ι]
    (ψ : Wave → ℝ) (t : ℝ) (k : ι → Wave) (w : ι → ℝ)
    (h : expEnergy (fun i j => ψ (k j-k i)) w t < 0) :
    (synthesis 0 (heatAction ψ t
      (reflection (∑ i, AddMonoidAlgebra.single (k i) (w i : ℂ)) *
        (∑ i, AddMonoidAlgebra.single (k i) (w i : ℂ))))).re < 0 := by
  rw [heat_square_real_energy_at_zero]
  exact h

theorem heat_square_negative_of_positive_symbol_energy
    (ψ : Wave → ℝ) (k : Fin 3 → Wave) (w : Fin 3 → ℝ)
    (hw : ∑ i, w i = 0)
    (hd : 0 < AnchoredCovariance.energy (fun i j => ψ (k j-k i)) w) :
    ∃ t : ℝ, 0 < t ∧
      (synthesis 0 (heatAction ψ t
        (reflection (∑ i, AddMonoidAlgebra.single (k i) (w i : ℂ)) *
          (∑ i, AddMonoidAlgebra.single (k i) (w i : ℂ))))).re < 0 := by
  obtain ⟨t, ht, hn⟩ := FiniteBochnerObstruction.expEnergy_eventually_negative
    (fun i j => ψ (k j-k i)) w hw hd
  exact ⟨t, ht, heat_square_negative_of_energy ψ t k w hn⟩

theorem anisotropic_heat_square_nonnegative (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j)
    (hactive : ∀ j, 0 < a j → γ j ≤ 2)
    (t : ℝ) (ht : 0 ≤ t) (f : Fourier) (x : Space) :
    (synthesis x (heatAction (AnisotropicStableGamma.anisotropicSymbol a γ) t
      (reflection f * f))).im = 0 ∧
    0 ≤ (synthesis x (heatAction (AnisotropicStableGamma.anisotropicSymbol a γ) t
      (reflection f * f))).re :=
  heat_square_nonnegative _
    (AnisotropicMixedThreshold.anisotropic_covariance_of_positive_axes
      a γ ha hγ0 hactive) t ht f x

theorem anisotropic_heat_square_negative_above_two (a γ : Fin 3 → ℝ)
    (hγ0 : ∀ j, 0 < γ j) (j : Fin 3)
    (ha : 0 < a j) (hγgt : 2 < γ j) :
    ∃ t : ℝ, 0 < t ∧
      (synthesis 0 (heatAction (AnisotropicStableGamma.anisotropicSymbol a γ) t
        (reflection (∑ i, AddMonoidAlgebra.single
          (AnisotropicMixedThreshold.axisTriple j i)
          (AnisotropicStableEndpoint.tripleWeights i : ℂ)) *
          (∑ i, AddMonoidAlgebra.single
            (AnisotropicMixedThreshold.axisTriple j i)
            (AnisotropicStableEndpoint.tripleWeights i : ℂ))))).re < 0 := by
  have hp : (4 : ℝ) < 2^(γ j) := by
    have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hγgt
    norm_num at hh
    exact hh
  have hd : 0 < AnchoredCovariance.energy
      (fun i l => AnisotropicStableGamma.anisotropicSymbol a γ
        (AnisotropicMixedThreshold.axisTriple j l -
          AnisotropicMixedThreshold.axisTriple j i))
      AnisotropicStableEndpoint.tripleWeights := by
    rw [AnisotropicMixedThreshold.mixed_triple_energy a γ hγ0 j]
    exact mul_pos ha (by linarith)
  exact heat_square_negative_of_positive_symbol_energy _ _ _
    AnisotropicStableEndpoint.triple_sum hd

end OperatorDerivativeRewrite.Foundation.FiniteHeatSquarePositivity
