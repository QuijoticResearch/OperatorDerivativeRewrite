import Foundation.FourierGammaComplexCriterion
/-! Anisotropic coordinatewise stable Fourier symbols and their Gamma calculus. -/
open scoped BigOperators
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.AnisotropicStableGamma
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
open FiniteStableGamma.Core FourierCovarianceCriterion FourierGammaCovariance

theorem covariance_zero : CovarianceSymbol (fun _ => 0) := by
  intro ι _ _ k
  have he : (fun i j => kernel (fun _ : Wave => 0) (k i) (k j)) =
      (0 : Matrix ι ι ℝ) := by
    ext i j
    simp [kernel]
  rw [he]
  exact Matrix.PosSemidef.zero

theorem covariance_add (ψ φ : Wave → ℝ)
    (hψ : CovarianceSymbol ψ) (hφ : CovarianceSymbol φ) :
    CovarianceSymbol (fun k => ψ k + φ k) := by
  intro ι _ _ k
  have he : (fun i j => kernel (fun x => ψ x + φ x) (k i) (k j)) =
      (fun i j => kernel ψ (k i) (k j)) +
      (fun i j => kernel φ (k i) (k j)) := by
    ext i j
    change kernel (fun x => ψ x + φ x) (k i) (k j) =
      kernel ψ (k i) (k j) + kernel φ (k i) (k j)
    unfold kernel
    ring
  rw [he]
  exact (hψ _ k).add (hφ _ k)

theorem covariance_scale (a : ℝ) (ha : 0 ≤ a) (ψ : Wave → ℝ)
    (hψ : CovarianceSymbol ψ) :
    CovarianceSymbol (fun k => a * ψ k) := by
  intro ι _ _ k
  have he : (fun i j => kernel (fun x => a * ψ x) (k i) (k j)) =
      a • (fun i j => kernel ψ (k i) (k j)) := by
    ext i j
    change kernel (fun x => a * ψ x) (k i) (k j) =
      a * kernel ψ (k i) (k j)
    unfold kernel
    ring
  rw [he]
  exact (hψ _ k).smul ha

theorem covariance_sum {α : Type*} (s : Finset α) (ψ : α → Wave → ℝ)
    (h : ∀ j ∈ s, CovarianceSymbol (ψ j)) :
    CovarianceSymbol (fun k => ∑ j ∈ s, ψ j k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using covariance_zero
  | @insert j s hj ih =>
    have h' : CovarianceSymbol (fun k => ψ j k + ∑ i ∈ s, ψ i k) := by
      apply covariance_add
      · exact h j (Finset.mem_insert_self j s)
      · apply ih
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert hj] using h'

def axisSymbol (γ : ℝ) (j : Fin 3) (k : Wave) : ℝ := |(k j : ℝ)|^γ

theorem axis_kernel (γ : ℝ) (j : Fin 3) (k l : Wave) :
    kernel (axisSymbol γ j) k l =
      FractionalSpectralGeometry.covariance (γ/2) (k j) (l j) := by
  unfold kernel axisSymbol FractionalSpectralGeometry.covariance
  have he : 2*(γ/2) = γ := by ring
  simp [he, Pi.sub_apply, Int.cast_sub]

theorem axis_covariance (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (j : Fin 3) :
    CovarianceSymbol (axisSymbol γ j) := by
  intro ι _ _ k
  have h := FractionalCovarianceMatrices.covarianceMatrix_posSemidef
    (γ/2) (by linarith) (by linarith) (fun i => (k i j : ℝ))
  have he : (fun i j' => kernel (axisSymbol γ j) (k i) (k j')) =
      FractionalCovarianceMatrices.covarianceMatrix (γ/2)
        (fun i => (k i j : ℝ)) := by
    funext i j'
    exact axis_kernel γ j (k i) (k j')
  rw [he]
  exact h

def anisotropicSymbol (a : Fin 3 → ℝ) (γ : Fin 3 → ℝ) (k : Wave) : ℝ :=
  ∑ j, a j * axisSymbol (γ j) j k

theorem anisotropic_covariance (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j) (hγ2 : ∀ j, γ j < 2) :
    CovarianceSymbol (anisotropicSymbol a γ) := by
  have h := covariance_sum (Finset.univ : Finset (Fin 3))
    (fun j k => a j * axisSymbol (γ j) j k) (by
      intro j hj
      exact covariance_scale (a j) (ha j) _
        (axis_covariance (γ j) (hγ0 j) (hγ2 j) j))
  change CovarianceSymbol (fun k => ∑ j, a j * axisSymbol (γ j) j k)
  exact h

theorem anisotropic_zero (a γ : Fin 3 → ℝ)
    (hγ0 : ∀ j, 0 < γ j) : anisotropicSymbol a γ 0 = 0 := by
  unfold anisotropicSymbol
  apply Finset.sum_eq_zero
  intro j hj
  simp [axisSymbol, Real.zero_rpow (ne_of_gt (hγ0 j))]

theorem anisotropic_even (a γ : Fin 3 → ℝ) (k : Wave) :
    anisotropicSymbol a γ (-k) = anisotropicSymbol a γ k := by
  unfold anisotropicSymbol
  apply Finset.sum_congr rfl
  intro j hj
  simp [axisSymbol]

theorem anisotropic_negative (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j) (hγ2 : ∀ j, γ j < 2) :
    NegativeSymbol (anisotropicSymbol a γ) := by
  exact (symbol_iff _ (anisotropic_zero a γ hγ0)
    (anisotropic_even a γ)).mp (anisotropic_covariance a γ ha hγ0 hγ2)

theorem anisotropic_gamma (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j) (hγ2 : ∀ j, γ j < 2)
    (n : ℕ) (f : Fourier) (x : Space) :
    (synthesis x (gammaIter (anisotropicSymbol a γ) n f f)).im = 0 ∧
      0 ≤ (synthesis x (gammaIter (anisotropicSymbol a γ) n f f)).re :=
  gamma_nonnegative _ (anisotropic_covariance a γ ha hγ0 hγ2) n f x

def halfCauchy (k : Wave) : ℝ := (1/2 : ℝ) * stableSymbol 1 k

theorem half_cauchy_covariance : CovarianceSymbol halfCauchy := by
  change CovarianceSymbol (fun k => (1/2 : ℝ) * stableSymbol 1 k)
  exact covariance_scale (1/2) (by norm_num) _
    (stable_covariance 1 (by norm_num) (by norm_num))

def firstWave : Wave := fun _ => 1
def firstMode : Fourier := AddMonoidAlgebra.single firstWave 1

theorem half_mode_gamma (n : ℕ) :
    synthesis (0 : Space) (gammaIter halfCauchy n firstMode firstMode) =
      ((1/2 : ℝ)^n : ℂ) := by
  unfold firstMode
  rw [gammaIter_single, synthesis_single]
  have hk : kernel halfCauchy firstWave firstWave = 1/2 := by
    norm_num [kernel, halfCauchy, stableSymbol, firstWave]
  simp [hk, character_zero]

theorem half_gamma_two_below_one :
    (synthesis (0 : Space) (gammaIter halfCauchy 2 firstMode firstMode)).re <
      (synthesis (0 : Space) (gammaIter halfCauchy 1 firstMode firstMode)).re := by
  rw [half_mode_gamma, half_mode_gamma]
  norm_num

end OperatorDerivativeRewrite.Foundation.AnisotropicStableGamma
