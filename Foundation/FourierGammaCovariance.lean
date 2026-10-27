import Foundation.FourierCovarianceCriterion
open scoped BigOperators ComplexConjugate
/-! Pointwise positivity of every integer Fourier Gamma iteration.
The actual generator recursion is identified with covariance Hadamard powers.
The domain is the finite Fourier algebra; no completed domain is asserted.
No positive curvature constant, spectral gap or process is inferred. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourierGammaCovariance
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierReality
open FiniteStableGamma.Core FiniteStableGamma.ComplexEnergy FourierCovarianceCriterion

theorem power_psd {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hM : M.PosSemidef) (n : ℕ) : Matrix.PosSemidef (fun i j => M i j ^ n) := by
  induction n with
  | zero =>
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j; change star (M j i ^ 0) = M i j ^ 0; simp
    · intro c
      have hp : 0 ≤ (∑ i, c i)^2 := sq_nonneg _
      simpa [dotProduct, Matrix.mulVec, pow_two, Finset.sum_mul] using hp
  | succ n hn =>
    have he : (fun i j => M i j ^ (n+1)) =
        Matrix.hadamard (fun i j => M i j ^ n) M := by
      ext i j
      change M i j ^ (n+1) = M i j ^ n * M i j
      exact pow_succ _ _
    rw [he]
    exact hn.hadamard hM

theorem energy_nonnegative {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hM : M.PosSemidef) (b : ι → ℂ) :
    (energy M b).im = 0 ∧ 0 ≤ (energy M b).re := by
  constructor
  · apply energy_real
    intro i j
    simpa only [star_trivial] using (hM.1.apply i j).symm
  · rw [energy_re]
    have hr := hM.dotProduct_mulVec_nonneg (fun i => (b i).re)
    have hi := hM.dotProduct_mulVec_nonneg (fun i => (b i).im)
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_left_comm, mul_comm] at hr hi ⊢
    exact add_nonneg hr hi

theorem gamma_energy {ι : Type*} [Fintype ι] (ψ : Wave → ℝ) (n : ℕ)
    (k : ι → Wave) (c : ι → ℂ) (x : Space) :
    synthesis x (gammaIter ψ n (∑ i, AddMonoidAlgebra.single (k i) (c i))
      (∑ i, AddMonoidAlgebra.single (k i) (c i))) =
      energy (fun i j => kernel ψ (k i) (k j)^n)
        (fun i => c i * character (k i) x) := by
  rw [gammaIter_finite]
  simp only [map_sum, synthesis_single]
  unfold energy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.ofReal_pow, map_mul, sub_eq_add_neg, character_add, character_neg]
  ring

theorem gamma_finite_nonnegative {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : Wave → ℝ) (hψ : CovarianceSymbol ψ) (n : ℕ)
    (k : ι → Wave) (c : ι → ℂ) (x : Space) :
    let z := synthesis x (gammaIter ψ n (∑ i, AddMonoidAlgebra.single (k i) (c i))
      (∑ i, AddMonoidAlgebra.single (k i) (c i)))
    z.im = 0 ∧ 0 ≤ z.re := by
  dsimp only
  rw [gamma_energy]
  exact energy_nonnegative _ (power_psd _ (hψ _ k) n) _

theorem gamma_nonnegative (ψ : Wave → ℝ) (hψ : CovarianceSymbol ψ)
    (n : ℕ) (f : Fourier) (x : Space) :
    (synthesis x (gammaIter ψ n f f)).im = 0 ∧
      0 ≤ (synthesis x (gammaIter ψ n f f)).re := by
  classical
  have hf : (∑ k : f.coeff.support, AddMonoidAlgebra.single k.val (f.coeff k.val)) = f :=
    (Finset.sum_attach f.coeff.support (fun k => AddMonoidAlgebra.single k (f.coeff k))).trans
      (AddMonoidAlgebra.sum_coeff_single f)
  have h := gamma_finite_nonnegative ψ hψ n
    (fun k : f.coeff.support => k.val) (fun k => f.coeff k.val) x
  simpa only [hf] using h

theorem negative_symbol_gamma (ψ : Wave → ℝ) (h0 : ψ 0 = 0)
    (he : ∀ k, ψ (-k) = ψ k) (hψ : NegativeSymbol ψ)
    (n : ℕ) (f : Fourier) (x : Space) :
    (synthesis x (gammaIter ψ n f f)).im = 0 ∧
      0 ≤ (synthesis x (gammaIter ψ n f f)).re :=
  gamma_nonnegative ψ ((symbol_iff ψ h0 he).mpr hψ) n f x

end OperatorDerivativeRewrite.Foundation.FourierGammaCovariance
