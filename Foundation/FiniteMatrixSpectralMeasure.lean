import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Actual finite probability measures from a real symmetric matrix and a coordinate vector. -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.FiniteMatrixSpectralMeasure
set_option backward.isDefEq.respectTransparency false
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : Matrix I I ℝ} (hA : A.IsHermitian)

def weight (i j : I) : ℝ := (hA.eigenvectorUnitary i j)^2

theorem weight_nonneg (i j : I) : 0 ≤ weight hA i j := sq_nonneg _

theorem power_entry (i : I) (n : ℕ) :
    (A^n) i i = ∑ j, weight hA i j * (hA.eigenvalues j)^n := by
  have hp : A^n = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal (fun j => (hA.eigenvalues j)^n)) := by
    calc
      A^n = (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)))^n :=
        congrArg (fun M : Matrix I I ℝ => M^n) hA.spectral_theorem
      _ = _ := by rw [← map_pow, Matrix.diagonal_pow]; rfl
  rw [hp, Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro j _
  unfold weight
  ring

theorem weight_sum (i : I) : ∑ j, weight hA i j = 1 := by
  simpa only [pow_zero, mul_one, Matrix.one_apply_eq] using (power_entry hA i 0).symm

def law (i : I) : Measure ℝ :=
  Measure.sum fun j => ENNReal.ofReal (weight hA i j) • Measure.dirac (hA.eigenvalues j)

instance law_probability (i : I) : IsProbabilityMeasure (law hA i) := by
  constructor
  rw [law, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => weight_nonneg hA i j), weight_sum]
  norm_num

theorem law_integrable (i : I) (f : ℝ → ℝ) : Integrable f (law hA i) := by
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  exact (hasSum_fintype _).summable

theorem law_integral (i : I) (f : ℝ → ℝ) :
    (∫ x, f x ∂law hA i) = ∑ j, weight hA i j * f (hA.eigenvalues j) := by
  rw [law, integral_sum_dirac_eq_tsum (fun _ => ENNReal.ofReal_ne_top)
    (hasSum_fintype _).summable, tsum_fintype]
  simp only [ENNReal.toReal_ofReal (weight_nonneg hA i _), smul_eq_mul]

theorem law_moment (i : I) (n : ℕ) :
    (∫ x : ℝ, x^n ∂law hA i) = (A^n) i i := by
  rw [law_integral, power_entry]

end OperatorDerivativeRewrite.Foundation.FiniteMatrixSpectralMeasure
