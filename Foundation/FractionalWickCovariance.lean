import Foundation.FractionalGaussianProcess
import Foundation.GaussianTimeSpaceHermite

/-! Hadamard covariance powers realized by genuine Gaussian Wick polynomials.
This identifies Gram matrices, not fractional-time generators or their domains. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.FractionalWickCovariance
open FractionalGaussianProcess FractionalSpectralGeometry FractionalSpectralKernel
open InfiniteGaussian GaussianTimeSpaceHermite SeparableHilbertEmbedding

attribute [local instance] spectralSpace_secondCountable

variable (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)

def cylinder (t : ℝ≥0) (n : ℕ) : polynomialCylindricalDomain :=
  wick (direction H hH0 hH1 t) n

theorem direction_inner (s t : ℝ≥0) :
    inner ℝ (direction H hH0 hH1 s) (direction H hH0 hH1 t) = covariance H s t := by
  unfold direction
  rw [(hilbertEmbedding SpectralSpace).inner_map_map, normalized_inner]

theorem cylinder_inner (s t : ℝ≥0) (n m : ℕ) :
    inner ℝ (cylinder H hH0 hH1 s n : GaussianL2) (cylinder H hH0 hH1 t m : GaussianL2) =
      if n = m then (n.factorial : ℝ) * (covariance H s t)^n else 0 := by
  rw [cylinder, cylinder, wick_inner, direction_inner]

theorem cylinder_centered (t : ℝ≥0) (n : ℕ) :
    inner ℝ gaussianOne (cylinder H hH0 hH1 t (n+1) : GaussianL2) = 0 :=
  wick_centered _ _

theorem cylinder_derivative_graph (t : ℝ≥0) (n : ℕ) :
    ((cylinder H hH0 hH1 t (n+1) : GaussianL2),
      (n+1 : ℝ) • scalarTensor (direction H hH0 hH1 t)
        (cylinder H hH0 hH1 t n : GaussianL2)) ∈ closedCylindricalDerivative.graph := by
  have hg := closedCylindricalDerivative_core_graph (cylinder H hH0 hH1 t (n+1))
  change (_, polynomialDerivative (core _ _ (n+1))) ∈ _ at hg
  rw [core_derivative] at hg
  exact hg

theorem finite_sum_norm_sq {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) (c : ι → ℝ) (n : ℕ) :
    ‖∑ i, c i • (cylinder H hH0 hH1 (t i) n : GaussianL2)‖^2 =
      (n.factorial : ℝ) * ∑ i, ∑ j, c i * c j * (covariance H (t i) (t j))^n := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right,
    cylinder_inner, ite_true, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [covariance_symm H (t j) (t i)]
  ring

end OperatorDerivativeRewrite.Foundation.FractionalWickCovariance
