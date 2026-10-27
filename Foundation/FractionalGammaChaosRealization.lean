import Foundation.GaussianTimeSpaceHermite
import Foundation.FractionalGaussianProcess
import Foundation.FiniteStableGamma
import Foundation.GaussianDeterministicAdjointDomain
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open scoped NNReal
/-! Finite stable Gamma energies realized by factorial-normalized Gaussian Wick
chaos. Complex coefficients use a real Hilbert sum of real and imaginary parts.
This is a Gram realization, not an identification of stable and Gaussian
generators or a completed complex tensor-product construction. The derivative
identity is first-order only; the deterministic adjoint kills other sectors. -/
namespace OperatorDerivativeRewrite.Foundation.FractionalGammaChaosRealization
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian GaussianTimeSpaceHermite

def normalizedWick (h : CoefficientSpace) (n : ℕ) : GaussianL2 :=
  (Real.sqrt (n.factorial : ℝ))⁻¹ • (wick h n : GaussianL2)

theorem normalizedWick_inner (h k : CoefficientSpace) (n : ℕ) :
    inner ℝ (normalizedWick h n) (normalizedWick k n) = (inner ℝ h k)^n := by
  have hp : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have he := Real.sq_sqrt hp.le
  simp [normalizedWick, real_inner_smul_left, real_inner_smul_right, wick_inner]
  field_simp
  rw [he]

def realLift {ι : Type*} [Fintype ι] (h : ι → CoefficientSpace) (n : ℕ)
    (b : ι → ℝ) : GaussianL2 := ∑ i, b i • normalizedWick (h i) n

theorem realLift_norm_sq {ι : Type*} [Fintype ι] (h : ι → CoefficientSpace)
    (n : ℕ) (b : ι → ℝ) :
    ‖realLift h n b‖^2 = ∑ i, ∑ j, b i*b j*(inner ℝ (h i) (h j))^n := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [realLift, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    normalizedWick_inner]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm (h j) (h i)]
  ring

theorem direction_covariance (H : ℝ) (h0 : 0 < H) (h1 : H < 1) (s t : ℝ≥0) :
    inner ℝ (FractionalGaussianProcess.direction H h0 h1 s)
      (FractionalGaussianProcess.direction H h0 h1 t) =
      FractionalSpectralGeometry.covariance H s t := by
  have h := FractionalGaussianProcess.process_covariance H h0 h1 s t
  rw [FractionalGaussianProcess.process, FractionalGaussianProcess.process,
    FractionalGaussianProcess.value, FractionalGaussianProcess.value,
    firstChaos_covariance] at h
  simpa [FractionalSpectralGeometry.covariance, abs_of_nonneg s.coe_nonneg,
    abs_of_nonneg t.coe_nonneg] using h

abbrev RealImagGaussian := PiLp 2 (fun _ : Fin 2 => GaussianL2)

/-- Real and imaginary components, with the Hilbert sum norm rather than a sup norm. -/
def complexLift {ι : Type*} [Fintype ι] (h : ι → CoefficientSpace) (n : ℕ)
    (b : ι → ℂ) : RealImagGaussian :=
  WithLp.toLp 2 ![realLift h n (fun i => (b i).re), realLift h n (fun i => (b i).im)]

theorem complexLift_norm_sq {ι : Type*} [Fintype ι] (h : ι → CoefficientSpace)
    (n : ℕ) (b : ι → ℂ) :
    ‖complexLift h n b‖^2 =
      (FiniteStableGamma.ComplexEnergy.energy
        (Matrix.of fun i j => (inner ℝ (h i) (h j))^n) b).re := by
  rw [FiniteStableGamma.ComplexEnergy.energy_re]
  simp [complexLift, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, realLift_norm_sq]

theorem fractional_complexLift_norm_sq {ι : Type*} [Fintype ι]
    (H : ℝ) (h0 : 0 < H) (h1 : H < 1) (t : ι → ℝ≥0) (n : ℕ) (b : ι → ℂ) :
    ‖complexLift (fun i => FractionalGaussianProcess.direction H h0 h1 (t i)) n b‖^2 =
      (FiniteStableGamma.ComplexEnergy.energy
        (FractionalCovarianceMatrices.covariancePower H (fun i => (t i : ℝ)) n) b).re := by
  rw [complexLift_norm_sq]
  simp only [direction_covariance]
  rfl

open FiniteFourierDifferentialTrace FiniteFourierSynthesis

theorem actual_gamma_realization_re {ι : Type*} [Fintype ι]
    (H : ℝ) (h0 : 0 < H) (h1 : H < 1) (t : ι → ℝ≥0)
    (k : ι → Wave) (ht : ∀ i, (k i 0 : ℝ) = (t i : ℝ))
    (n : ℕ) (c : ι → ℂ) (x : Space) :
    ‖complexLift (fun i => FractionalGaussianProcess.direction H h0 h1 (t i)) n
      (fun i => c i*character (k i) x)‖^2 =
      (synthesis x (FiniteStableGamma.Core.gammaIter (FiniteStableGamma.Core.stableSymbol (2*H)) n
        (∑ i, AddMonoidAlgebra.single (k i) (c i))
        (∑ i, AddMonoidAlgebra.single (k i) (c i)))).re := by
  rw [fractional_complexLift_norm_sq, FiniteStableGamma.Bridge.stable_gamma_energy]
  simp only [show 2*H/2 = H by ring, ht]

theorem actual_gamma_realization {ι : Type*} [Fintype ι]
    (H : ℝ) (h0 : 0 < H) (h1 : H < 1) (t : ι → ℝ≥0)
    (k : ι → Wave) (ht : ∀ i, (k i 0 : ℝ) = (t i : ℝ))
    (n : ℕ) (c : ι → ℂ) (x : Space) :
    Complex.ofReal (‖complexLift (fun i => FractionalGaussianProcess.direction H h0 h1 (t i)) n
      (fun i => c i*character (k i) x)‖^2) =
      synthesis x (FiniteStableGamma.Core.gammaIter (FiniteStableGamma.Core.stableSymbol (2*H)) n
        (∑ i, AddMonoidAlgebra.single (k i) (c i))
        (∑ i, AddMonoidAlgebra.single (k i) (c i))) := by
  apply Complex.ext
  · exact actual_gamma_realization_re H h0 h1 t k ht n c x
  · rw [FiniteStableGamma.Bridge.stable_gamma_energy,
      FiniteStableGamma.ComplexEnergy.covariance_energy_real]
    rfl

theorem normalizedWick_mem_sector (h : CoefficientSpace) (n : ℕ) :
    normalizedWick h n ∈ GaussianNumberSectors.sector n :=
  (GaussianNumberSectors.sector n).smul_mem _ (IBMCubicFirstChaos.wick_mem_sector h n)

theorem realLift_mem_sector {ι : Type*} [Fintype ι] (h : ι → CoefficientSpace)
    (n : ℕ) (b : ι → ℝ) : realLift h n b ∈ GaussianNumberSectors.sector n := by
  apply (GaussianNumberSectors.sector n).sum_mem
  intro i hi
  exact (GaussianNumberSectors.sector n).smul_mem _ (normalizedWick_mem_sector (h i) n)

theorem normalizedWick_one (h : CoefficientSpace) :
    normalizedWick h 1 = firstChaosEmbedding h := by
  simp [normalizedWick, IBMCubicFirstChaos.wick_one_eq_embedding]

theorem realLift_one {ι : Type*} [Fintype ι] (h : ι → CoefficientSpace) (b : ι → ℝ) :
    realLift h 1 b = firstChaosEmbedding (∑ i, b i • h i) := by
  simp [realLift, normalizedWick_one, map_sum]

theorem realLift_deterministic_derivative {ι : Type*} [Fintype ι]
    (h : ι → CoefficientSpace) (b : ι → ℝ) :
    GaussianDeterministicAdjointDomain.deterministicDerivative (realLift h 1 b) =
      ∑ i, b i • h i := by
  rw [realLift_one, GaussianDeterministicAdjointDomain.deterministic_first]

theorem higherLift_deterministic_derivative {ι : Type*} [Fintype ι]
    (h : ι → CoefficientSpace) (n : ℕ) (hn : n ≠ 1) (b : ι → ℝ) :
    GaussianDeterministicAdjointDomain.deterministicDerivative (realLift h n b) = 0 := by
  simp [realLift, normalizedWick, map_sum,
    GaussianDeterministicAdjointDomain.deterministic_wick_other _ n hn]

theorem normalizedWick_orthogonal (h k : CoefficientSpace) (n m : ℕ)
    (hnm : n ≠ m) : inner ℝ (normalizedWick h n) (normalizedWick k m) = 0 := by
  simp [normalizedWick, real_inner_smul_left, real_inner_smul_right, wick_inner, hnm]

theorem complexLift_one_derivative_energy {ι : Type*} [Fintype ι]
    (h : ι → CoefficientSpace) (b : ι → ℂ) :
    ‖complexLift h 1 b‖^2 =
      ‖GaussianDeterministicAdjointDomain.deterministicDerivative
        (realLift h 1 (fun i => (b i).re))‖^2 +
      ‖GaussianDeterministicAdjointDomain.deterministicDerivative
        (realLift h 1 (fun i => (b i).im))‖^2 := by
  rw [realLift_deterministic_derivative, realLift_deterministic_derivative]
  simp only [complexLift, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [realLift_one, realLift_one, firstChaosEmbedding.norm_map,
    firstChaosEmbedding.norm_map]

theorem realLift_orthogonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (h : ι → CoefficientSpace) (k : κ → CoefficientSpace)
    (n m : ℕ) (hnm : n ≠ m) (b : ι → ℝ) (c : κ → ℝ) :
    inner ℝ (realLift h n b) (realLift k m c) = 0 := by
  simp [realLift, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    normalizedWick_orthogonal _ _ n m hnm]

/-- An unnormalized second Wick power has a factorial discrepancy even in one direction. -/
theorem wick_two_normalization_obstruction (h : CoefficientSpace) (hh : ‖h‖ = 1) :
    ‖(wick h 2 : GaussianL2)‖^2 = 2 ∧
    ‖normalizedWick h 2‖^2 = 1 := by
  constructor
  · norm_num [wick_norm_sq, hh]
  · rw [← real_inner_self_eq_norm_sq, normalizedWick_inner,
      real_inner_self_eq_norm_sq, hh]
    norm_num

end OperatorDerivativeRewrite.Foundation.FractionalGammaChaosRealization
