import Foundation.IBMJointMollifierGaussian
import Foundation.FractionalControlledEstimate
import Foundation.GaussianTimeSpaceHermite

/-! Gaussian mixed moments derived from the verified source adjoint/Wick calculus. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMGaussianSteinMoments
open InfiniteGaussian GaussianQuadraticIncrement
open FractionalControlledEstimate GaussianDeterministicGraphCore
open GaussianTimeSpaceHermite
open IBMJointMollifierGaussian FractionalSpectralKernel
open IBMContinuousScenery
open SeparableHilbertEmbedding
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

theorem firstChaos_square_inner (h k : CoefficientSpace) :
    inner ℝ (square h) (square k) =
      ‖h‖^2 * ‖k‖^2 + 2 * (inner ℝ h k)^2 := by
  rw [square, square]
  simp only [inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [centeredSquare_inner,
    show inner ℝ (centeredSquare h : GaussianL2) gaussianOne = 0 by
      rw [real_inner_comm]
      exact centeredSquare_centered h,
    centeredSquare_centered k, gaussianOne_inner_self]
  norm_num
  ring

theorem firstChaos_square_product (h k : CoefficientSpace) :
    (∫ ω, (firstChaosEmbedding h ω)^2 * (firstChaosEmbedding k ω)^2
      ∂gaussianProduct) =
      ‖h‖^2 * ‖k‖^2 + 2 * (inner ℝ h k)^2 := by
  rw [← firstChaos_square_inner h k, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [square_coeFn h, square_coeFn k] with ω hh hk
  rw [hh, hk]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem value_three (z t : ℝ) : value 3 z t = z^3 - 3*t*z := by
  rw [show (3 : ℕ) = 1 + 2 by norm_num, value_recursion]
  rw [value_two, value_one]
  ring

def cube (h : CoefficientSpace) : GaussianL2 :=
  (wick h 3 : GaussianL2) +
    (3 * ‖h‖^2 : ℝ) • (wick h 1 : GaussianL2)

theorem cube_coeFn (h : CoefficientSpace) :
    cube h =ᵐ[gaussianProduct] fun ω => (firstChaosEmbedding h ω)^3 := by
  filter_upwards [Lp.coeFn_add (wick h 3 : GaussianL2)
      ((3 * ‖h‖^2 : ℝ) • (wick h 1 : GaussianL2)),
    Lp.coeFn_smul (3 * ‖h‖^2 : ℝ) (wick h 1 : GaussianL2),
    core_coeFn h (‖h‖^2) 3, core_coeFn h (‖h‖^2) 1] with ω ha hs h3 h1
  rw [cube, ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  change (wick h 3 : GaussianL2) ω = _ at h3
  change (wick h 1 : GaussianL2) ω = _ at h1
  rw [h3, h1]
  simp only [value_three, value_one]
  ring

theorem firstChaos_cube_first_inner (h k : CoefficientSpace) :
    inner ℝ (cube h) (wick k 1 : GaussianL2) =
      3 * ‖h‖^2 * inner ℝ h k := by
  rw [cube, inner_add_left, real_inner_smul_left,
    wick_inner, wick_inner]
  norm_num

theorem firstChaos_cube_first_product (h k : CoefficientSpace) :
    (∫ ω, (firstChaosEmbedding h ω)^3 * firstChaosEmbedding k ω
      ∂gaussianProduct) =
      3 * ‖h‖^2 * inner ℝ h k := by
  rw [← firstChaos_cube_first_inner h k, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cube_coeFn h, core_coeFn k (‖k‖^2) 1] with ω hc hk
  rw [hc]
  change (wick k 1 : GaussianL2) ω = _ at hk
  rw [hk]
  simp only [value_one, RCLike.inner_apply, conj_trivial]
  ring

def tripleCoefficient (n : ℕ) (x : ℝ) (i : Fin 3) : CoefficientSpace :=
  hilbertEmbedding SpectralSpace (wholeLineDirection (derivativeKernel n i) x)

theorem gaussianTriple_eq_firstChaos (n : ℕ) (x : ℝ) (i : Fin 3) :
    gaussianTriple n x i = firstChaosEmbedding (tripleCoefficient n x i) := rfl

theorem tripleCoefficient_inner (n : ℕ) (x : ℝ) (i j : Fin 3) :
    inner ℝ (tripleCoefficient n x i) (tripleCoefficient n x j) =
      cov[gaussianTriple n x i, gaussianTriple n x j; gaussianProduct] := by
  rw [gaussianTriple_covariance]
  exact (hilbertEmbedding SpectralSpace).inner_map_map _ _

theorem gaussianTriple_square_product (n : ℕ) (x : ℝ) (i j : Fin 3) :
    (∫ ω, (gaussianTriple n x i ω)^2 * (gaussianTriple n x j ω)^2
      ∂gaussianProduct) =
      cov[gaussianTriple n x i, gaussianTriple n x i; gaussianProduct] *
        cov[gaussianTriple n x j, gaussianTriple n x j; gaussianProduct] +
        2 * cov[gaussianTriple n x i, gaussianTriple n x j; gaussianProduct]^2 := by
  rw [gaussianTriple_eq_firstChaos, gaussianTriple_eq_firstChaos,
    firstChaos_square_product]
  simp only [firstChaos_covariance, real_inner_self_eq_norm_sq]

theorem gaussianTriple_cube_first_product (n : ℕ) (x : ℝ) (i j : Fin 3) :
    (∫ ω, (gaussianTriple n x i ω)^3 * gaussianTriple n x j ω
      ∂gaussianProduct) =
      3 * cov[gaussianTriple n x i, gaussianTriple n x i; gaussianProduct] *
        cov[gaussianTriple n x i, gaussianTriple n x j; gaussianProduct] := by
  rw [gaussianTriple_eq_firstChaos, gaussianTriple_eq_firstChaos,
    firstChaos_cube_first_product]
  simp only [firstChaos_covariance, real_inner_self_eq_norm_sq]

/-- The finite-mollifier IBM correction has the predicted one-quarter
expectation coefficient for the quartic test function `f(z)=z⁴/24` on the
strict positive interior. Both moments come from the genuine Gaussian source
adjoint/Wick pairing, and the covariance cancellation is the concrete one. -/
theorem concrete_quartic_stein_cancellation (n : ℕ) (x : ℝ)
    (hbulk : (IBMMollifier.bump n).rOut < x) :
    (1 / 2 : ℝ) *
        (∫ ω, (gaussianTriple n x 0 ω)^2 * (gaussianTriple n x 1 ω)^2
          ∂gaussianProduct) +
      (1 / 6 : ℝ) *
        (∫ ω, (gaussianTriple n x 0 ω)^3 * gaussianTriple n x 2 ω
          ∂gaussianProduct) = 1 / 4 := by
  rw [gaussianTriple_square_product n x 0 1,
    gaussianTriple_cube_first_product n x 0 2]
  have hc := gaussianTriple_interior_covariance_half n x hbulk
  have hz := gaussianTriple_interior_covariance_cancellation n x hbulk
  have hm := congrArg (fun z : ℝ =>
      cov[gaussianTriple n x 0, gaussianTriple n x 0; gaussianProduct] * z) hz
  rw [hc]
  nlinarith

private theorem triple_square_memLp (n : ℕ) (x : ℝ) (i : Fin 3) :
    MemLp (fun ω => (gaussianTriple n x i ω)^2) 2 gaussianProduct := by
  rw [gaussianTriple_eq_firstChaos]
  exact (Lp.memLp (square (tripleCoefficient n x i))).ae_eq
    (square_coeFn (tripleCoefficient n x i))

private theorem triple_cube_memLp (n : ℕ) (x : ℝ) (i : Fin 3) :
    MemLp (fun ω => (gaussianTriple n x i ω)^3) 2 gaussianProduct := by
  rw [gaussianTriple_eq_firstChaos]
  exact (Lp.memLp (cube (tripleCoefficient n x i))).ae_eq
    (cube_coeFn (tripleCoefficient n x i))

private theorem triple_first_memLp (n : ℕ) (x : ℝ) (i : Fin 3) :
    MemLp (gaussianTriple n x i) 2 gaussianProduct := by
  rw [gaussianTriple_eq_firstChaos]
  exact Lp.memLp _

/-- Actual finite Gaussian expectation of the quartic mollified IBM
correction, including integrability of both nonlinear summands. -/
theorem concrete_quartic_correction_expectation (n : ℕ) (x : ℝ)
    (hbulk : (IBMMollifier.bump n).rOut < x) :
    (∫ ω, (1 / 2 : ℝ) *
        (gaussianTriple n x 0 ω)^2 * (gaussianTriple n x 1 ω)^2 +
        (1 / 6 : ℝ) *
        (gaussianTriple n x 0 ω)^3 * gaussianTriple n x 2 ω
      ∂gaussianProduct) = 1 / 4 := by
  have hi₁ : Integrable (fun ω =>
      (gaussianTriple n x 0 ω)^2 * (gaussianTriple n x 1 ω)^2)
      gaussianProduct :=
    mul_L2_integrable (triple_square_memLp n x 0) (triple_square_memLp n x 1)
  have hi₂ : Integrable (fun ω =>
      (gaussianTriple n x 0 ω)^3 * gaussianTriple n x 2 ω)
      gaussianProduct :=
    mul_L2_integrable (triple_cube_memLp n x 0) (triple_first_memLp n x 2)
  simp only [mul_assoc]
  rw [integral_add (hi₁.const_mul _) (hi₂.const_mul _),
    integral_const_mul, integral_const_mul]
  exact concrete_quartic_stein_cancellation n x hbulk

/-- Exact finite-mollifier quartic correction at every spatial point. The
second and third terms are the boundary departures from bulk cancellation;
no singular limit is inferred from this finite identity. -/
theorem quartic_correction_expectation_all_x (n : ℕ) (x : ℝ) :
    (∫ ω, (1 / 2 : ℝ) *
        (gaussianTriple n x 0 ω)^2 * (gaussianTriple n x 1 ω)^2 +
        (1 / 6 : ℝ) *
        (gaussianTriple n x 0 ω)^3 * gaussianTriple n x 2 ω
      ∂gaussianProduct) =
      (1 / 2 : ℝ) *
        cov[gaussianTriple n x 0, gaussianTriple n x 0; gaussianProduct] *
        (cov[gaussianTriple n x 1, gaussianTriple n x 1; gaussianProduct] +
          cov[gaussianTriple n x 0, gaussianTriple n x 2; gaussianProduct]) +
        cov[gaussianTriple n x 0, gaussianTriple n x 1; gaussianProduct]^2 := by
  have hi₁ : Integrable (fun ω =>
      (gaussianTriple n x 0 ω)^2 * (gaussianTriple n x 1 ω)^2)
      gaussianProduct :=
    mul_L2_integrable (triple_square_memLp n x 0) (triple_square_memLp n x 1)
  have hi₂ : Integrable (fun ω =>
      (gaussianTriple n x 0 ω)^3 * gaussianTriple n x 2 ω)
      gaussianProduct :=
    mul_L2_integrable (triple_cube_memLp n x 0) (triple_first_memLp n x 2)
  simp only [mul_assoc]
  rw [integral_add (hi₁.const_mul _) (hi₂.const_mul _),
    integral_const_mul, integral_const_mul,
    gaussianTriple_square_product n x 0 1,
    gaussianTriple_cube_first_product n x 0 2]
  ring

theorem gaussianTriple_covariance_eq_L2_inner (n : ℕ) (x : ℝ) (i j : Fin 3) :
    cov[gaussianTriple n x i, gaussianTriple n x j; gaussianProduct] =
      inner ℝ (wholeLineScenery (derivativeKernel n i) x)
        (wholeLineScenery (derivativeKernel n j) x) := by
  rw [gaussianTriple_covariance, wholeLineScenery_eq_sourceEmbedding,
    wholeLineScenery_eq_sourceEmbedding, LinearIsometry.inner_map_map]

/-- The finite quartic correction depends only on the first two derivatives
of the actual Gaussian scenery variance. This is valid at the boundary as
well as in the bulk, before any singular limit. -/
theorem quartic_correction_variance_geometry (n : ℕ) (x : ℝ) :
    (∫ ω, (1 / 2 : ℝ) *
        (gaussianTriple n x 0 ω)^2 * (gaussianTriple n x 1 ω)^2 +
        (1 / 6 : ℝ) *
        (gaussianTriple n x 0 ω)^3 * gaussianTriple n x 2 ω
      ∂gaussianProduct) =
      (1 / 4 : ℝ) * (deriv (wholeLineVariance (IBMMollifier.kernel n)) x)^2 +
        (1 / 4 : ℝ) * wholeLineVariance (IBMMollifier.kernel n) x *
          deriv (fun y => deriv (wholeLineVariance (IBMMollifier.kernel n)) y) x := by
  rw [quartic_correction_expectation_all_x]
  have h₀₀ : cov[gaussianTriple n x 0, gaussianTriple n x 0; gaussianProduct] =
      wholeLineVariance (IBMMollifier.kernel n) x := by
    rw [gaussianTriple_covariance_eq_L2_inner]
    simp [derivativeKernel, wholeLineVariance]
  have h₀₁ : 2 * cov[gaussianTriple n x 0, gaussianTriple n x 1;
      gaussianProduct] = deriv (wholeLineVariance (IBMMollifier.kernel n)) x := by
    rw [gaussianTriple_covariance_eq_L2_inner]
    simpa [derivativeKernel] using
      (wholeLineVariance_deriv (IBMMollifier.kernel n)
        (IBMMollifier.kernel_compactSupport n)
        ((IBMMollifier.kernel_smooth n).of_le (by norm_num)) x).symm
  have hsum : 2 *
      (cov[gaussianTriple n x 1, gaussianTriple n x 1; gaussianProduct] +
        cov[gaussianTriple n x 0, gaussianTriple n x 2; gaussianProduct]) =
      deriv (fun y => deriv (wholeLineVariance (IBMMollifier.kernel n)) y) x := by
    rw [gaussianTriple_covariance_eq_L2_inner,
      gaussianTriple_covariance_eq_L2_inner]
    simpa [derivativeKernel, real_inner_self_eq_norm_sq] using
      (wholeLineVariance_second_deriv (IBMMollifier.kernel n)
        (IBMMollifier.kernel_compactSupport n)
        ((IBMMollifier.kernel_smooth n).of_le (by norm_num)) x).symm
  rw [h₀₀]
  have hsq := congrArg (fun z : ℝ => z^2) h₀₁
  have hmul := congrArg (fun z : ℝ =>
      wholeLineVariance (IBMMollifier.kernel n) x * z) hsum
  nlinarith

/-- Exact finite-mollifier boundary deviation from the bulk `1/4` Stein
coefficient. All terms are ordinary real derivatives of the proved Gaussian
L² variance; no distributional limit has been taken. -/
theorem quartic_boundary_stein_deviation (n : ℕ) (x : ℝ) :
    (∫ ω, (1 / 2 : ℝ) *
        (gaussianTriple n x 0 ω)^2 * (gaussianTriple n x 1 ω)^2 +
        (1 / 6 : ℝ) *
        (gaussianTriple n x 0 ω)^3 * gaussianTriple n x 2 ω
      ∂gaussianProduct) - 1 / 4 =
      (1 / 4 : ℝ) *
        ((deriv (wholeLineVariance (IBMMollifier.kernel n)) x)^2 - 1 +
          wholeLineVariance (IBMMollifier.kernel n) x *
            deriv (fun y => deriv (wholeLineVariance (IBMMollifier.kernel n)) y) x) := by
  rw [quartic_correction_variance_geometry]
  ring

end OperatorDerivativeRewrite.Foundation.IBMGaussianSteinMoments
