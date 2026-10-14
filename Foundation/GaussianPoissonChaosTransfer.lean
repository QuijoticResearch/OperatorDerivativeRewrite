import Foundation.PoissonCharlierLadder
import Foundation.IBMCubicFirstChaos

/-! Identical finite-chaos Hilbert geometry across Gaussian and Poisson
sources does not identify their ordinary multiplication algebras. -/
noncomputable section
open MeasureTheory
open scoped NNReal
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.GaussianPoissonChaosTransfer
open InfiniteGaussian GaussianTimeSpaceHermite
open PoissonDifferenceOperators PoissonPolynomialExamples

def poissonExpansion (rate : ℝ≥0) (hr : 0 < rate) {N : ℕ} (c : Fin N → ℝ) :
    ScalarL2 rate := ∑ i, c i • PoissonCharlierLadder.scalar rate hr i.val

def gaussianExpansion (h : CoefficientSpace) {N : ℕ} (c : Fin N → ℝ) : GaussianL2 :=
  ∑ i, c i • (wick h i.val : GaussianL2)

theorem poissonExpansion_inner (rate : ℝ≥0) (hr : 0 < rate) {N : ℕ}
    (c d : Fin N → ℝ) :
    inner ℝ (poissonExpansion rate hr c) (poissonExpansion rate hr d) =
      ∑ i, c i*d i*(i.val.factorial : ℝ)*(rate : ℝ)^i.val := by
  simp only [poissonExpansion, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, PoissonCharlierLadder.scalar_inner]
  simp [Fin.val_inj, mul_ite, ite_mul, mul_assoc, mul_left_comm]

theorem gaussianExpansion_inner (h : CoefficientSpace) {N : ℕ} (c d : Fin N → ℝ) :
    inner ℝ (gaussianExpansion h c) (gaussianExpansion h d) =
      ∑ i, c i*d i*(i.val.factorial : ℝ)*(‖h‖^2)^i.val := by
  simp only [gaussianExpansion, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, wick_inner, real_inner_self_eq_norm_sq]
  simp [Fin.val_inj, mul_ite, ite_mul, mul_assoc, mul_left_comm]

/-- The exact same coefficient map preserves all finite-chaos inner products
when the Gaussian direction variance is the Poisson rate. -/
theorem finite_chaos_inner_transfer (rate : ℝ≥0) (hr : 0 < rate)
    (h : CoefficientSpace) (hv : ‖h‖^2 = rate) {N : ℕ} (c d : Fin N → ℝ) :
    inner ℝ (poissonExpansion rate hr c) (poissonExpansion rate hr d) =
      inner ℝ (gaussianExpansion h c) (gaussianExpansion h d) := by
  rw [poissonExpansion_inner, gaussianExpansion_inner, hv]

theorem finite_chaos_norm_transfer (rate : ℝ≥0) (hr : 0 < rate)
    (h : CoefficientSpace) (hv : ‖h‖^2 = rate) {N : ℕ} (c : Fin N → ℝ) :
    ‖poissonExpansion rate hr c‖ = ‖gaussianExpansion h c‖ := by
  have he := finite_chaos_inner_transfer rate hr h hv c c
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (poissonExpansion rate hr c), norm_nonneg (gaussianExpansion h c)]

def matchingDirection (rate : ℝ≥0) : CoefficientSpace :=
  lp.single 2 0 (Real.sqrt rate)

theorem matchingDirection_norm_sq (rate : ℝ≥0) : ‖matchingDirection rate‖^2 = rate := by
  rw [matchingDirection, lp.norm_single (by norm_num), Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt rate.coe_nonneg

theorem concrete_finite_chaos_norm_transfer (rate : ℝ≥0) (hr : 0 < rate)
    {N : ℕ} (c : Fin N → ℝ) :
    ‖poissonExpansion rate hr c‖ = ‖gaussianExpansion (matchingDirection rate) c‖ :=
  finite_chaos_norm_transfer rate hr _ (matchingDirection_norm_sq rate) c

theorem charlier_one (rate : ℝ≥0) (x : ℝ) :
    PoissonCharlierLadder.value rate 1 x = x-rate := by
  simp [PoissonCharlierLadder.value_succ, PoissonCharlierLadder.value_zero]

theorem charlier_two (rate : ℝ≥0) (x : ℝ) :
    PoissonCharlierLadder.value rate 2 x = (x-rate)^2-(x-rate)-rate := by
  rw [PoissonCharlierLadder.value_succ, charlier_one, charlier_one]
  ring

/-- Poisson squaring creates first chaos, unlike squaring a centered Gaussian.
The rate term remains the scalar vacuum contribution. -/
theorem poisson_square_decomposition (rate : ℝ≥0) (hr : 0 < rate) :
    centeredCountSqL2 rate hr = PoissonCharlierLadder.scalar rate hr 2 +
      PoissonCharlierLadder.scalar rate hr 1 +
      (rate : ℝ) • PoissonCharlierLadder.scalar rate hr 0 := by
  apply Lp.ext
  filter_upwards [] with k
  rw [PoissonCoordinateEvaluation.scalar_add_apply rate hr,
    PoissonCoordinateEvaluation.scalar_add_apply rate hr,
    PoissonCoordinateEvaluation.scalar_smul_apply rate hr, centeredCountSqL2_apply,
    PoissonCharlierLadder.scalar_apply, PoissonCharlierLadder.scalar_apply,
    PoissonCharlierLadder.scalar_apply, charlier_two, charlier_one,
    PoissonCharlierLadder.value_zero]
  simp only [centeredCount]
  ring

theorem poisson_square_first_inner (rate : ℝ≥0) (hr : 0 < rate) :
    inner ℝ (centeredCountSqL2 rate hr) (PoissonCharlierLadder.scalar rate hr 1) = rate := by
  rw [poisson_square_decomposition]
  simp only [inner_add_left, real_inner_smul_left, PoissonCharlierLadder.scalar_inner]
  norm_num

theorem gaussian_square_first_inner (h : CoefficientSpace) :
    inner ℝ ((wick h 2 : GaussianL2) + (‖h‖^2) • (wick h 0 : GaussianL2))
      (wick h 1 : GaussianL2) = 0 := by
  simp only [inner_add_left, real_inner_smul_left, wick_inner]
  norm_num

theorem gaussian_square_coeFn (h : CoefficientSpace) :
    ((wick h 2 : GaussianL2) + (‖h‖^2) • (wick h 0 : GaussianL2)) =ᵐ[gaussianProduct]
      fun ω => (firstChaosEmbedding h ω)^2 := by
  filter_upwards [Lp.coeFn_add (wick h 2 : GaussianL2)
      ((‖h‖^2) • (wick h 0 : GaussianL2)),
    Lp.coeFn_smul (‖h‖^2) (wick h 0 : GaussianL2),
    core_coeFn h (‖h‖^2) 2, core_coeFn h (‖h‖^2) 0] with ω ha hs h2 h0
  rw [ha]
  simp only [Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul]
  change (core h (‖h‖^2) 2 : GaussianL2) ω +
    (‖h‖^2)*(core h (‖h‖^2) 0 : GaussianL2) ω = _
  rw [h2,h0]
  simp

end OperatorDerivativeRewrite.Foundation.GaussianPoissonChaosTransfer
