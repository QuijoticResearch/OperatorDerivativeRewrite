import Foundation.SU2HaarLaplaceUpper

/-! Matched polynomial normalization bounds for the actual homogeneous Wilson slab. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeMatchedGround
open CubeTemporalSlab CubeWilsonSlab CubeSlabGround CubeHaarUpper SU2HaarLaplaceUpper
attribute [local irreducible] CubeWilsonSlab.kernel boundaryHaar

def temporalConstant : ℝ := upperConstant (1/63)
def boundaryConstant : ℝ := upperConstant (1/8)
def upperGroundConstant : ℝ := temporalConstant^7*boundaryConstant^5

theorem temporalConstant_pos : 0 < temporalConstant := upperConstant_pos (1/63) (by norm_num)
theorem boundaryConstant_pos : 0 < boundaryConstant := upperConstant_pos (1/8) (by norm_num)
theorem upperGroundConstant_pos : 0 < upperGroundConstant :=
  mul_pos (pow_pos temporalConstant_pos 7) (pow_pos boundaryConstant_pos 5)

private theorem temporal_scalar (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) :
    laplace ((1/t^2)/63) ≤ temporalConstant*t^3 := by
  have he : (1/t^2)/63=(1/63)/t^2 := by ring
  rw [he]
  exact laplace_scaled_upper (1/63) t (by norm_num) ht h1

private theorem boundary_scalar (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) :
    laplace ((1/t^2)/8) ≤ boundaryConstant*t^3 := by
  have he : (1/t^2)/8=(1/8)/t^2 := by ring
  rw [he]
  exact laplace_scaled_upper (1/8) t (by norm_num) ht h1

/-- Actual temporal integration has the correct t^21 upper power, with the free
root Haar orbit retained and arbitrary original boundary representatives. -/
theorem kernel_upper (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (U V : State) :
    kernel (1/t^2) U V ≤
      Real.exp (-(1/t^2)*spatialAction U/2)*Real.exp (-(1/t^2)*spatialAction V/2)*
      temporalConstant^7*t^21 := by
  have hp := pow_le_pow_left₀ (laplace_pos ((1/t^2)/63) (by positivity)).le
    (temporal_scalar t ht h1) 7
  have h := (CubeHaarUpper.kernel_upper (1/t^2) (by positivity) U V).trans
    (mul_le_mul_of_nonneg_left hp (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
  convert h using 1 <;> ring

/-- Actual original boundary Haar, not an auxiliary Gibbs probability. -/
theorem boundary_integral_upper (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) :
    (∫ U,Real.exp (-(1/t^2)*spatialAction U/2) ∂boundaryHaar) ≤ boundaryConstant^5*t^15 := by
  have hp := pow_le_pow_left₀ (laplace_pos ((1/t^2)/8) (by positivity)).le
    (boundary_scalar t ht h1) 5
  have h := (CubeHaarUpper.boundary_integral_upper (1/t^2) (by positivity)).trans hp
  convert h using 1 <;> ring

/-- A beta^-18-SCALE upper bound for every ACTUAL positive ground, with explicit
beta-independent constants. A limiting prefactor or spectral gap is not asserted. -/
theorem eigenvalue_upper (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (d : GroundData (1/t^2)) :
    d.value ≤ upperGroundConstant*t^36 := by
  have h7 := pow_le_pow_left₀ (laplace_pos ((1/t^2)/63) (by positivity)).le
    (temporal_scalar t ht h1) 7
  have h5 := pow_le_pow_left₀ (laplace_pos ((1/t^2)/8) (by positivity)).le
    (boundary_scalar t ht h1) 5
  have hp := mul_le_mul h7 h5 (pow_nonneg (laplace_pos ((1/t^2)/8) (by positivity)).le 5)
    (pow_nonneg (mul_pos temporalConstant_pos (pow_pos ht 3)).le 7)
  have h := (CubeHaarUpper.eigenvalue_upper d (by positivity)).trans hp
  convert h using 1 <;> unfold upperGroundConstant <;> ring

/-- Matched polynomial powers for the genuine integrated-kernel normalization. -/
theorem normalization_bounds (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (d : GroundData (1/t^2)) :
    CubeRootGround.lowerConstant*t^36 ≤ d.value ∧ d.value ≤ upperGroundConstant*t^36 := by
  have hs : (1/t^2)*t^2=1 := by field_simp [ht.ne']
  exact ⟨CubeRootGround.eigenvalue_polynomial d t ht h1 (by positivity) hs.le,
    eigenvalue_upper t ht h1 d⟩

/-- The actual rescaled ground values stay bounded above AND away from zero.
This does not prove their convergence or identify a limiting prefactor. -/
theorem rescaled_value_bounds (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (d : GroundData (1/t^2)) :
    CubeRootGround.lowerConstant ≤ d.value/t^36 ∧ d.value/t^36 ≤ upperGroundConstant := by
  have h := normalization_bounds t ht h1 d
  exact ⟨(le_div_iff₀ (pow_pos ht 36)).mpr h.1,(div_le_iff₀ (pow_pos ht 36)).mpr h.2⟩

end OperatorDerivativeRewrite.Foundation.CubeMatchedGround
