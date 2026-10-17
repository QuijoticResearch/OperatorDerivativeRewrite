import Foundation.GaussianSecondChaosL4
import Foundation.GaussianPureQuadraticProduct
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Actual bounded bilinear multiplication from completed second-chaos targets
to Gaussian L2. The output is not asserted to remain in second chaos. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianSecondChaosProduct
open InfiniteGaussian GaussianNumberSectors GaussianSecondChaosL4

def product (f g : sector 2) : GaussianL2 :=
  (mul_memLp (second_chaos_memLp_four f.property) (second_chaos_memLp_four g.property)).toLp _

theorem product_coeFn (f g : sector 2) : product f g =ᵐ[gaussianProduct]
    fun ω => f.val ω * g.val ω := MemLp.coeFn_toLp _

theorem product_energy_inner (f g : sector 2) :
    ‖product f g‖^2 = inner ℝ (square f) (square g) := by
  rw [BochnerL2Dominated.norm_sq_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [product_coeFn f g, square_coeFn f, square_coeFn g] with ω hp hf hg
  rw [hp, hf, hg]
  simp only [Real.norm_eq_abs, sq_abs, Real.inner_apply]
  ring

theorem square_norm_le (f : sector 2) : ‖square f‖ ≤ Real.sqrt 15 * ‖f.val‖^2 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]
  exact square_norm_bound f

theorem product_energy_bound (f g : sector 2) :
    ‖product f g‖^2 ≤ 15 * ‖f.val‖^2 * ‖g.val‖^2 := by
  rw [product_energy_inner]
  calc
    _ ≤ ‖square f‖ * ‖square g‖ := real_inner_le_norm _ _
    _ ≤ (Real.sqrt 15 * ‖f.val‖^2) * (Real.sqrt 15 * ‖g.val‖^2) :=
      mul_le_mul (square_norm_le f) (square_norm_le g) (norm_nonneg _) (by positivity)
    _ = _ := by
      calc
        _ = (Real.sqrt 15)^2 * ‖f.val‖^2 * ‖g.val‖^2 := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]

theorem product_norm_bound (f g : sector 2) :
    ‖product f g‖ ≤ Real.sqrt 15 * ‖f‖ * ‖g‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]
  exact product_energy_bound f g

theorem product_comm (f g : sector 2) : product f g = product g f := by
  apply Lp.ext
  filter_upwards [product_coeFn f g, product_coeFn g f] with ω hfg hgf
  rw [hfg, hgf, mul_comm]

theorem product_add_left (f k g : sector 2) : product (f+k) g = product f g + product k g := by
  apply Lp.ext
  filter_upwards [product_coeFn (f+k) g, product_coeFn f g, product_coeFn k g,
    Lp.coeFn_add f.val k.val, Lp.coeFn_add (product f g) (product k g)] with ω hs hf hk ha hb
  rw [hs, hb, Pi.add_apply, hf, hk]
  change (f.val + k.val) ω * g.val ω = _
  rw [ha, Pi.add_apply]
  ring

theorem product_smul_left (c : ℝ) (f g : sector 2) : product (c • f) g = c • product f g := by
  apply Lp.ext
  filter_upwards [product_coeFn (c • f) g, product_coeFn f g,
    Lp.coeFn_smul c f.val, Lp.coeFn_smul c (product f g)] with ω hs hf ha hb
  rw [hs, hb, Pi.smul_apply, hf]
  change (c • f.val) ω * g.val ω = _
  rw [ha, Pi.smul_apply]
  simp only [smul_eq_mul]
  ring

theorem product_add_right (f g k : sector 2) : product f (g+k) = product f g + product f k := by
  rw [product_comm, product_add_left, product_comm g f, product_comm k f]

theorem product_smul_right (c : ℝ) (f g : sector 2) : product f (c • g) = c • product f g := by
  rw [product_comm, product_smul_left, product_comm g f]

def productLinear : sector 2 →ₗ[ℝ] sector 2 →ₗ[ℝ] GaussianL2 :=
  LinearMap.mk₂ ℝ product product_add_left product_smul_left product_add_right product_smul_right

def productBilinear : sector 2 →L[ℝ] sector 2 →L[ℝ] GaussianL2 :=
  productLinear.mkContinuous₂ (Real.sqrt 15) product_norm_bound

theorem productBilinear_apply (f g : sector 2) : productBilinear f g = product f g := rfl

theorem product_self_eq_square (f : sector 2) : product f f = square f := by
  apply Lp.ext
  filter_upwards [product_coeFn f f, square_coeFn f] with ω hp hs
  rw [hp, hs]
  ring

/-- Rank-one quadratic squares attain the bilinear norm exactly. -/
theorem productBilinear_norm : ‖productBilinear‖ = Real.sqrt 15 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound₂ _ (Real.sqrt_nonneg _)
    intro f g
    exact product_norm_bound f g
  · let u := GaussianLinearFieldMatrixCoordinates.unit 0
    have hu : ‖u‖^2 = 1 := by
      rw [show ‖u‖ = 1 from GaussianLinearFieldMatrixCoordinates.units_orthonormal.norm_eq_one 0]
      norm_num
    let f : sector 2 := ⟨(GaussianTimeSpaceHermite.wick u 2 : GaussianL2),
      IBMCubicFirstChaos.wick_mem_sector u 2⟩
    have hf : ‖f‖^2 = 2 := by
      change ‖(GaussianTimeSpaceHermite.wick u 2 : GaussianL2)‖^2 = 2
      rw [GaussianWickContinuity.wick_norm_sq, hu]
      norm_num
    have hs : ‖product f f‖^2 = 15 * (‖f‖^2)^2 := by
      rw [product_self_eq_square, square_polynomial (GaussianTimeSpaceHermite.wick u 2) f.property]
      exact GaussianPureQuadraticProduct.fourth_moment_sharp u
    have hb := productBilinear.le_opNorm₂ f f
    change ‖product f f‖ ≤ ‖productBilinear‖ * ‖f‖ * ‖f‖ at hb
    have hb2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖productBilinear‖ * ‖f‖ * ‖f‖)).mpr hb
    rw [hs, mul_pow, mul_pow, hf] at hb2
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]
    nlinarith

theorem product_continuous : Continuous (fun fg : sector 2 × sector 2 => product fg.1 fg.2) := by
  change Continuous (fun fg : sector 2 × sector 2 => productBilinear fg.1 fg.2)
  fun_prop

end OperatorDerivativeRewrite.Foundation.GaussianSecondChaosProduct
