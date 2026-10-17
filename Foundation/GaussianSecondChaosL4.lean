import Foundation.GaussianQuadraticMatrixApproximation
import Foundation.L2SquareLimit

/-! Every completed actual second-chaos L2 target has a genuine square in L2,
with the sharp Gaussian quadratic fourth-moment coefficient fifteen. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianSecondChaosL4
open InfiniteGaussian GaussianNumberSectors GaussianDivergenceRecovery
open GaussianQuadraticRecoverySurjectivity GaussianLinearFieldDivergenceCompletion
open GaussianQuadraticMatrixApproximation

theorem exists_square {f : GaussianL2} (hf : f ∈ sector 2) :
    ∃ q : GaussianL2, q =ᵐ[gaussianProduct] (fun ω => (f ω)^2) ∧
      ‖q‖^2 ≤ 15 * (‖f‖^2)^2 := by
  let v : linearGaussianFields := ⟨recovery f, recovery_second_chaos_linear hf⟩
  let b : ℕ → polynomialCylindricalDomain := fun n => boxCore (Finset.range n) v
  let sq : ℕ → GaussianL2 := fun n => polynomialProduct (b n) (b n)
  have ht : Tendsto (fun n => (b n : GaussianL2)) atTop (𝓝 f) := boxCore_tendsto f hf
  have hsq (n : ℕ) : sq n =ᵐ[gaussianProduct] fun ω => ((b n : GaussianL2) ω)^2 := by
    filter_upwards [polynomialProductL2_coeFn (b n) (b n)] with ω hp
    change polynomialProductL2 (b n) (b n) ω = _
    rw [hp]
    ring
  have hC : 0 ≤ Real.sqrt 15 * ‖f‖^2 := by positivity
  have hb (n : ℕ) : ‖sq n‖ ≤ Real.sqrt 15 * ‖f‖^2 := by
    apply (sq_le_sq₀ (norm_nonneg _) hC).mp
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)]
    exact boxCore_fourth_upper_bound f hf (Finset.range n)
  obtain ⟨q, hq, hqb⟩ := L2SquareLimit.exists_square_of_bounded_approximation
    (fun n => (b n : GaussianL2)) sq f (Real.sqrt 15 * ‖f‖^2) hC ht hsq hb
  refine ⟨q, hq, ?_⟩
  have he := (sq_le_sq₀ (norm_nonneg _) hC).mpr hqb
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)] at he
  exact he

def square (f : sector 2) : GaussianL2 := Classical.choose (exists_square f.property)

theorem square_coeFn (f : sector 2) :
    square f =ᵐ[gaussianProduct] fun ω => (f.val ω)^2 :=
  (Classical.choose_spec (exists_square f.property)).1

theorem square_norm_bound (f : sector 2) : ‖square f‖^2 ≤ 15 * (‖f.val‖^2)^2 :=
  (Classical.choose_spec (exists_square f.property)).2

theorem second_chaos_memLp_four {f : GaussianL2} (hf : f ∈ sector 2) : MemLp f 4 gaussianProduct :=
  L2SquareLimit.memLp_four_of_square f (square ⟨f, hf⟩) (square_coeFn ⟨f, hf⟩)

theorem fourth_power_integrable (f : sector 2) :
    Integrable (fun ω => (f.val ω)^4) gaussianProduct := by
  have hi := (Lp.memLp (square f)).norm.integrable_sq
  apply hi.congr
  filter_upwards [square_coeFn f] with ω hq
  rw [Real.norm_eq_abs, sq_abs, hq]
  ring

theorem fourth_moment_bound (f : sector 2) :
    (∫ ω, (f.val ω)^4 ∂gaussianProduct) ≤ 15 * (‖f.val‖^2)^2 := by
  have he : (∫ ω, (f.val ω)^4 ∂gaussianProduct) = ‖square f‖^2 := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [square_coeFn f] with ω hq
    rw [Real.norm_eq_abs, sq_abs, hq]
    ring
  rw [he]
  exact square_norm_bound f

theorem square_polynomial (p : polynomialCylindricalDomain) (hp : (p : GaussianL2) ∈ sector 2) :
    square ⟨p, hp⟩ = (polynomialProduct p p : GaussianL2) := by
  apply Lp.ext
  filter_upwards [square_coeFn ⟨p, hp⟩, polynomialProductL2_coeFn p p] with ω hq hp'
  change square ⟨p, hp⟩ ω = polynomialProductL2 p p ω
  rw [hq, hp']
  ring

end OperatorDerivativeRewrite.Foundation.GaussianSecondChaosL4
