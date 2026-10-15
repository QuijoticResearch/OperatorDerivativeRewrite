import Foundation.GaussianQuarticWick
import Foundation.GaussianRecoveryCompactnessObstruction
import Foundation.BochnerL2Dominated

/-! Centered first/second-chaos mixtures need not have nonnegative square-product covariance. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianMixedChaosProductCounterexample
open InfiniteGaussian GaussianTimeSpaceHermite GaussianQuarticWick

def mix (u : CoefficientSpace) (a : ℝ) : polynomialCylindricalDomain := wick u 1+a • wick u 2

theorem mix_centered (u : CoefficientSpace) (a : ℝ) : inner ℝ gaussianOne (mix u a : GaussianL2)=0 := by
  change inner ℝ gaussianOne ((wick u 1 : GaussianL2)+a • (wick u 2 : GaussianL2))=0
  rw [inner_add_right,real_inner_smul_right,wick_centered u 0,wick_centered u 1]
  ring

theorem mix_norm_sq (u : CoefficientSpace) (hu : ‖u‖^2=1) (a : ℝ) : ‖(mix u a : GaussianL2)‖^2=1+2*a^2 := by
  change ‖(wick u 1 : GaussianL2)+a • (wick u 2 : GaussianL2)‖^2=_
  rw [← real_inner_self_eq_norm_sq]
  have hi : inner ℝ u u=1 := (real_inner_self_eq_norm_sq u).trans hu
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,wick_inner,
    hi]
  norm_num
  ring

theorem mix_coeFn (u : CoefficientSpace) (hu : ‖u‖^2=1) (a : ℝ) :
    (mix u a : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => firstChaosEmbedding u ω+a*((firstChaosEmbedding u ω)^2-1) := by
  filter_upwards [Lp.coeFn_add (wick u 1 : GaussianL2) (a • (wick u 2 : GaussianL2)),
    Lp.coeFn_smul a (wick u 2 : GaussianL2),core_coeFn u (‖u‖^2) 1,core_coeFn u (‖u‖^2) 2] with ω ha hs h1 h2
  change ((wick u 1 : GaussianL2)+a • (wick u 2 : GaussianL2)) ω=_
  rw [ha,Pi.add_apply,hs,Pi.smul_apply]
  simp only [wick]
  rw [h1,h2]
  simp only [hu,value_one,value_two,smul_eq_mul]

theorem mix_product (u : CoefficientSpace) (hu : ‖u‖^2=1) :
    polynomialProduct (mix u (1/2)) (mix u (-(1/2)))=
      (1/2 : ℝ) • wick u 0-(1/4 : ℝ) • wick u 4 := by
  apply Subtype.ext
  change polynomialProductL2 (mix u (1/2)) (mix u (-(1/2)))=
    (1/2 : ℝ) • (wick u 0 : GaussianL2)-(1/4 : ℝ) • (wick u 4 : GaussianL2)
  apply Lp.ext
  filter_upwards [polynomialProductL2_coeFn (mix u (1/2)) (mix u (-(1/2))),
    mix_coeFn u hu (1/2),mix_coeFn u hu (-(1/2)),
    Lp.coeFn_sub ((1/2 : ℝ) • (wick u 0 : GaussianL2)) ((1/4 : ℝ) • (wick u 4 : GaussianL2)),
    Lp.coeFn_smul (1/2 : ℝ) (wick u 0 : GaussianL2),Lp.coeFn_smul (1/4 : ℝ) (wick u 4 : GaussianL2),
    core_coeFn u (‖u‖^2) 0,core_coeFn u (‖u‖^2) 4] with ω hp hf hg hs h0 h4 hw0 hw4
  rw [hp,hf,hg,hs,Pi.sub_apply,h0,h4,Pi.smul_apply,Pi.smul_apply]
  simp only [wick]
  rw [hw0,hw4]
  simp only [hu,value_zero,value_four,smul_eq_mul]
  ring

theorem mix_product_norm_sq (u : CoefficientSpace) (hu : ‖u‖^2=1) :
    ‖(polynomialProduct (mix u (1/2)) (mix u (-(1/2))) : GaussianL2)‖^2=7/4 := by
  rw [mix_product u hu]
  change ‖(1/2 : ℝ) • (wick u 0 : GaussianL2)-(1/4 : ℝ) • (wick u 4 : GaussianL2)‖^2=_
  rw [← real_inner_self_eq_norm_sq]
  have hi : inner ℝ u u=1 := (real_inner_self_eq_norm_sq u).trans hu
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,wick_inner,
    hi]
  norm_num

theorem mixed_square_association_failure (u : CoefficientSpace) (hu : ‖u‖^2=1) :
    ‖(polynomialProduct (mix u (1/2)) (mix u (-(1/2))) : GaussianL2)‖^2<
      ‖(mix u (1/2) : GaussianL2)‖^2*‖(mix u (-(1/2)) : GaussianL2)‖^2 := by
  rw [mix_product_norm_sq u hu,mix_norm_sq u hu,mix_norm_sq u hu]
  norm_num

private theorem norm_integral_sq (f : GaussianL2) : ‖f‖^2=∫ ω, (f ω)^2 ∂gaussianProduct := by
  simpa only [Real.norm_eq_abs,sq_abs] using BochnerL2Dominated.norm_sq_integral f

theorem negative_square_covariance (u : CoefficientSpace) (hu : ‖u‖^2=1) :
    (∫ ω, ((mix u (1/2) : GaussianL2) ω)^2*((mix u (-(1/2)) : GaussianL2) ω)^2 ∂gaussianProduct)-
      (∫ ω, ((mix u (1/2) : GaussianL2) ω)^2 ∂gaussianProduct)*
      (∫ ω, ((mix u (-(1/2)) : GaussianL2) ω)^2 ∂gaussianProduct)=-(1/2 : ℝ) := by
  have hp : ‖(polynomialProduct (mix u (1/2)) (mix u (-(1/2))) : GaussianL2)‖^2=
      ∫ ω, ((mix u (1/2) : GaussianL2) ω)^2*((mix u (-(1/2)) : GaussianL2) ω)^2 ∂gaussianProduct := by
    rw [norm_integral_sq]
    apply integral_congr_ae
    filter_upwards [polynomialProductL2_coeFn (mix u (1/2)) (mix u (-(1/2)))] with ω hw
    change (polynomialProductL2 (mix u (1/2)) (mix u (-(1/2))) ω)^2=_
    rw [hw,mul_pow]
  rw [← hp,← norm_integral_sq,← norm_integral_sq,mix_product_norm_sq u hu,mix_norm_sq u hu,mix_norm_sq u hu]
  norm_num

theorem exists_centered_polynomial_counterexample : ∃ f g : polynomialCylindricalDomain,
    inner ℝ gaussianOne (f : GaussianL2)=0 ∧ inner ℝ gaussianOne (g : GaussianL2)=0 ∧
      ‖(polynomialProduct f g : GaussianL2)‖^2<‖(f : GaussianL2)‖^2*‖(g : GaussianL2)‖^2 := by
  let u : CoefficientSpace := lp.single 2 0 (1 : ℝ)
  have hu : ‖u‖^2=1 := by
    rw [show ‖u‖=1 from GaussianRecoveryCompactnessObstruction.coefficient_single_orthonormal.norm_eq_one 0]
    norm_num
  exact ⟨mix u (1/2),mix u (-(1/2)),mix_centered _ _,mix_centered _ _,mixed_square_association_failure u hu⟩

end OperatorDerivativeRewrite.Foundation.GaussianMixedChaosProductCounterexample
