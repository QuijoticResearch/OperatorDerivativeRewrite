import Foundation.GaussianQuarticWick
import Foundation.BochnerL2Dominated

/-! Rank-one pure second-chaos observables retain sharp square association, unlike mixtures. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianPureQuadraticProduct
open InfiniteGaussian GaussianTimeSpaceHermite GaussianQuarticWick

def quadraticSquare (u : CoefficientSpace) : GaussianL2 :=
  (wick u 4 : GaussianL2)+(4*‖u‖^2 : ℝ) • (wick u 2 : GaussianL2)+
    (2*(‖u‖^2)^2 : ℝ) • (wick u 0 : GaussianL2)

theorem quadraticSquare_coeFn (u : CoefficientSpace) : quadraticSquare u =ᵐ[gaussianProduct]
    fun ω => ((wick u 2 : GaussianL2) ω)^2 := by
  filter_upwards [Lp.coeFn_add
    ((wick u 4 : GaussianL2)+(4*‖u‖^2 : ℝ) • (wick u 2 : GaussianL2))
    ((2*(‖u‖^2)^2 : ℝ) • (wick u 0 : GaussianL2)),
    Lp.coeFn_add (wick u 4 : GaussianL2) ((4*‖u‖^2 : ℝ) • (wick u 2 : GaussianL2)),
    Lp.coeFn_smul (4*‖u‖^2 : ℝ) (wick u 2 : GaussianL2),
    Lp.coeFn_smul (2*(‖u‖^2)^2 : ℝ) (wick u 0 : GaussianL2),
    core_coeFn u (‖u‖^2) 4,core_coeFn u (‖u‖^2) 2,core_coeFn u (‖u‖^2) 0] with ω ha hb hc hd h4 h2 h0
  change (((wick u 4 : GaussianL2)+(4*‖u‖^2 : ℝ) • (wick u 2 : GaussianL2))+
    (2*(‖u‖^2)^2 : ℝ) • (wick u 0 : GaussianL2)) ω=_
  rw [ha,Pi.add_apply,hb,Pi.add_apply,hc,hd,Pi.smul_apply,Pi.smul_apply]
  simp only [wick] at *
  rw [h4,h2,h0]
  simp only [smul_eq_mul,value_four,value_two,value_zero]
  ring

theorem quadraticSquare_inner (u v : CoefficientSpace) :
    inner ℝ (quadraticSquare u) (quadraticSquare v)=
      4*(‖u‖^2)^2*(‖v‖^2)^2+32*‖u‖^2*‖v‖^2*(inner ℝ u v)^2+24*(inner ℝ u v)^4 := by
  simp only [quadraticSquare,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,wick_inner]
  norm_num
  ring

theorem product_energy (u v : CoefficientSpace) :
    ‖(polynomialProduct (wick u 2) (wick v 2) : GaussianL2)‖^2=
      4*(‖u‖^2)^2*(‖v‖^2)^2+32*‖u‖^2*‖v‖^2*(inner ℝ u v)^2+24*(inner ℝ u v)^4 := by
  have he : ‖(polynomialProduct (wick u 2) (wick v 2) : GaussianL2)‖^2=
      inner ℝ (quadraticSquare u) (quadraticSquare v) := by
    rw [BochnerL2Dominated.norm_sq_integral,L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [polynomialProductL2_coeFn (wick u 2) (wick v 2),quadraticSquare_coeFn u,
      quadraticSquare_coeFn v] with ω hp hu hv
    change ‖polynomialProductL2 (wick u 2) (wick v 2) ω‖^2=_
    rw [hp,hu,hv]
    simp only [Real.norm_eq_abs,sq_abs,Real.inner_apply]
    ring
  rw [he,quadraticSquare_inner]

theorem square_association (u v : CoefficientSpace) :
    ‖(wick u 2 : GaussianL2)‖^2*‖(wick v 2 : GaussianL2)‖^2≤
      ‖(polynomialProduct (wick u 2) (wick v 2) : GaussianL2)‖^2 := by
  rw [product_energy,GaussianTimeSpaceHermite.wick_norm_sq,GaussianTimeSpaceHermite.wick_norm_sq]
  norm_num
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ‖u‖) (sq_nonneg ‖v‖)) (sq_nonneg (inner ℝ u v)),
    sq_nonneg ((inner ℝ u v)^2)]

theorem square_association_equality_iff (u v : CoefficientSpace) :
    ‖(polynomialProduct (wick u 2) (wick v 2) : GaussianL2)‖^2=
      ‖(wick u 2 : GaussianL2)‖^2*‖(wick v 2 : GaussianL2)‖^2 ↔ inner ℝ u v=0 := by
  rw [product_energy,GaussianTimeSpaceHermite.wick_norm_sq,GaussianTimeSpaceHermite.wick_norm_sq]
  norm_num
  constructor
  · intro he
    have hm := mul_nonneg (mul_nonneg (sq_nonneg ‖u‖) (sq_nonneg ‖v‖)) (sq_nonneg (inner ℝ u v))
    have hz : (inner ℝ u v)^4=0 := by nlinarith [sq_nonneg ((inner ℝ u v)^2)]
    exact (pow_eq_zero_iff (by norm_num : (4 : ℕ)≠0)).mp hz
  · intro he
    rw [he]
    ring

theorem fourth_moment_sharp (u : CoefficientSpace) :
    ‖(polynomialProduct (wick u 2) (wick u 2) : GaussianL2)‖^2=
      15*(‖(wick u 2 : GaussianL2)‖^2)^2 := by
  rw [product_energy,real_inner_self_eq_norm_sq,GaussianTimeSpaceHermite.wick_norm_sq]
  norm_num
  ring

end OperatorDerivativeRewrite.Foundation.GaussianPureQuadraticProduct


