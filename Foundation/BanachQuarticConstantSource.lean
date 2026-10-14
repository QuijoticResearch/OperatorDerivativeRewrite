import Foundation.BanachQuarticWeightedStability

/-! A genuine probability-space constant source has regular nonzero quartic
inverse data, in contrast with the infinite Poisson L4 identity source. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.BanachQuarticConstantSource
open BanachLpDualityFour BanachLpDualityFourContinuity BanachLpDualityFourInfinite
open BanachQuarticWeightedStability
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
private instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def source : ℝ →L[ℝ] Lp ℝ 4 μ := Lp.constL 4 μ ℝ

theorem source_norm (w : ℝ) : ‖source μ w‖=‖w‖ := by
  simp only [source,Lp.constL_apply]
  rw [Lp.norm_const 4 μ w (by norm_num)]
  simp

theorem weightedSource_eq_const (u w : ℝ) :
    weightedSource (source μ) u w=Lp.const 2 μ (u*w) := by
  apply Lp.ext
  filter_upwards [squareProduct_ae (source μ u) (source μ w),
    Lp.coeFn_const (p := 4) (μ := μ) u,Lp.coeFn_const (p := 4) (μ := μ) w,
    Lp.coeFn_const (p := 2) (μ := μ) (u*w)] with ω hp hu hw hc
  change (squareProduct (source μ u) (source μ w)) ω=_
  rw [hp]
  simpa only [source,Lp.constL_apply] using congrArg₂ (fun a b : ℝ => a*b) hu hw |>.trans hc.symm

theorem weightedSource_norm (u w : ℝ) :
    ‖weightedSource (source μ) u w‖=‖u‖*‖w‖ := by
  rw [weightedSource_eq_const]
  rw [Lp.norm_const 2 μ (u*w) (by norm_num)]
  simp [norm_mul]

theorem inverse_regular_at_nonzero_source (u : ℝ) (hu : u≠0) (f : StrongDual ℝ ℝ) :
    ‖u-(normalFourEquiv (source μ) 1 (by norm_num)
      (by intro w; simp [source_norm])).symm f‖ ≤
      (4/(3*‖u‖^2))*‖normalFour (source μ) u-f‖ := by
  have he := inverse_lipschitz_at_weighted_datum (source μ) u ‖u‖
    (norm_pos_iff.mpr hu) (by intro w; rw [weightedSource_norm])
    ((normalFourEquiv (source μ) 1 (by norm_num) (by intro w; simp [source_norm])).symm f)
  simpa only [normalFour_inverse_solves] using he

end OperatorDerivativeRewrite.Foundation.BanachQuarticConstantSource
