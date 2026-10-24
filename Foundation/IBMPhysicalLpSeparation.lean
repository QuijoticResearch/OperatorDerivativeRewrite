import Foundation.IBMPhysicalCellErrorRate

/-! Physical real dual tests separate actual H^-1-valued Gaussian L2 classes.
The proof uses existing Lp simple-function density, not an assumed pointwise
common exceptional set over an uncountable family of tests. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalLpSeparation
open InfiniteGaussian IBMPhysicalWeakWiener
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _

theorem annihilator_zero (Z : Lp Kernel 2 gaussianProduct)
    (hZ : ∀ L : Tests, L.compLpL 2 gaussianProduct Z = 0) : Z = 0 := by
  have hall (W : Lp Kernel 2 gaussianProduct) : inner ℝ Z W = 0 := by
    apply Lp.induction (by simp) (fun W => inner ℝ Z W = 0)
    · intro h s hs hfin
      rw [Lp.simpleFunc.coe_indicatorConst, L2.inner_def]
      apply integral_eq_zero_of_ae
      have he := hZ (innerSL ℝ h)
      filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := gaussianProduct)
          (hs := hs) (hμs := hfin.ne) (c := h),
        (innerSL ℝ h).coeFn_compLpL Z, Lp.coeFn_zero ℝ 2 gaussianProduct]
        with Y hw hz h0
      rw [he, h0] at hz
      change (0 : ℝ) = inner ℝ h (Z Y) at hz
      have hz' : inner ℝ (Z Y) h = 0 := by
        simpa only [innerSL_apply_apply, real_inner_comm] using hz.symm
      rw [hw]
      change inner ℝ (Z Y) (s.indicator (fun _ => h) Y) = (0 : ℝ)
      by_cases hYs : Y ∈ s
      · simpa only [Set.indicator_of_mem hYs] using hz'
      · simp only [Set.indicator_of_notMem hYs, inner_zero_right]
    · intro V W _hV _hW _hd hV hW
      rw [inner_add_right, hV, hW, add_zero]
    · exact isClosed_eq (innerSL ℝ Z).continuous continuous_const
  exact inner_self_eq_zero.mp (hall Z)

theorem ext (U V : Lp Kernel 2 gaussianProduct)
    (h : ∀ L : Tests, L.compLpL 2 gaussianProduct U = L.compLpL 2 gaussianProduct V) : U = V := by
  apply sub_eq_zero.mp
  apply annihilator_zero
  intro L
  rw [map_sub, h L, sub_self]

end OperatorDerivativeRewrite.Foundation.IBMPhysicalLpSeparation
