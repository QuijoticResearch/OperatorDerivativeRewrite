import Foundation.IBMPhysicalLpSeparation

/-! The physical-dual L2 separation proof on an arbitrary actual measure.
This extends the existing Gaussian-only theorem to the predictable time measure. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalMeasureSeparation
open IBMPhysicalWeakWiener
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem annihilator_zero (Z : Lp Kernel 2 μ)
    (hZ : ∀ L : Tests, L.compLpL 2 μ Z = 0) : Z = 0 := by
  have hall (W : Lp Kernel 2 μ) : inner ℝ Z W = 0 := by
    apply Lp.induction (by simp) (fun W => inner ℝ Z W = 0)
    · intro h s hs hfin
      rw [Lp.simpleFunc.coe_indicatorConst, L2.inner_def]
      apply integral_eq_zero_of_ae
      have he := hZ (innerSL ℝ h)
      filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := μ)
          (hs := hs) (hμs := hfin.ne) (c := h),
        (innerSL ℝ h).coeFn_compLpL Z, Lp.coeFn_zero ℝ 2 μ] with x hw hz h0
      rw [he,h0] at hz
      change (0 : ℝ) = inner ℝ h (Z x) at hz
      have hz' : inner ℝ (Z x) h = 0 := by
        simpa only [innerSL_apply_apply, real_inner_comm] using hz.symm
      rw [hw]
      change inner ℝ (Z x) (s.indicator (fun _ => h) x) = (0 : ℝ)
      by_cases hxs : x ∈ s
      · simpa only [Set.indicator_of_mem hxs] using hz'
      · simp only [Set.indicator_of_notMem hxs, inner_zero_right]
    · intro V W _hV _hW _hd hV hW
      rw [inner_add_right,hV,hW,add_zero]
    · exact isClosed_eq (innerSL ℝ Z).continuous continuous_const
  exact inner_self_eq_zero.mp (hall Z)

theorem ext (U V : Lp Kernel 2 μ)
    (h : ∀ L : Tests, L.compLpL 2 μ U = L.compLpL 2 μ V) : U = V := by
  apply sub_eq_zero.mp
  apply annihilator_zero μ
  intro L
  rw [map_sub,h L,sub_self]

end OperatorDerivativeRewrite.Foundation.IBMPhysicalMeasureSeparation
