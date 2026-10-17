import Foundation.BrownianTimeChangedConditionalKernel
import Foundation.BrownianStickyNontriviality

/-! Positive holding forces a genuine atom at zero at some deterministic
positive time in every horizon. No assertion for every time is inferred. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianStickyBoundaryAtom
open InfiniteGaussian BrownianMassRandomTimeChange BrownianStickyNontriviality
open BrownianTimeChangedConditionalKernel BrownianClockMeasureTransport BrownianStickyOccupation
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath
  BrownianMassRandomTimeChange.inverse BrownianRandomMassClock.mass

theorem exists_boundary_atom (κ T : ℝ≥0) (hκ : 0 < κ) (hT : 0 < T) :
    ∃ s : ℝ≥0, 0 < s ∧ s ≤ T ∧ 0 < gaussianProduct {ω | changedPath κ ω s = 0} := by
  by_contra hno
  have hz (s : ℝ≥0) (hs : 0 < s) (hsT : s ≤ T) :
      gaussianProduct {ω | changedPath κ ω s = 0} = 0 := by
    by_contra hn
    exact hno ⟨s,hs,hsT,bot_lt_iff_ne_bot.mpr hn⟩
  have hq : Measurable (fun z : ℝ × SampleSpace => (z.1.toNNReal,z.2)) :=
    (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
  have hm : MeasurableSet {z : ℝ × SampleSpace | changedPath κ z.2 z.1.toNNReal ≠ 0} :=
    (measurableSet_eq_fun ((changedPath_joint κ).comp hq) measurable_const).compl
  have ht : ∀ᵐ r ∂(volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)),
      ∀ᵐ ω ∂gaussianProduct, changedPath κ ω r.toNNReal ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hs : 0 < r.toNNReal := Real.toNNReal_pos.mpr hr.1
    have hsT : r.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hr.2
    simpa only [ae_iff, not_not] using hz r.toNNReal hs hsT
  have hω := (Measure.ae_ae_comm hm).mp ht
  have hocc : (fun ω => occupation κ ω T) =ᵐ[gaussianProduct] (fun _ => 0) := by
    filter_upwards [hω] with ω hw
    have hzero : ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)))
        {r | changedPath κ ω r.toNNReal = 0} = 0 := by
      simpa only [ae_iff, not_not] using hw
    have hE : MeasurableSet {t : ℝ≥0 | changedPath κ ω t = 0} :=
      (isClosed_eq (changedPath κ ω).continuous continuous_const).measurableSet
    unfold occupation
    rw [ordinaryTime_cut _ hE T]
    change (((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)))
      {r | changedPath κ ω r.toNNReal = 0}).toReal = 0
    rw [hzero]
    rfl
  have hp := expected_occupation_pos κ T hκ hT
  rw [integral_congr_ae hocc, integral_zero] at hp
  exact (lt_irrefl 0) hp

theorem exists_positive_boundary_marginal (κ T : ℝ≥0) (hκ : 0 < κ) (hT : 0 < T) :
    ∃ s : ℝ≥0, 0 < s ∧ s ≤ T ∧ 0 < marginal κ s {0} := by
  obtain ⟨s,hs,hsT,hp⟩ := exists_boundary_atom κ T hκ hT
  refine ⟨s,hs,hsT,?_⟩
  rw [marginal, Measure.map_apply (state_measurable κ s) (measurableSet_singleton 0)]
  exact hp

theorem boundary_row_formula (κ s t : ℝ≥0) (hs : marginal κ s {0} ≠ 0) (A : Set ℝ) :
    pairKernel κ s t 0 A = (marginal κ s {0})⁻¹*pairLaw κ s t ({0} ×ˢ A) :=
  condDistrib_apply_of_ne_zero (state_measurable κ s) (state_measurable κ t) 0 hs A

end OperatorDerivativeRewrite.Foundation.BrownianStickyBoundaryAtom
