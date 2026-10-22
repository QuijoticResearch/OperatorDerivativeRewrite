import Foundation.GaussianClosedDerivativePrimitive
import Foundation.IBMClockSectionEnergyObstruction

/-! Scalar original Gaussian graphs with ONE square-integrable vector derivative
force a genuine vector primitive. Separate scalar derivatives without a common
finite-energy realization do not meet this hypothesis. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianWeakVectorPrimitive
open GaussianCore GaussianClosedDerivativePrimitive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
theorem scalar_integral_eq (e : E) (g : Lp E 2 γ) (a b : ℝ) :
    (∫ x in Icc a b, ((innerSL ℝ e).compLp g) x) =
      inner ℝ e (∫ x in Icc a b, g x) := by
  have hv : (volume : Measure ℝ) ≪ γ :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)
  have he : ((innerSL ℝ e).compLp g) =ᵐ[volume.restrict (Icc a b)]
      fun x => inner ℝ e (g x) :=
    ae_restrict_of_ae (hv.ae_eq ((innerSL ℝ e).coeFn_compLp g))
  rw [integral_congr_ae he]
  obtain ⟨C, _, hC, hcmp⟩ := GaussianLocalSobolev.exists_local_measure_comparison a b
  exact (innerSL ℝ e).integral_comp_comm
    (((Lp.memLp g).of_measure_le_smul hC hcmp).integrable (by norm_num))

theorem weak_graph_primitive (f g : Lp E 2 γ)
    (hfg : ∀ e : E, ((innerSL ℝ e).compLp f, (innerSL ℝ e).compLp g) ∈
      closedDerivative.graph) {a b : ℝ} (hab : a < b) :
    ∃ v : E, f =ᵐ[volume.restrict (Icc a b)] fun x => v + ∫ y in Icc a x, g y := by
  let e : ℕ → E := TopologicalSpace.denseSeq E
  have hc (n : ℕ) := closed_graph_primitive (hfg (e n)) hab
  choose c hc using hc
  have hv : (volume : Measure ℝ) ≪ γ :=
    ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)
  have hf : ∀ n, ∀ᵐ x ∂volume.restrict (Icc a b),
      inner ℝ (e n) (f x) = c n + inner ℝ (e n) (∫ y in Icc a x, g y) := by
    intro n
    filter_upwards [hc n, ae_restrict_of_ae
      (hv.ae_eq ((innerSL ℝ (e n)).coeFn_compLp f))] with x hx hf
    rw [hf, scalar_integral_eq] at hx
    exact hx
  have hall := ae_all_iff.mpr hf
  obtain ⟨z, hz, hzl⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (show (volume : Measure ℝ) (Icc a b) ≠ 0 by
      rw [Real.volume_Icc]
      exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne') hall
  refine ⟨f z - ∫ y in Icc a z, g y, ?_⟩
  filter_upwards [hall] with x hx
  apply (TopologicalSpace.denseRange_denseSeq E).eq_of_inner_right (𝕜 := ℝ)
  intro n
  change inner ℝ (e n) (f x) = _
  rw [inner_add_right, inner_sub_right]
  linarith [hx n, hzl n]

end OperatorDerivativeRewrite.Foundation.GaussianWeakVectorPrimitive
