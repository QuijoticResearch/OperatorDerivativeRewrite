import Foundation.GaussianDivergenceRecovery
import Foundation.BochnerClosedOperator

/-! Bounded source-divergence recovery with arbitrary Bochner-L2 parameters.
The domain uses the original closed source graph in every fiber. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.GaussianBochnerDivergenceRecovery
open InfiniteGaussian GaussianNumberSectors GaussianDivergenceRecovery
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def fiberRecovery : Lp GaussianL2 2 μ →L[ℝ] Lp GaussianVectorL2 2 μ :=
  recoveryOperator.compLpL 2 μ

def fiberCenter : Lp GaussianL2 2 μ →L[ℝ] Lp GaussianL2 2 μ :=
  ((ContinuousLinearMap.id ℝ GaussianL2)-projection 0).compLpL 2 μ

theorem fiberRecovery_coeFn (u : Lp GaussianL2 2 μ) :
    fiberRecovery μ u =ᵐ[μ] fun x => recovery (u x) :=
  recoveryOperator.coeFn_compLpL u

theorem fiberCenter_coeFn (u : Lp GaussianL2 2 μ) :
    fiberCenter μ u =ᵐ[μ] fun x => u x-projection 0 (u x) :=
  ((ContinuousLinearMap.id ℝ GaussianL2)-projection 0).coeFn_compLpL u

theorem fiberRecovery_graph (u : Lp GaussianL2 2 μ) :
    (fiberRecovery μ u, fiberCenter μ u) ∈
      (BochnerClosedOperator.lift μ hilbertDivergence).graph := by
  rw [BochnerClosedOperator.mem_lift_graph_iff]
  filter_upwards [fiberRecovery_coeFn μ u, fiberCenter_coeFn μ u] with x hr hc
  rw [hr,hc]
  exact recovery_graph (u x)

theorem fiberRecovery_norm_le (u : Lp GaussianL2 2 μ) : ‖fiberRecovery μ u‖ ≤ ‖u‖ := by
  apply (Lp.norm_le_mul_norm_of_ae_le_mul (c := (1 : ℝ)) ?_).trans_eq (one_mul ‖u‖)
  filter_upwards [fiberRecovery_coeFn μ u] with x hx
  rw [hx,one_mul]
  exact recovery_norm_le (u x)

theorem fiberRecovery_minimal_norm (u : Lp GaussianL2 2 μ) (v : Lp GaussianVectorL2 2 μ)
    (hv : (v,fiberCenter μ u) ∈ (BochnerClosedOperator.lift μ hilbertDivergence).graph) :
    ‖fiberRecovery μ u‖ ≤ ‖v‖ := by
  rw [BochnerClosedOperator.mem_lift_graph_iff] at hv
  apply (Lp.norm_le_mul_norm_of_ae_le_mul (c := (1 : ℝ)) ?_).trans_eq (one_mul ‖v‖)
  filter_upwards [hv, fiberRecovery_coeFn μ u, fiberCenter_coeFn μ u] with x hv hr hc
  rw [hc] at hv
  rw [hr,one_mul]
  exact recovery_minimal_norm (u x) (v x) hv

theorem exists_fiber_divergence_iff_centered (u : Lp GaussianL2 2 μ) :
    (∃ v : Lp GaussianVectorL2 2 μ,
      (v,u) ∈ (BochnerClosedOperator.lift μ hilbertDivergence).graph) ↔
        ∀ᵐ x ∂μ, inner ℝ gaussianOne (u x) = 0 := by
  constructor
  · rintro ⟨v,hv⟩
    rw [BochnerClosedOperator.mem_lift_graph_iff] at hv
    filter_upwards [hv] with x hx
    exact (exists_divergence_iff_centered (u x)).mp ⟨v x,hx⟩
  · intro hu
    have he : fiberCenter μ u = u := by
      apply Lp.ext
      filter_upwards [hu,fiberCenter_coeFn μ u] with x hx hc
      rw [hc,projection_zero,hx,zero_smul,sub_zero]
    refine ⟨fiberRecovery μ u, ?_⟩
    have hg := fiberRecovery_graph μ u
    rw [he] at hg
    exact hg

end OperatorDerivativeRewrite.Foundation.GaussianBochnerDivergenceRecovery
