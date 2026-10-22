import Foundation.GaussianClockBochnerContraction
import Foundation.IBMClockWeakGraphObstruction

/-! A COMMON finite-energy derivative is recovered from an actual original
Bochner clock graph. This supplies the vector realization, not just separate
scalar derivative existence. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockBochnerConverse
open InfiniteGaussian IBMClockObservationGraph IBMClockObservationConverse
open GaussianClockBochnerContraction
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def fieldPullback (h : CoefficientSpace) (hh : ‖h‖ = 1) :
    Lp GaussianL2 2 GaussianCore.γ →ₗᵢ[ℝ] Lp GaussianL2 2 gaussianProduct :=
  Lp.compMeasurePreservingₗᵢ ℝ (firstChaosEmbedding h) (observation_measurePreserving h hh)

theorem fieldPullback_ae (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (f : Lp GaussianL2 2 GaussianCore.γ) :
    fieldPullback h hh f =ᵐ[gaussianProduct] fun ω => f (firstChaosEmbedding h ω) :=
  Lp.coeFn_compMeasurePreserving f (observation_measurePreserving h hh)

theorem scalar_pullback (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (f : Lp GaussianL2 2 GaussianCore.γ) (e : GaussianL2) :
    (innerSL ℝ e).compLp (fieldPullback h hh f) =
      pullback h hh ((innerSL ℝ e).compLp f) := by
  apply Lp.ext
  have hc := (observation_measurePreserving h hh).quasiMeasurePreserving.ae_eq_comp
    ((innerSL ℝ e).coeFn_compLp f)
  filter_upwards [(innerSL ℝ e).coeFn_compLp (fieldPullback h hh f),
    fieldPullback_ae h hh f, pullback_ae h hh ((innerSL ℝ e).compLp f), hc]
    with ω hi hf hp hc
  rw [hi, hf, hp]
  exact hc.symm

def recoveredField (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (V : Lp GaussianVectorL2 2 gaussianProduct) : Lp GaussianL2 2 GaussianCore.γ :=
  ProductL2Curry.flip gaussianProduct GaussianCore.γ ((recover h hh).compLp V)

theorem recoveredField_norm_le (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (V : Lp GaussianVectorL2 2 gaussianProduct) : ‖recoveredField h hh V‖ ≤ ‖V‖ := by
  rw [recoveredField, (ProductL2Curry.flip gaussianProduct GaussianCore.γ).norm_map]
  have hb : ‖(recover h hh).compLp V‖ ≤ 1 * ‖V‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(recover h hh).coeFn_compLp V] with ω hω
    rw [hω, one_mul]
    exact recover_norm_le h hh (V ω)
  simpa only [one_mul] using hb

theorem recovered_scalar (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (V : Lp GaussianVectorL2 2 gaussianProduct) (e : GaussianL2) :
    (innerSL ℝ e).compLp (recoveredField h hh V) = recover h hh (contract e V) := by
  have hr : ProductL2Curry.flip GaussianCore.γ gaussianProduct (recoveredField h hh V) =
      (recover h hh).compLp V := by
    apply (ProductL2Curry.flip gaussianProduct GaussianCore.γ).injective
    exact flip_involution GaussianCore.γ (recoveredField h hh V)
  have he := contract_flip GaussianCore.γ (recoveredField h hh V) e
  rw [hr, contract_comp] at he
  exact he.symm

theorem original_field_graph_recovery (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (f : Lp GaussianL2 2 GaussianCore.γ) (V : Lp GaussianVectorL2 2 gaussianProduct)
    (hu : (ProductL2Curry.flip gaussianProduct gaussianProduct (fieldPullback h hh f), V) ∈
      (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph) :
    ∀ e : GaussianL2, ((innerSL ℝ e).compLp f,
      (innerSL ℝ e).compLp (recoveredField h hh V)) ∈ GaussianCore.closedDerivative.graph := by
  intro e
  have hg := contract_graph _ V hu e
  rw [contract_flip, scalar_pullback] at hg
  have hc := converse_graph h hh hg
  rwa [recovered_scalar]

theorem positive_section_not_clock_domain (h : CoefficientSpace) (hh : ‖h‖ = 1)
    (c : ℝ) (hc : 0 < c) :
    ProductL2Curry.flip gaussianProduct gaussianProduct
      (fieldPullback h hh (IBMClockWeakGraphObstruction.sectionClass c)) ∉
        (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).domain := by
  intro hu
  obtain ⟨V, hV⟩ := LinearPMap.mem_domain_iff.mp hu
  have hg := original_field_graph_recovery h hh _ V hV
  exact IBMClockWeakGraphObstruction.no_common_closed_derivative c hc
    ⟨recoveredField h hh V, hg⟩

end OperatorDerivativeRewrite.Foundation.IBMClockBochnerConverse
