import Foundation.GaussianSpectralPoincare
import Foundation.GaussianPredictableChaosCore

/-! Gaussian Poincare and quantitative rigidity on the original, independent
predictable Sobolev domain. The comparison field is the actual Gaussian mean. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianQuantitativeRigidity
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianProductDerivative
open GaussianPredictableFull GaussianAdaptedGraphCore GaussianDeterministicGraphCore
open GaussianPredictableChaosCore GaussianContinuousRigidity GaussianNumberSectors
attribute [local instance] timeHilbert_secondCountable coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem field_poincare_sq {u : TimeProbabilityL2} {v : ProductDerivativeL2}
    (hd : (u, v) ∈ derivative.graph) : ‖u - meanProjection u‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have hm : scalarCurry (meanProjection u) = vacuumProjection.compLp (scalarCurry u) := by
    change scalarCurry (scalarCurry.symm _) = _
    exact scalarCurry.apply_symm_apply _
  have he : ∀ᵐ t ∂(volume : Measure ℝ),
      ‖scalarCurry (u - meanProjection u) t‖ ^ 2 ≤ ‖vectorCurry v t‖ ^ 2 := by
    rw [map_sub, hm]
    filter_upwards [Lp.coeFn_sub (scalarCurry u) (vacuumProjection.compLp (scalarCurry u)),
      vacuumProjection.coeFn_compLp (scalarCurry u),
      (derivative_fiber_graph_iff u v).mp hd] with t hs hm hf
    rw [hs, Pi.sub_apply, hm]
    exact gaussian_poincare_sq hf
  have hi := integral_mono_ae
    (Lp.memLp (scalarCurry (u - meanProjection u))).norm.integrable_sq
    (Lp.memLp (vectorCurry v)).norm.integrable_sq he
  rw [← BochnerL2Dominated.norm_sq_integral, ← BochnerL2Dominated.norm_sq_integral,
    scalarCurry.norm_map, vectorCurry.norm_map] at hi
  exact hi

theorem field_poincare {u : TimeProbabilityL2} {v : ProductDerivativeL2}
    (hd : (u, v) ∈ derivative.graph) : ‖u - meanProjection u‖ ≤ ‖v‖ := by
  have h := field_poincare_sq hd
  nlinarith [norm_nonneg (u - meanProjection u), norm_nonneg v]

theorem meanProjection_deterministic_profile (u : fullPredictable) :
    ∃ a : TimeHilbert, meanProjection u = productTensor a gaussianOne :=
  (derivative_zero_iff_deterministic _).mp
    (completedGraph_le_derivative (meanProjection_graph u))

theorem quantitative_rigidity (u : fullPredictable) (v : ProductDerivativeL2)
    (hd : ((u : TimeProbabilityL2), v) ∈ derivative.graph) :
    ∃ a : TimeHilbert, ‖(u : TimeProbabilityL2) - productTensor a gaussianOne‖ ≤
      ‖closedCylindricalDerivative (independentIntegralDomain u v hd) - fieldEmbedding u‖ := by
  obtain ⟨a, ha⟩ := meanProjection_deterministic_profile u
  refine ⟨a, ?_⟩
  rw [independent_sensitivity_norm, ← ha]
  exact field_poincare hd

theorem distance_deterministic_le_sensitivity (u : fullPredictable) (v : ProductDerivativeL2)
    (hd : ((u : TimeProbabilityL2), v) ∈ derivative.graph) :
    Metric.infDist (u : TimeProbabilityL2)
      (Set.range (fun a : TimeHilbert => productTensor a gaussianOne)) ≤
        ‖closedCylindricalDerivative (independentIntegralDomain u v hd) - fieldEmbedding u‖ := by
  obtain ⟨a, ha⟩ := quantitative_rigidity u v hd
  exact (Metric.infDist_le_dist_of_mem
    (s := Set.range (fun a : TimeHilbert => productTensor a gaussianOne)) ⟨a, rfl⟩).trans
    (by simpa only [dist_eq_norm] using ha)

end OperatorDerivativeRewrite.Foundation.GaussianQuantitativeRigidity
