import Foundation.GaussianDeterministicIntegral

/-! Actual full Malliavin derivatives of Brownian increments. Their local
normalization is distinguished from integrated whole-gradient energy.
No pathwise quadratic-variation claim is made in this module. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianLocalIncrementEnergy
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeProductL2
open GaussianContinuousRigidity GaussianDeterministicIntegral

theorem increment_closedDerivative_graph (s t : ℝ≥0) (hst : s ≤ t) :
    (wienerL2 t - wienerL2 s, fieldEmbedding (productTensor (intervalVector s t) gaussianOne)) ∈
      closedCylindricalDerivative.graph := by
  rw [wienerL2_sub s t hst]
  exact firstChaos_closedDerivative_graph _

def incrementDomain (s t : ℝ≥0) (hst : s ≤ t) : closedCylindricalDerivative.domain :=
  ⟨wienerL2 t - wienerL2 s, LinearPMap.mem_domain_iff.mpr
    ⟨_, increment_closedDerivative_graph s t hst⟩⟩

theorem increment_derivative (s t : ℝ≥0) (hst : s ≤ t) :
    closedCylindricalDerivative (incrementDomain s t hst) =
      fieldEmbedding (productTensor (intervalVector s t) gaussianOne) :=
  closedCylindricalDerivative.mem_graph_snd_inj (closedCylindricalDerivative.mem_graph _)
    (increment_closedDerivative_graph s t hst) rfl

/-- This is the norm of the ACTUAL full closed derivative, not a prescribed energy. -/
def incrementEnergy (s t : ℝ≥0) (hst : s ≤ t) : ℝ :=
  ‖closedCylindricalDerivative (incrementDomain s t hst)‖ ^ 2

theorem incrementEnergy_eq (s t : ℝ≥0) (hst : s ≤ t) :
    incrementEnergy s t hst = (t : ℝ) - s := by
  rw [incrementEnergy, increment_derivative, fieldEmbedding.norm_map,
    ← real_inner_self_eq_norm_sq, productTensor_inner,
    GaussianDeterministicGraphCore.gaussianOne_inner_self, mul_one,
    real_inner_self_eq_norm_sq, ← timeVector_sub s t hst]
  exact timeVector_sub_norm_sq s t hst

theorem normalized_incrementEnergy (t h : ℝ≥0) (hh : 0 < h) :
    incrementEnergy t (t + h) (le_add_of_nonneg_right h.coe_nonneg) / (h : ℝ) = 1 := by
  rw [incrementEnergy_eq]
  simp only [NNReal.coe_add, add_sub_cancel_left]
  exact div_self (ne_of_gt (show (0 : ℝ) < h from hh))

/-- Increment energies are additive, unlike the time integral of global energy. -/
theorem incrementEnergy_add (r s t : ℝ≥0) (hrs : r ≤ s) (hst : s ≤ t) :
    incrementEnergy r t (hrs.trans hst) =
      incrementEnergy r s hrs + incrementEnergy s t hst := by
  simp only [incrementEnergy_eq]
  ring

theorem incrementEnergy_eq_variance (s t : ℝ≥0) (hst : s ≤ t) :
    incrementEnergy s t hst = ‖wienerL2 t - wienerL2 s‖ ^ 2 := by
  rw [incrementEnergy_eq, wienerL2_sub_norm_sq s t hst]

/-- The integral of the proved unit local density recovers Brownian variance.
This equality alone is not a construction of pathwise quadratic variation. -/
theorem integrated_local_density (T : ℝ≥0) :
    (∫ _s in (0 : ℝ)..(T : ℝ), (1 : ℝ)) =
      incrementEnergy 0 T (by positivity) := by
  rw [incrementEnergy_eq]
  simp

end OperatorDerivativeRewrite.Foundation.GaussianLocalIncrementEnergy
