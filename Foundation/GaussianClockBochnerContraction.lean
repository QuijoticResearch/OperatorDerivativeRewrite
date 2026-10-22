import Foundation.IBMClockObservationConverse
import Foundation.ProductL2Flip
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! Genuine L²-weighted Bochner contraction of the original closed clock graph,
and its compatibility with the existing scalar L² flip. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianClockBochnerContraction
open InfiniteGaussian
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def contract (e : GaussianL2) : Lp E 2 gaussianProduct →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).lpPairing gaussianProduct 2 2 e

omit [CompleteSpace E] in
theorem weighted_integrable (e : GaussianL2) (u : Lp E 2 gaussianProduct) :
    Integrable (fun ω => e ω • u ω) gaussianProduct := by
  have h : MemLp (fun ω => e ω • u ω) 1 gaussianProduct :=
    (Lp.memLp e).smul (Lp.memLp u)
  exact h.integrable le_rfl

theorem contract_integral (e : GaussianL2) (u : Lp E 2 gaussianProduct) :
    contract e u = ∫ ω, e ω • u ω ∂gaussianProduct :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).lpPairing_eq_integral e u

theorem contract_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (e : GaussianL2) (u : Lp E 2 gaussianProduct) :
    contract e (L.compLp u) = L (contract e u) := by
  rw [contract_integral, contract_integral, ← L.integral_comp_comm (weighted_integrable e u)]
  apply integral_congr_ae
  filter_upwards [L.coeFn_compLp u] with ω hω
  rw [hω, map_smul]

theorem contract_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (e : GaussianL2) (u : Lp H 2 gaussianProduct) (v : H) :
    inner ℝ v (contract e u) =
      inner ℝ (BochnerClosedOperator.tensor gaussianProduct e v) u := by
  rw [contract_integral, ← integral_inner (weighted_integrable e u) v, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct e v] with ω hω
  rw [hω, real_inner_smul_left, real_inner_smul_right]

theorem contract_flip {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    [SecondCountableTopology (Lp ℝ 2 ν)] (f : Lp GaussianL2 2 ν) (e : GaussianL2) :
    contract e (ProductL2Curry.flip ν gaussianProduct f) =
      (innerSL ℝ e).compLp f := by
  apply ext_inner_left ℝ
  intro q
  rw [contract_inner]
  have hi := (ProductL2Curry.flip ν gaussianProduct).inner_map_map
    (BochnerClosedOperator.tensor ν q e) f
  rw [ProductL2Curry.flip_tensor] at hi
  rw [hi, L2_inner_eq_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [BochnerClosedOperator.tensor_coeFn ν q e,
    (innerSL ℝ e).coeFn_compLp f] with x ht hc
  rw [ht, hc, real_inner_smul_left, Real.inner_apply, innerSL_apply_apply]

theorem flip_involution {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    [SecondCountableTopology (Lp ℝ 2 ν)] (f : Lp GaussianL2 2 ν) :
    ProductL2Curry.flip gaussianProduct ν (ProductL2Curry.flip ν gaussianProduct f) = f := by
  have hs (F : Lp ℝ 2 (ν.prod gaussianProduct)) :
      ProductL2Curry.swap gaussianProduct ν (ProductL2Curry.swap ν gaussianProduct F) = F := by
    apply Lp.ext
    have ha := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
      (ProductL2Curry.swap_coeFn ν gaussianProduct F)
    filter_upwards [ProductL2Curry.swap_coeFn gaussianProduct ν
      (ProductL2Curry.swap ν gaussianProduct F), ha] with ω h1 h2
    exact h1.trans h2
  change (ProductL2Curry.curryEquiv ν gaussianProduct)
    (ProductL2Curry.swap gaussianProduct ν
      ((ProductL2Curry.curryEquiv gaussianProduct ν).symm
        ((ProductL2Curry.curryEquiv gaussianProduct ν)
          (ProductL2Curry.swap ν gaussianProduct
            ((ProductL2Curry.curryEquiv ν gaussianProduct).symm f))))) = f
  rw [LinearIsometryEquiv.symm_apply_apply, hs, LinearIsometryEquiv.apply_symm_apply]

theorem contract_graph (u : Lp GaussianL2 2 gaussianProduct)
    (V : Lp GaussianVectorL2 2 gaussianProduct)
    (hu : (u, V) ∈ (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph)
    (e : GaussianL2) :
    (contract e u, contract e V) ∈ closedCylindricalDerivative.graph := by
  let S := closedCylindricalDerivative.graph
  let : IsClosed (S : Set (GaussianL2 × GaussianVectorL2)) :=
    closedCylindricalDerivative_isClosed
  let w : SampleSpace → GaussianL2 × GaussianVectorL2 := fun ω => (e ω • u ω, e ω • V ω)
  have hw : Integrable w gaussianProduct :=
    (weighted_integrable e u).prodMk (weighted_integrable e V)
  have ha : ∀ᵐ ω ∂gaussianProduct, w ω ∈ S := by
    filter_upwards [(BochnerClosedOperator.mem_lift_graph_iff _ _ _ _).mp hu] with ω hω
    exact S.smul_mem (e ω) hω
  have hq : S.mkQL (∫ ω, w ω ∂gaussianProduct) = 0 := by
    rw [← S.mkQL.integral_comp_comm hw]
    apply integral_eq_zero_of_ae
    filter_upwards [ha] with ω hω
    exact (Submodule.Quotient.mk_eq_zero S).mpr hω
  have hm := (Submodule.Quotient.mk_eq_zero S).mp hq
  rw [show (∫ ω, w ω ∂gaussianProduct) =
    (∫ ω, e ω • u ω ∂gaussianProduct, ∫ ω, e ω • V ω ∂gaussianProduct) from
      integral_pair (weighted_integrable e u) (weighted_integrable e V)] at hm
  simpa only [← contract_integral] using hm

end OperatorDerivativeRewrite.Foundation.GaussianClockBochnerContraction
