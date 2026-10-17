import Foundation.BrownianStickyL2Transitions

/-! Positivity, constants, and the actual coordinate of the two-time Hilbert
operators. These properties do not imply Chapman--Kolmogorov or stationarity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianStickyL2MarkovProperties
open InfiniteGaussian BrownianTimeChangedConditionalKernel BrownianStickyL2Transitions
open HilbertRepresentation BrownianTimeChangedVariance
set_option backward.isDefEq.respectTransparency false

def one (κ t : ℝ≥0) : StateL2 κ t :=
  (MemLp.of_bound stronglyMeasurable_const.aestronglyMeasurable 1
    (Eventually.of_forall fun _ => by norm_num) :
      MemLp (fun _ : ℝ => (1 : ℝ)) 2 (marginal κ t)).toLp _

theorem one_coeFn (κ t : ℝ≥0) : one κ t =ᵐ[marginal κ t] fun _ => 1 := MemLp.coeFn_toLp _

theorem embedding_one (κ t : ℝ≥0) : embedding κ t (one κ t) =ᵐ[gaussianProduct] fun _ => 1 :=
  (embedding_coeFn κ t (one κ t)).trans
    ((state_preserving κ t).quasiMeasurePreserving.ae_eq_comp (one_coeFn κ t))

theorem transition_one (κ s t : ℝ≥0) : transition κ s t (one κ t) = one κ s := by
  have he : embedding κ t (one κ t) = embedding κ s (one κ s) :=
    Lp.ext ((embedding_one κ t).trans (embedding_one κ s).symm)
  change predictableAdjoint (embedding κ s) (embedding κ t (one κ t)) = one κ s
  rw [he, predictableAdjoint_isometry_apply]

theorem transition_nonnegative (κ s t : ℝ≥0) (f : StateL2 κ t)
    (hf : 0 ≤ᵐ[marginal κ t] f) : 0 ≤ᵐ[marginal κ s] transition κ s t f := by
  have ht : 0 ≤ᵐ[gaussianProduct] (fun ω => f (state κ t ω)) :=
    ae_of_ae_map (state_measurable κ t).aemeasurable hf
  have hce := condExp_nonneg (m := MeasurableSpace.comap (state κ s) inferInstance) ht
  change ∀ᵐ x ∂gaussianProduct.map (state κ s), 0 ≤ transition κ s t f x
  apply (ae_map_iff (state_measurable κ s).aemeasurable
    (measurableSet_le measurable_const (Lp.stronglyMeasurable _).measurable)).mpr
  filter_upwards [hce, transition_condExp κ s t f,
    embedding_coeFn κ s (transition κ s t f)] with ω hp he hc
  rw [← hc, he]
  exact hp

theorem coordinate_memLp (κ t : ℝ≥0) : MemLp (fun x : ℝ => x) 2 (marginal κ t) := by
  apply (memLp_map_measure_iff stronglyMeasurable_id.aestronglyMeasurable
    (state_measurable κ t).aemeasurable).mpr
  exact (memLp_two_iff_integrable_sq (state_measurable κ t).aestronglyMeasurable).mpr
    (changed_square_integrable κ t)

def coordinate (κ t : ℝ≥0) : StateL2 κ t := (coordinate_memLp κ t).toLp _

theorem coordinate_coeFn (κ t : ℝ≥0) : coordinate κ t =ᵐ[marginal κ t] fun x => x :=
  MemLp.coeFn_toLp _

theorem embedding_coordinate (κ t : ℝ≥0) :
    embedding κ t (coordinate κ t) =ᵐ[gaussianProduct] state κ t :=
  (embedding_coeFn κ t (coordinate κ t)).trans
    ((state_preserving κ t).quasiMeasurePreserving.ae_eq_comp (coordinate_coeFn κ t))

theorem transition_coordinate (κ s t : ℝ≥0) (hst : s ≤ t) :
    transition κ s t (coordinate κ t) = coordinate κ s := by
  apply (embedding κ s).injective
  apply Lp.ext
  have ht : (fun ω => coordinate κ t (state κ t ω)) =ᵐ[gaussianProduct] state κ t :=
    (state_preserving κ t).quasiMeasurePreserving.ae_eq_comp (coordinate_coeFn κ t)
  exact (transition_condExp κ s t (coordinate κ t)).trans
    ((condExp_congr_ae ht).trans ((current_mean κ s t hst).trans (embedding_coordinate κ s).symm))

theorem coordinate_norm_sq (κ t : ℝ≥0) : ‖coordinate κ t‖^2 =
    ∫ ω, (BrownianMassRandomTimeChange.inverse κ ω t : ℝ) ∂gaussianProduct := by
  rw [← (embedding κ t).norm_map, ← real_inner_self_eq_norm_sq, L2.inner_def]
  have he : (fun ω => inner ℝ (embedding κ t (coordinate κ t) ω)
      (embedding κ t (coordinate κ t) ω)) =ᵐ[gaussianProduct] (fun ω => (state κ t ω)^2) := by
    filter_upwards [embedding_coordinate κ t] with ω hω
    rw [hω, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [integral_congr_ae he]
  exact changed_second_moment κ t

end OperatorDerivativeRewrite.Foundation.BrownianStickyL2MarkovProperties
