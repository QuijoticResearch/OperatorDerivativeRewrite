import Foundation.IBMNativeGridEscape
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! The ORIGINAL projected native IBM integrals fail even weak reconstruction
on all intrinsic L2 observables. This does not contradict the verified spatial
test calculus or rule out a distribution-valued stochastic calculus. -/
noncomputable section
open Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeWeakObstruction

theorem exists_unbounded_inner_of_norm_escape {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (u : ℕ → E)
    (hu : Tendsto (fun N => ‖u N‖) atTop atTop) :
    ∃ v : E, ∀ C : ℝ, ∃ N : ℕ, C < |inner ℝ (u N) v| := by
  by_contra h
  push_neg at h
  have hp : ∀ v : E, ∃ C : ℝ, ∀ N : ℕ, ‖innerSL ℝ (u N) v‖ ≤ C := by
    intro v
    simpa only [innerSL_apply_apply,Real.norm_eq_abs] using h v
  obtain ⟨C,hC⟩ := banach_steinhaus hp
  have hh := (tendsto_atTop.mp hu) (C+1)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  have hb := hC N
  rw [innerSL_apply_norm] at hb
  linarith [hN N le_rfl]

open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMRawGridCompensation
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _ IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem exists_original_unbounded_observable (T : ℝ≥0) (hT : 0 < T) :
    ∃ v : IntrinsicSpace, ∀ C : ℝ, ∃ N : ℕ,
      C < |inner ℝ (jointDivergence (gridInput (T/(N+1)) (N+1))) v| :=
  exists_unbounded_inner_of_norm_escape _ (IBMNativeGridEscape.original_native_norm_escape T hT)

theorem exists_original_nonconvergent_observable (T : ℝ≥0) (hT : 0 < T) :
    ∃ v : IntrinsicSpace, ∀ c : ℝ, ¬ Tendsto
      (fun N : ℕ => inner ℝ (jointDivergence (gridInput (T/(N+1)) (N+1))) v) atTop (𝓝 c) := by
  obtain ⟨v,hv⟩ := exists_original_unbounded_observable T hT
  refine ⟨v,fun c hc => ?_⟩
  obtain ⟨C,hC⟩ := hc.cauchySeq.isBounded_range.exists_norm_le
  obtain ⟨N,hN⟩ := hv C
  have hb := hC _ (mem_range_self N)
  rw [Real.norm_eq_abs] at hb
  exact (not_lt_of_ge hb) hN

theorem no_original_weak_limit (T : ℝ≥0) (hT : 0 < T) (w : IntrinsicSpace) :
    ¬ (∀ v : IntrinsicSpace, Tendsto
      (fun N : ℕ => inner ℝ (jointDivergence (gridInput (T/(N+1)) (N+1))) v) atTop
        (𝓝 (inner ℝ w v))) := by
  obtain ⟨v,hv⟩ := exists_original_nonconvergent_observable T hT
  exact fun h => hv _ (h v)

theorem no_original_weak_subsequence (T : ℝ≥0) (hT : 0 < T)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (w : IntrinsicSpace) :
    ¬ (∀ v : IntrinsicSpace, Tendsto
      (fun N : ℕ => inner ℝ (jointDivergence (gridInput (T/(φ N+1)) (φ N+1))) v) atTop
        (𝓝 (inner ℝ w v))) := by
  intro h
  have he := (IBMNativeGridEscape.original_native_norm_escape T hT).comp hφ.tendsto_atTop
  obtain ⟨v,hv⟩ := exists_unbounded_inner_of_norm_escape _ he
  obtain ⟨C,hC⟩ := (h v).cauchySeq.isBounded_range.exists_norm_le
  obtain ⟨N,hN⟩ := hv C
  have hb := hC _ (mem_range_self N)
  rw [Real.norm_eq_abs] at hb
  exact (not_lt_of_ge hb) hN

end OperatorDerivativeRewrite.Foundation.IBMNativeWeakObstruction
