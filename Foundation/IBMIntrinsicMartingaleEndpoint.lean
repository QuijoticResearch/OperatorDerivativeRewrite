import Foundation.IBMCofinalPast

/-! Genuine terminal identification for cofinal countable-grid integration.
No right-continuous modification or Brownian law is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicMartingaleEndpoint
open IBMNaturalFiltrationObstruction IBMTimeAveragedObservable
open IBMIntrinsicQuadraticMartingale IBMIntrinsicMartingaleStep IBMIntrinsicMartingaleGrid
open IBMIntrinsicMartingaleRefinement IBMIntrinsicMartingaleSeries IBMCofinalPast
set_option backward.isDefEq.respectTransparency false

theorem projection_value {s T : ℝ≥0} (hs : s ≤ T) :
    (past s).starProjection (valueClass T : JointL2) = (valueClass s : JointL2) := by
  apply Lp.ext
  exact (projection_ae s (valueClass T : JointL2)).trans
    ((condExp_congr_ae (valueClass_ae T)).trans
      ((actual_martingale.condExp_ae_eq hs).trans (valueClass_ae s).symm))

theorem valueClass_tendsto (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (T : ℝ≥0)
    (hT : ∀ n, τ n ≤ T) (hlim : Tendsto τ atTop (𝓝 T)) :
    Tendsto (fun n => (valueClass (τ n) : JointL2)) atTop (𝓝 (valueClass T : JointL2)) := by
  have ht := projection_tendsto τ hτ T hT hlim (valueClass T : JointL2)
  have he : (past T).starProjection (valueClass T : JointL2) = (valueClass T : JointL2) :=
    Submodule.starProjection_eq_self_iff.mpr (valueClass T).property
  rw [he] at ht
  simpa only [projection_value (hT _)] using ht

theorem split_stepClass {s u : ℝ≥0} (hsu : s ≤ u) (t : ℝ≥0) (a : Coefficient s) :
    stepClass s u a + stepClass u t (later hsu a) = stepClass s t a := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (stepClass s u a) (stepClass u t (later hsu a)),
    stepClass_ae s u a, stepClass_ae u t (later hsu a), stepClass_ae s t a] with ω hh h1 h2 h3
  rw [hh, Pi.add_apply, h1, h2, h3]
  exact congrFun (split_step hsu t a) ω

theorem retained_step_tendsto (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (T : ℝ≥0)
    (hT : ∀ n, τ n ≤ T) (hlim : Tendsto τ atTop (𝓝 T)) (a : Coefficient (τ 0)) :
    Tendsto (fun n => stepClass (τ 0) (τ n) a) atTop (𝓝 (stepClass (τ 0) T a)) := by
  have hu : Tendsto (fun n => stepClass (τ n) T (constant (τ n) 1)) atTop (𝓝 (0 : JointL2)) := by
    have hc : Tendsto (fun _ : ℕ => (valueClass T : JointL2)) atTop
        (𝓝 (valueClass T : JointL2)) := tendsto_const_nhds
    simpa only [unit_stepClass, sub_self] using
      (hc.sub (valueClass_tendsto τ hτ T hT hlim))
  have hb (n : ℕ) : ‖stepClass (τ 0) (τ n) a - stepClass (τ 0) T a‖ ≤
      a.bound * ‖stepClass (τ n) T (constant (τ n) 1)‖ := by
    have he := split_stepClass (hτ (Nat.zero_le n)) T a
    have hd : stepClass (τ 0) (τ n) a - stepClass (τ 0) T a =
        -stepClass (τ n) T (later (hτ (Nat.zero_le n)) a) := by
      rw [← he]; abel
    rw [hd, norm_neg]
    exact step_norm_bound _ _ _ a.bound a.bounded
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) hb
    (by simpa using tendsto_const_nhds.mul hu.norm)

/-- A cofinal countable refinement of one retained actual stochastic step has
the ORIGINAL terminal integral, with convergence in strong scalar L2. -/
theorem integral_retained_endpoint (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (T : ℝ≥0)
    (hT : ∀ n, τ n ≤ T) (hlim : Tendsto τ atTop (𝓝 T)) (a : Coefficient (τ 0)) :
    IBMIntrinsicMartingaleSeries.integral τ (constantAlong τ hτ a) = stepClass (τ 0) T a := by
  have hb (i : ℕ) : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      ‖(constantAlong τ hτ a i).function ω‖ ≤ |a.bound| :=
    a.bounded.mono fun ω h => h.trans (le_abs_self _)
  have ht := sumClass_tendsto τ hτ (constantAlong τ hτ a)
    (bounded_energy_summable τ hτ T hT _ |a.bound| (abs_nonneg _) hb)
  have hs : Tendsto (sumClass τ (constantAlong τ hτ a)) atTop (𝓝 (stepClass (τ 0) T a)) := by
    have he : sumClass τ (constantAlong τ hτ a) = (fun n => stepClass (τ 0) (τ n) a) :=
      funext (refined_sumClass τ hτ a)
    rw [he]
    exact retained_step_tendsto τ hτ T hT hlim a
  exact tendsto_nhds_unique ht hs

theorem integral_retained_actual (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (T : ℝ≥0)
    (hT : ∀ n, τ n ≤ T) (hlim : Tendsto τ atTop (𝓝 T)) (a : Coefficient (τ 0)) :
    IBMIntrinsicMartingaleSeries.integral τ (constantAlong τ hτ a)
      =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => a.function ω * (value T ω - value (τ 0) ω)) := by
  rw [integral_retained_endpoint τ hτ T hT hlim a]
  exact stepClass_ae (τ 0) T a

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicMartingaleEndpoint
